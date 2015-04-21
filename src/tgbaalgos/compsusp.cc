// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "compsusp.hh"
#include "sccfilter.hh"
#include "sccinfo.hh"
#include "twa/twagraph.hh"
#include "ltl2tgba_fm.hh"
#include "minimize.hh"
#include "simulation.hh"
#include "safety.hh"
#include "ltlast/allnodes.hh"
#include "ltlvisit/tostring.hh"
#include "ltlvisit/clone.hh"
#include <queue>
#include <sstream>
#include "ltlenv/environment.hh"

namespace spot
{
  namespace
  {
    typedef std::map<const ltl::formula*, bdd> formula_bdd_map;

    // An environment to store atomic proposition associated to
    // suspended variable.  (We don't use the default environment to
    // avoid conflicts with user-defined atomic propositions that
    // would share the same name.)
    class suspended_environment: public ltl::environment
    {
    public:
      const ltl::formula*
      require(const std::string& s)
      {
	return ltl::atomic_prop::instance(s, *this);
      }

      const std::string&
      name() const
      {
	static std::string name("suspended environment");
	return name;
      }
    };
    static suspended_environment suspenv;

    // Rewrite the suspendable subformulae "s" of an LTL formula in
    // the form Gg where "g" is an atomic proposition representing
    // "s".  At the same time, populate maps that associate "s" to "g"
    // and vice-versa.
    class ltl_suspender_visitor: public ltl::clone_visitor
    {
    public:
      typedef std::map<const ltl::formula*, const ltl::formula*> fmap_t;
      ltl_suspender_visitor(fmap_t& g2s, fmap_t& a2o, bool oblig)
	: g2s_(g2s), a2o_(a2o), oblig_(oblig)
      {
      }

      void
      visit(const ltl::multop* mo)
      {
	ltl::multop::type op = mo->op();
	switch (op)
	  {
	  case ltl::multop::Or:
	  case ltl::multop::And:
	    {
	      ltl::multop::vec* res = new ltl::multop::vec;
	      ltl::multop::vec* oblig = oblig_ ? new ltl::multop::vec : 0;
	      ltl::multop::vec* susp = new ltl::multop::vec;
	      unsigned mos = mo->size();
	      for (unsigned i = 0; i < mos; ++i)
		{
		  const ltl::formula* c = mo->nth(i);
		  if (c->is_boolean())
		    res->push_back(c->clone());
		  else if (oblig_ && c->is_syntactic_obligation())
		    oblig->push_back(c->clone());
		  else if (c->is_eventual() && c->is_universal())
		    susp->push_back(c->clone());
		  else
		    res->push_back(recurse(c));
		}
	      if (!oblig_ || oblig->empty())
		{
		  delete oblig;
		}
	      else
		{
		  const ltl::formula* o = ltl::multop::instance(op, oblig);
		  res->push_back(recurse(o));
		  o->destroy();
		}
	      if (susp->empty())
		{
		  delete susp;
		}
	      else
		{
		  const ltl::formula* o = ltl::multop::instance(op, susp);
		  // Rewrite 'o' as 'G"o"'
		  const ltl::formula* g = recurse(o);
		  o->destroy();
		  if (op == ltl::multop::And)
		    {
		      res->push_back(g);
		    }
		  else
		    {
		      // res || susp -> (res && G![susp]) || G[susp])
		      const ltl::formula* r = ltl::multop::instance(op, res);
		      const ltl::unop* u =
			down_cast<const ltl::unop*>(g);
		      const ltl::formula* gn =
			ltl::unop::instance
			(ltl::unop::G, ltl::unop::instance
			 (ltl::unop::Not, u->child()->clone()));
		      result_ = ltl::multop::instance
			(ltl::multop::Or, ltl::multop::instance
			 (ltl::multop::And, r, gn),
			 g);
		      return;
		    }
		}
	      result_ = ltl::multop::instance(op, res);
	    }
	    break;
	  case ltl::multop::OrRat:
	  case ltl::multop::AndRat:
	  case ltl::multop::AndNLM:
	  case ltl::multop::Concat:
	  case ltl::multop::Fusion:
	    this->ltl::clone_visitor::visit(mo);
	    break;
	  }
      }


      const ltl::formula*
      recurse(const ltl::formula* f)
      {
	const ltl::formula* res;
	if (f->is_boolean())
	  return f->clone();
	if (oblig_ && f->is_syntactic_obligation())
	  {
	    fmap_t::const_iterator i = assoc_.find(f);
	    if (i != assoc_.end())
	      return i->second->clone();

	    std::ostringstream s;
	    s << "〈";
	    to_string(f, s);
	    s << "〉";
	    res = suspenv.require(s.str());
	    // We have to clone f, because it is not always a sub-tree
	    // of the original formula.  (Think n-ary operators.)
	    a2o_[res] = f->clone();
	    assoc_[f] = res;
	    return res;
	  }
	if (f->is_eventual() && f->is_universal())
	  {
	    fmap_t::const_iterator i = assoc_.find(f);
	    if (i != assoc_.end())
	      return ltl::unop::instance(ltl::unop::G, i->second->clone());

	    std::ostringstream s;
	    s << '[';
	    to_string(f, s);
	    s << ']';
	    res = suspenv.require(s.str());
	    // We have to clone f, because it is not always a sub-tree
	    // of the original formula.  (Think n-ary operators.)
	    g2s_[res] = f->clone();
	    assoc_[f] = res;
	    return ltl::unop::instance(ltl::unop::G, res);
	  }
	f->accept(*this);
	return result_;
      }

    private:
      fmap_t& g2s_;
      fmap_t assoc_;		// This one is only needed by the visitor.
      fmap_t& a2o_;
      bool oblig_;
    };


    typedef std::pair<const state*, const state*> state_pair;

    typedef std::map<state_pair, unsigned> pair_map;
    typedef std::deque<state_pair> pair_queue;

    static
    twa_graph_ptr
    susp_prod(const const_twa_ptr& left, const ltl::formula* f, bdd v)
    {
      bdd_dict_ptr dict = left->get_dict();
      auto right =
	iterated_simulations(scc_filter(ltl_to_tgba_fm(f, dict, true, true),
					false));

      twa_graph_ptr res = make_twa_graph(dict);
      dict->register_all_variables_of(left, res);
      dict->register_all_variables_of(right, res);
      dict->unregister_variable(bdd_var(v), res);

      const acc_cond& la = left->acc();
      const acc_cond& ra = right->acc();
      res->set_generalized_buchi(la.num_sets() + ra.num_sets());

      acc_cond::mark_t radd = ra.all_sets();

      pair_map seen;
      pair_queue todo;

      state_pair p(left->get_init_state(), 0);
      state* ris = right->get_init_state();
      p.second = ris;
      unsigned i = res->new_state();
      seen[p] = i;
      todo.push_back(p);
      res->set_init_state(i);

      while (!todo.empty())
	{
	  p = todo.front();
	  todo.pop_front();
	  const state* ls = p.first;
	  const state* rs = p.second;
	  int src = seen[p];

	  for (auto li: left->succ(ls))
	    {
	      state_pair d(li->current_state(), ris);
	      bdd lc = li->current_condition();

	      twa_succ_iterator* ri = 0;
	      // Should we reset the right automaton?
	      if ((lc & v) == lc)
		{
		  // No.
		  ri = right->succ_iter(rs);
		  ri->first();
		}
	      // Yes.  Reset the right automaton.
	      else
		{
		  p.second = ris;
		}

	      // This loops over all the right transitions
	      // if RI is defined.  Otherwise this just makes
	      // one iteration as if the right automaton was
	      // looping in state 0 with "true".
	      while (!ri || !ri->done())
		{
		  bdd cond = lc;
		  acc_cond::mark_t racc = radd;
		  if (ri)
		    {
		      cond = lc & ri->current_condition();
		      // Skip incompatible transitions.
		      if (cond == bddfalse)
			{
			  ri->next();
			  continue;
			}
		      d.second = ri->current_state();
		      racc = ri->current_acceptance_conditions();
		    }

		  int dest;
		  pair_map::const_iterator i = seen.find(d);
		  if (i != seen.end()) // Is this an existing state?
		    {
		      dest = i->second;
		    }
		  else
		    {
		      dest = res->new_state();
		      seen[d] = dest;
		      todo.push_back(d);
		    }

		  acc_cond::mark_t a =
		    res->acc().join(la, li->current_acceptance_conditions(),
				    ra, racc);
		  res->new_transition(src, dest, bdd_exist(cond, v), a);

		  if (ri)
		    ri->next();
		  else
		    break;
		}
	      if (ri)
		right->release_iter(ri);
	    }
	}
      return res;
    }
  }


  twa_graph_ptr
  compsusp(const ltl::formula* f, const bdd_dict_ptr& dict,
	   bool no_wdba, bool no_simulation,
	   bool early_susp, bool no_susp_product, bool wdba_smaller,
	   bool oblig)
  {
    ltl_suspender_visitor::fmap_t g2s;
    ltl_suspender_visitor::fmap_t a2o;
    ltl_suspender_visitor v(g2s, a2o, oblig);
    const ltl::formula* g = v.recurse(f);

    // Translate the patched formula, and remove useless SCCs.
    twa_graph_ptr res =
      scc_filter(ltl_to_tgba_fm(g, dict, true, true, false, false, 0, 0),
		 false);

    if (!no_wdba)
      {
	twa_graph_ptr min = minimize_obligation(res, g, 0, wdba_smaller);
	if (min != res)
	  {
	    res = min;
	    no_simulation = true;
	  }
      }

    if (!no_simulation)
      res = iterated_simulations(res);

    // Create a map of suspended formulae to BDD variables.
    spot::formula_bdd_map susp;
    for (auto& it: g2s)
      {
	auto j = dict->var_map.find(it.first);
	// If no BDD variable of this suspended formula exist in the
	// BDD dict, it means the suspended subformulae was never
	// actually used in the automaton.  Just skip it.  FIXME: It
	// would be better if we had a way to check that the variable
	// is used in this automaton, and not in some automaton
	// (sharing the same dictionary.)
	if (j != dict->var_map.end())
	  susp[it.second] = bdd_ithvar(j->second);
      }

    // Remove suspendable formulae from non-accepting SCCs.
    bdd suspvars = bddtrue;
    for (formula_bdd_map::const_iterator i = susp.begin();
	 i != susp.end(); ++i)
      suspvars &= i->second;

    bdd allaccap = bddtrue; // set of atomic prop used in accepting SCCs.
    {
      scc_info si(res);

      // Restrict suspvars to the set of suspension labels that occur
      // in accepting SCC.
      unsigned sn = si.scc_count();
      for (unsigned n = 0; n < sn; n++)
	if (si.is_accepting_scc(n))
	  allaccap &= si.scc_ap_support(n);

      bdd ignored = bdd_exist(suspvars, allaccap);
      suspvars = bdd_existcomp(suspvars, allaccap);
      res = scc_filter_susp(res, false, suspvars, ignored, early_susp, &si);
    }

    // Do we need to synchronize any suspended formula?
    if (!susp.empty() && !no_susp_product)
      for (formula_bdd_map::const_iterator i = susp.begin();
	   i != susp.end(); ++i)
	if ((allaccap & i->second) == allaccap)
	  res = susp_prod(res, i->first, i->second);

    g->destroy();

    for (ltl_suspender_visitor::fmap_t::iterator i = g2s.begin();
	 i != g2s.end(); ++i)
      i->second->destroy();
    for (ltl_suspender_visitor::fmap_t::iterator i = a2o.begin();
	 i != a2o.end(); ++i)
      i->second->destroy();
    return res;
  }
}
