// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
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

#include "stutter.hh"
#include "tgba/tgba.hh"
#include "dupexp.hh"
#include "misc/hash.hh"
#include "misc/hashfunc.hh"
#include "ltlvisit/apcollect.hh"
#include "translate.hh"
#include "ltlast/unop.hh"
#include "ltlvisit/remove_x.hh"
#include "tgbaalgos/product.hh"
#include "tgba/tgbaproduct.hh"
#include "tgba/bddprint.hh"
#include <deque>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace spot
{
  namespace
  {
    class state_tgbasl: public state
    {
    public:
      state_tgbasl(state* s, bdd cond) : s_(s), cond_(cond)
      {
      }

      virtual
      ~state_tgbasl()
      {
        s_->destroy();
      }

      virtual int
      compare(const state* other) const
      {
        const state_tgbasl* o =
          down_cast<const state_tgbasl*>(other);
        assert(o);
        int res = s_->compare(o->real_state());
        if (res != 0)
          return res;
        return cond_.id() - o->cond_.id();
      }

      virtual size_t
      hash() const
      {
        return wang32_hash(s_->hash()) ^ wang32_hash(cond_.id());
      }

      virtual
      state_tgbasl* clone() const
      {
        return new state_tgbasl(*this);
      }

      state*
      real_state() const
      {
        return s_;
      }

      bdd
      cond() const
      {
        return cond_;
      }

    private:
      state* s_;
      bdd cond_;
    };

    class tgbasl_succ_iterator : public tgba_succ_iterator
    {
    public:
      tgbasl_succ_iterator(tgba_succ_iterator* it, const state_tgbasl* state,
			   bdd_dict_ptr d, bdd atomic_propositions)
        : it_(it), state_(state), aps_(atomic_propositions), d_(d)
      {
      }

      virtual
      ~tgbasl_succ_iterator()
      {
        delete it_;
      }

      // iteration

      bool
      first()
      {
        loop_ = false;
        done_ = false;
        need_loop_ = true;
        if (it_->first())
          {
            cond_ = it_->current_condition();
            next_edge();
          }
        return true;
      }

      bool
      next()
      {
        if (cond_ != bddfalse)
          {
            next_edge();
            return true;
          }
        if (!it_->next())
          {
            if (loop_ || !need_loop_)
              done_ = true;
            loop_ = true;
            return !done_;
          }
        else
          {
            cond_ = it_->current_condition();
            next_edge();
            return true;
          }
      }

      bool
      done() const
      {
        return it_->done() && done_;
      }

      // inspection

      state_tgbasl*
      current_state() const
      {
        if (loop_)
          return new state_tgbasl(state_->real_state(), state_->cond());
        return new state_tgbasl(it_->current_state(), one_);
      }

      bdd
      current_condition() const
      {
        if (loop_)
          return state_->cond();
        return one_;
      }

      acc_cond::mark_t
      current_acceptance_conditions() const
      {
        if (loop_)
          return 0U;
        return it_->current_acceptance_conditions();
      }

    private:
      void
      next_edge()
      {
        one_ = bdd_satoneset(cond_, aps_, bddtrue);
        cond_ -= one_;
        if (need_loop_ && (state_->cond() == one_)
            && (state_ == it_->current_state()))
          need_loop_ = false;
      }

      tgba_succ_iterator* it_;
      const state_tgbasl* state_;
      bdd cond_;
      bdd one_;
      bdd aps_;
      bdd_dict_ptr d_;
      bool loop_;
      bool need_loop_;
      bool done_;
    };


    class tgbasl final : public tgba
    {
    public:
      tgbasl(const const_tgba_ptr& a, bdd atomic_propositions)
	: tgba(a->get_dict()), a_(a), aps_(atomic_propositions)
      {
	get_dict()->register_all_propositions_of(&a_, this);
	assert(acc_.num_sets() == 0);
	acc_.add_sets(a_->acc().num_sets());
      }

      virtual ~tgbasl()
      {
	get_dict()->unregister_all_my_variables(this);
      }

      virtual state* get_init_state() const override
      {
	return new state_tgbasl(a_->get_init_state(), bddfalse);
      }

      virtual tgba_succ_iterator* succ_iter(const state* state) const override
      {
	const state_tgbasl* s = down_cast<const state_tgbasl*>(state);
	assert(s);
	return new tgbasl_succ_iterator(a_->succ_iter(s->real_state()), s,
					a_->get_dict(), aps_);
      }

      virtual std::string format_state(const state* state) const override
      {
	const state_tgbasl* s = down_cast<const state_tgbasl*>(state);
	assert(s);
	return (a_->format_state(s->real_state())
		+ ", "
		+ bdd_format_formula(a_->get_dict(), s->cond()));
      }

    protected:
      virtual bdd compute_support_conditions(const state*) const override
      {
	return bddtrue;
      }

    private:
      const_tgba_ptr a_;
      bdd aps_;
    };

    typedef std::shared_ptr<tgbasl> tgbasl_ptr;

    inline tgbasl_ptr make_tgbasl(const const_tgba_ptr& aut, bdd ap)
    {
      return std::make_shared<tgbasl>(aut, ap);
    }



    typedef std::pair<unsigned, bdd> stutter_state;

    struct stutter_state_hash
    {
      size_t
      operator()(const stutter_state& s) const
      {
	return wang32_hash(s.first) ^ wang32_hash(s.second.id());
      }
    };

    // Associate the stutter state to its number.
    typedef std::unordered_map<stutter_state, unsigned,
			       stutter_state_hash> ss2num_map;

    // Queue of state to be processed.
    typedef std::deque<stutter_state> queue_t;

    static bdd
    get_all_ap(const const_tgba_digraph_ptr& a)
    {
      bdd res = bddtrue;
      for (auto& i: a->transitions())
	res &= bdd_support(i.cond);
      return res;
    }

  }

  tgba_digraph_ptr
  sl(const const_tgba_digraph_ptr& a, const ltl::formula* f)
  {
    bdd aps = f
      ? atomic_prop_collect_as_bdd(f, a)
      : get_all_ap(a);
    return sl(a, aps);
  }

  tgba_digraph_ptr
  sl2(const const_tgba_digraph_ptr& a, const ltl::formula* f)
  {
    bdd aps = f
      ? atomic_prop_collect_as_bdd(f, a)
      : get_all_ap(a);
    return sl2(a, aps);
  }

  tgba_digraph_ptr
  sl(const const_tgba_digraph_ptr& a, bdd atomic_propositions)
  {
    // The result automaton uses numbered states.
    tgba_digraph_ptr res = make_tgba_digraph(a->get_dict());
    // We use the same BDD variables as the input.
    res->copy_ap_of(a);
    res->copy_acceptance_conditions_of(a);
    // These maps make it possible to convert stutter_state to number
    // and vice-versa.
    ss2num_map ss2num;

    queue_t todo;

    unsigned s0 = a->get_init_state_number();
    stutter_state s(s0, bddfalse);
    ss2num[s] = 0;
    res->new_state();
    todo.push_back(s);

    while (!todo.empty())
      {
	s = todo.front();
	todo.pop_front();
	unsigned src = ss2num[s];

	bool self_loop_needed = true;

	for (auto& t : a->out(s.first))
	  {
	    bdd all = t.cond;
	    while (all != bddfalse)
	      {
		bdd one = bdd_satoneset(all, atomic_propositions, bddtrue);
		all -= one;

		stutter_state d(t.dst, one);

		auto r = ss2num.emplace(d, ss2num.size());
		unsigned dest = r.first->second;

		if (r.second)
		  {
		    todo.push_back(d);
		    unsigned u = res->new_state();
		    assert(u == dest);
		    (void)u;
		  }

		// Create the transition.
		res->new_transition(src, dest, one, t.acc);

		if (src == dest)
		  self_loop_needed = false;
	      }
	  }

	if (self_loop_needed && s.second != bddfalse)
	  res->new_transition(src, src, s.second, 0U);
      }
    res->merge_transitions();
    return res;
  }

  tgba_digraph_ptr
  sl2(tgba_digraph_ptr&& a, bdd atomic_propositions)
  {
    if (atomic_propositions == bddfalse)
      atomic_propositions = get_all_ap(a);
    unsigned num_states = a->num_states();
    unsigned num_transitions = a->num_transitions();
    for (unsigned src = 0; src < num_states; ++src)
      {
	auto trans = a->out(src);

	for (auto it = trans.begin(); it != trans.end()
             && it.trans() <= num_transitions; ++it)
	  if (it->dst != src)
	    {
	      bdd all = it->cond;
	      while (all != bddfalse)
		{
		  unsigned dst = it->dst;
		  bdd one = bdd_satoneset(all, atomic_propositions, bddtrue);
		  unsigned tmp = a->new_state();
		  unsigned i = a->new_transition(src, tmp, one, it->acc);
		  assert(i > num_transitions);
		  i = a->new_transition(tmp, tmp, one, 0U);
		  assert(i > num_transitions);
		  // No acceptance here to preserve the state-based property.
		  i = a->new_transition(tmp, dst, one, 0U);
		  assert(i > num_transitions);
		  all -= one;
		}
	    }
      }
    if (num_states != a->num_states())
      a->prop_keep({true,	// state_based
	            true,	// single_acc
	            false,	// inherently_weak
	            false,	// deterministic
	           });
    a->merge_transitions();
    return a;
  }

  tgba_digraph_ptr
  sl2(const const_tgba_digraph_ptr& a, bdd atomic_propositions)
  {
    return sl2(make_tgba_digraph(a, tgba::prop_set::all()),
	       atomic_propositions);
  }


  tgba_digraph_ptr
  closure(tgba_digraph_ptr&& a)
  {
    a->prop_keep({false,	// state_based
	          true,		// single_acc
	          false,	// inherently_weak
	          false,	// deterministic
	         });

    unsigned n = a->num_states();
    std::vector<unsigned> todo;
    std::vector<std::vector<unsigned> > dst2trans(n);

    for (unsigned state = 0; state < n; ++state)
      {
	auto trans = a->out(state);

	for (auto it = trans.begin(); it != trans.end(); ++it)
	  {
	    todo.push_back(it.trans());
	    dst2trans[it->dst].push_back(it.trans());
	  }

	while (!todo.empty())
	  {
	    auto t1 = a->trans_storage(todo.back());
	    todo.pop_back();

	    for (auto& t2 : a->out(t1.dst))
	      {
		bdd cond = t1.cond & t2.cond;
		if (cond != bddfalse)
		  {
                    bool need_new_trans = true;
		    acc_cond::mark_t acc = t1.acc | t2.acc;
                    for (auto& t: dst2trans[t2.dst])
                      {
                        auto& ts = a->trans_storage(t);
                        if (acc == ts.acc)
                          {
                            if (!bdd_implies(cond, ts.cond))
                              {
                                ts.cond = ts.cond | cond;
                                if (std::find(todo.begin(), todo.end(), t)
                                    == todo.end())
                                  todo.push_back(t);
                              }
                            need_new_trans = false;
                          }
                      }
                    if (need_new_trans)
                      {
			// Load t2.dst first, because t2 can be
			// invalidated by new_transition().
			auto dst = t2.dst;
                        auto i = a->new_transition(state, dst, cond, acc);
                        dst2trans[dst].push_back(i);
                        todo.push_back(i);
                      }
		  }
	      }
	  }
        for (auto& it: dst2trans)
          it.clear();
      }
    return a;
  }

  tgba_digraph_ptr
  closure(const const_tgba_digraph_ptr& a)
  {
    return closure(make_tgba_digraph(a, {true, true, true, true}));
  }

  // The stutter check algorithm to use can be overridden via an
  // environment variable.
  static int default_stutter_check_algorithm()
  {
    static const char* stutter_check = getenv("SPOT_STUTTER_CHECK");
    if (stutter_check)
      {
	char* endptr;
	long res = strtol(stutter_check, &endptr, 10);
	if (*endptr || res < 0 || res > 8)
	  throw
	    std::runtime_error("invalid value for SPOT_STUTTER_CHECK.");
	return res;
      }
    else
      {
	return 8;     // The best variant, according to our benchmarks.
      }
  }

  bool
  is_stutter_invariant(const ltl::formula* f)
  {
    if (f->is_ltl_formula() && f->is_X_free())
      return true;

    int algo = default_stutter_check_algorithm();

    if (algo == 0) // Etessami's check via syntactic transformation.
      {
	if (!f->is_ltl_formula())
	  throw std::runtime_error("Cannot use the syntactic "
				   "stutter-invariance check "
				   "for non-LTL formulas");
	const ltl::formula* g = remove_x(f);
	ltl::ltl_simplifier ls;
	bool res = ls.are_equivalent(f, g);
	g->destroy();
	return res;
      }

    // Prepare for an automata-based check.
    const ltl::formula* nf = ltl::unop::instance(ltl::unop::Not, f->clone());
    translator trans;
    auto aut_f = trans.run(f);
    auto aut_nf = trans.run(nf);
    bdd aps = atomic_prop_collect_as_bdd(f, aut_f);
    nf->destroy();
    return is_stutter_invariant(std::move(aut_f), std::move(aut_nf), aps, algo);
  }

  bool
  is_stutter_invariant(tgba_digraph_ptr&& aut_f,
                       tgba_digraph_ptr&& aut_nf, bdd aps, int algo)
  {
    if (algo == 0)
      algo = default_stutter_check_algorithm();

    switch (algo)
      {
      case 1: // sl(aut_f) x sl(aut_nf)
	return product(sl(std::move(aut_f), aps),
		       sl(std::move(aut_nf), aps))->is_empty();
      case 2: // sl(cl(aut_f)) x aut_nf
	return product(sl(closure(std::move(aut_f)), aps),
		       std::move(aut_nf))->is_empty();
      case 3: // (cl(sl(aut_f)) x aut_nf
	return product(closure(sl(std::move(aut_f), aps)),
		       std::move(aut_nf))->is_empty();
      case 4: // sl2(aut_f) x sl2(aut_nf)
	return product(sl2(std::move(aut_f), aps),
		       sl2(std::move(aut_nf), aps))->is_empty();
      case 5: // sl2(cl(aut_f)) x aut_nf
	return product(sl2(closure(std::move(aut_f)), aps),
		       std::move(aut_nf))->is_empty();
      case 6: // (cl(sl2(aut_f)) x aut_nf
	return product(closure(sl2(std::move(aut_f), aps)),
		       std::move(aut_nf))->is_empty();
      case 7: // on-the-fly sl(aut_f) x sl(aut_nf)
	return otf_product(make_tgbasl(aut_f, aps),
			   make_tgbasl(aut_nf, aps))->is_empty();
      case 8: // cl(aut_f) x cl(aut_nf)
	return product(closure(std::move(aut_f)),
		       closure(std::move(aut_nf)))->is_empty();
      default:
	throw std::runtime_error("invalid algorithm number for "
				 "is_stutter_invariant()");
	SPOT_UNREACHABLE();
      }
  }
}
