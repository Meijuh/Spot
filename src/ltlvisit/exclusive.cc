// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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

#include "exclusive.hh"
#include "ltlenv/defaultenv.hh"
#include "ltlast/multop.hh"
#include "ltlast/unop.hh"
#include "ltlast/constant.hh"
#include "twaalgos/mask.hh"
#include "misc/casts.hh"
#include "misc/minato.hh"
#include "apcollect.hh"

namespace spot
{
  exclusive_ap::~exclusive_ap()
  {
    for (auto& g: groups)
      for (auto ap: g)
	ap->destroy();
  }

  namespace
  {
    static const std::vector<const spot::ltl::atomic_prop*>
    split_aps(const char* arg)
    {
      auto& env = spot::ltl::default_environment::instance();
      std::vector<const spot::ltl::atomic_prop*> group;
      auto start = arg;
      while (*start)
	{
	  while (*start == ' ' || *start == '\t')
	    ++start;
	  if (!*start)
	    break;
	  if (*start == ',')
	    {
	      std::string s = "unexpected ',' in ";
	      s += arg;
	      throw std::invalid_argument(s);
	    }
	  if (*start == '"')
	    {
	      ++start;
	      auto end = start;
	      while (*end && *end != '"')
		{
		  if (*end == '\\')
		    ++end;
		  ++end;
		}
	      if (!*end)
		{
		  std::string s = "missing closing '\"' in ";
		  s += arg;
		  throw std::invalid_argument(s);
		}
	      std::string ap(start, end - start);
	      auto* t = env.require(ap);
	      group.push_back(down_cast<const spot::ltl::atomic_prop*>(t));
	      do
		++end;
	      while (*end == ' ' || *end == '\t');
	      if (*end && *end != ',')
		{
		  std::string s = "unexpected character '";
		  s += *end;
		  s += "' in ";
		  s += arg;
		  throw std::invalid_argument(s);
		}
	      if (*end == ',')
		++end;
	      start = end;
	    }
	  else
	    {
	      auto end = start;
	      while (*end && *end != ',')
		++end;
	      auto rend = end;
	      while (rend > start && (rend[-1] == ' ' || rend[-1] == '\t'))
		--rend;
	      std::string ap(start, rend - start);
	      auto* t = env.require(ap);
	      group.push_back(down_cast<const spot::ltl::atomic_prop*>(t));
	      if (*end == ',')
		start = end + 1;
	      else
		break;
	    }
	}
      return group;
    }
  }

  void exclusive_ap::add_group(const char* ap_csv)
  {
    add_group(split_aps(ap_csv));
  }

  void exclusive_ap::add_group(std::vector<const ltl::atomic_prop*> ap)
  {
    groups.push_back(ap);
  }

  namespace
  {
    const ltl::formula*
    nand(const ltl::formula* lhs, const ltl::formula* rhs)
    {
      auto f = ltl::multop::instance(ltl::multop::And,
				     lhs->clone(), rhs->clone());
      return ltl::unop::instance(ltl::unop::Not, f);
    }
  }

  const ltl::formula*
  exclusive_ap::constrain(const ltl::formula* f) const
  {
    spot::ltl::atomic_prop_set* s = atomic_prop_collect(f);

    std::vector<const ltl::atomic_prop*> group;
    ltl::multop::vec* v = new ltl::multop::vec;

    for (auto& g: groups)
      {
	group.clear();

	for (auto ap: g)
	  if (s->find(ap) != s->end())
	    group.push_back(ap);

	unsigned s = group.size();
	for (unsigned j = 0; j < s; ++j)
	  for (unsigned k = j + 1; k < s; ++k)
	    v->push_back(nand(group[j], group[k]));
      };

    delete s;

    auto* c = ltl::unop::instance(ltl::unop::G,
				  ltl::multop::instance(ltl::multop::And, v));
    return ltl::multop::instance(ltl::multop::And, f->clone(), c);
  }

  twa_graph_ptr exclusive_ap::constrain(const_twa_graph_ptr aut,
					   bool simplify_guards) const
  {
    // Compute the support of the automaton.
    bdd support = bddtrue;
    {
      std::set<int> bdd_seen;
      for (auto& t: aut->edges())
	if (bdd_seen.insert(t.cond.id()).second)
	  support &= bdd_support(t.cond);
    }

    bdd restrict = bddtrue;
    auto d = aut->get_dict();

    std::vector<bdd> group;
    for (auto& g: groups)
      {
	group.clear();

	for (auto ap: g)
	  {
	    int v = d->has_registered_proposition(ap, aut);
	    if (v >= 0)
	      group.push_back(bdd_nithvar(v));
	  }

	unsigned s = group.size();
	for (unsigned j = 0; j < s; ++j)
	  for (unsigned k = j + 1; k < s; ++k)
	    restrict &= group[j] | group[k];
      }

    twa_graph_ptr res = make_twa_graph(aut->get_dict());
    res->copy_ap_of(aut);
    res->prop_copy(aut, { true, true, true, true });
    res->copy_acceptance_of(aut);
    if (simplify_guards)
      {
	transform_accessible(aut, res, [&](unsigned, bdd& cond,
					   acc_cond::mark_t&, unsigned)
			     {
			       minato_isop isop(cond & restrict,
						cond | !restrict,
						true);
			       bdd res = bddfalse;
			       bdd cube = bddfalse;
			       while ((cube = isop.next()) != bddfalse)
				 res |= cube;
			       cond = res;
			     });
      }
    else
      {
	transform_accessible(aut, res, [&](unsigned, bdd& cond,
					   acc_cond::mark_t&, unsigned)
			     {
			       cond &= restrict;
			     });
      }
    return res;
  }
}
