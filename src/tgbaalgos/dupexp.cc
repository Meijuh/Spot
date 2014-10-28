// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2011, 2012, 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include "dupexp.hh"
#include "tgba/tgbagraph.hh"
#include <sstream>
#include <string>
#include <map>
#include "reachiter.hh"
#include "dotty.hh"

namespace spot
{
  namespace
  {
    template <class T>
    class dupexp_iter: public T
    {
    public:
      dupexp_iter(const const_tgba_ptr& a)
	: T(a), out_(make_tgba_digraph(a->get_dict()))
      {
	out_->copy_acceptance_conditions_of(a);
	out_->copy_ap_of(a);
      }

      tgba_digraph_ptr
      result()
      {
	return out_;
      }

      virtual void
      process_state(const state*, int n, tgba_succ_iterator*)
      {
	unsigned ns = out_->new_state();
	assert(ns == static_cast<unsigned>(n) - 1);
	(void)ns;
      }

      virtual void
      process_link(const state*, int in,
		   const state*, int out,
		   const tgba_succ_iterator* si)
      {
	out_->new_transition
	  (in - 1, out - 1, si->current_condition(),
	   si->current_acceptance_conditions());
      }

    protected:
      tgba_digraph_ptr out_;
    };

    template <typename T>
    class dupexp_iter_save: public dupexp_iter<T>
    {
    public:
      dupexp_iter_save(const const_tgba_ptr& a,
		       std::vector<const state*>& relation)
        : dupexp_iter<T>(a), relation_(relation)
      {
      }

      virtual void
      end()
      {
	relation_.resize(this->seen.size());
	for (auto s: this->seen)
	  relation_[s.second - 1] = const_cast<state*>(s.first);
      }

      std::vector<const state*>& relation_;
    };

  } // anonymous

  tgba_digraph_ptr
  tgba_dupexp_bfs(const const_tgba_ptr& aut)
  {
    dupexp_iter<tgba_reachable_iterator_breadth_first> di(aut);
    di.run();
    return di.result();
  }

  tgba_digraph_ptr
  tgba_dupexp_dfs(const const_tgba_ptr& aut)
  {
    dupexp_iter<tgba_reachable_iterator_depth_first> di(aut);
    di.run();
    return di.result();
  }

  tgba_digraph_ptr
  tgba_dupexp_bfs(const const_tgba_ptr& aut, std::vector<const state*>& rel)
  {
    dupexp_iter_save<tgba_reachable_iterator_breadth_first> di(aut, rel);
    di.run();
    return di.result();
  }

  tgba_digraph_ptr
  tgba_dupexp_dfs(const const_tgba_ptr& aut, std::vector<const state*>& rel)
  {
    auto aa = std::dynamic_pointer_cast<const spot::tgba_digraph>(aut);
    if (aa)
      {
	aa->get_init_state_number(); // Create an initial state if needed.
	auto res = make_tgba_digraph(aa);
	unsigned ns = aa->num_states();
	rel.reserve(ns);
	// The state numbers are common to both automata, but
	// the state pointers are to the older one.
	for (unsigned n = 0; n < ns; ++n)
	  rel.push_back(aa->state_from_number(n));
	return res;
      }

    dupexp_iter_save<tgba_reachable_iterator_depth_first> di(aut, rel);
    di.run();
    return di.result();
  }
}
