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
#include <sstream>
#include <string>
#include <map>
#include "reachiter.hh"

namespace spot
{
  namespace
  {
    template <class T>
    class dupexp_iter: public T
    {
    public:
      dupexp_iter(const tgba* a)
	: T(a), out_(new tgba_digraph(a->get_dict()))
      {
	out_->copy_acceptance_conditions_of(a);
	a->get_dict()->register_all_variables_of(a, out_);
      }

      tgba_digraph*
      result()
      {
	return out_;
      }

      virtual void
      process_state(const state*, int n, tgba_succ_iterator*)
      {
	unsigned ns = out_->get_graph().new_state();
	assert(ns == static_cast<unsigned>(n) - 1);
	(void)ns;
      }

      virtual void
      process_link(const state*, int in,
		   const state*, int out,
		   const tgba_succ_iterator* si)
      {
	out_->get_graph().new_transition(in - 1, out - 1,
					 si->current_condition(),
					 si->current_acceptance_conditions());
      }

    protected:
      tgba_digraph* out_;
    };

    template <typename T>
    class dupexp_iter_save: public dupexp_iter<T>
    {
    public:
      dupexp_iter_save(const tgba* a,
                       std::map<const state*,
                                const state*,
                                state_ptr_less_than>& relation)
        : dupexp_iter<T>(a), relation_(relation)
      {
      }

      virtual void
      end()
      {
	for (auto s: this->seen)
	  relation_[this->out_->state_from_number(s.second - 1)]
	    = const_cast<state*>(s.first);
      }

      std::map<const state*, const state*, state_ptr_less_than>& relation_;
    };

  } // anonymous

  tgba_digraph*
  tgba_dupexp_bfs(const tgba* aut)
  {
    dupexp_iter<tgba_reachable_iterator_breadth_first> di(aut);
    di.run();
    return di.result();
  }

  tgba_digraph*
  tgba_dupexp_dfs(const tgba* aut)
  {
    dupexp_iter<tgba_reachable_iterator_depth_first> di(aut);
    di.run();
    return di.result();
  }

  tgba_digraph*
  tgba_dupexp_bfs(const tgba* aut,
                  std::map<const state*,
                           const state*, state_ptr_less_than>& rel)
  {
    dupexp_iter_save<tgba_reachable_iterator_breadth_first> di(aut,
                                                               rel);
    di.run();
    return di.result();
  }

  tgba_digraph*
  tgba_dupexp_dfs(const tgba* aut,
                  std::map<const state*,
                           const state*, state_ptr_less_than>& rel)
  {
    dupexp_iter_save<tgba_reachable_iterator_depth_first> di(aut,
                                                             rel);
    di.run();
    return di.result();
  }
}
