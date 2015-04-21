// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2011, 2012, 2014, 2015 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
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
      dupexp_iter(const const_tgba_ptr& a, twa::prop_set p)
	: T(a), out_(make_twa_graph(a->get_dict()))
      {
	out_->copy_acceptance_of(a);
	out_->copy_ap_of(a);
	out_->prop_copy(a, p);
      }

      twa_graph_ptr
      result()
      {
	return out_;
      }

      virtual void
      process_state(const state*, int n, twa_succ_iterator*)
      {
	unsigned ns = out_->new_state();
	assert(ns == static_cast<unsigned>(n) - 1);
	(void)ns;
	(void)n;
      }

      virtual void
      process_link(const state*, int in,
		   const state*, int out,
		   const twa_succ_iterator* si)
      {
	out_->new_transition
	  (in - 1, out - 1, si->current_condition(),
	   si->current_acceptance_conditions());
      }

    protected:
      twa_graph_ptr out_;
    };

  } // anonymous

  twa_graph_ptr
  tgba_dupexp_bfs(const const_tgba_ptr& aut, twa::prop_set p)
  {
    dupexp_iter<tgba_reachable_iterator_breadth_first> di(aut, p);
    di.run();
    return di.result();
  }

  twa_graph_ptr
  tgba_dupexp_dfs(const const_tgba_ptr& aut, twa::prop_set p)
  {
    dupexp_iter<tgba_reachable_iterator_depth_first> di(aut, p);
    di.run();
    return di.result();
  }
}
