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

#include "copy.hh"
#include "twa/twagraph.hh"
#include <sstream>
#include <string>
#include <map>
#include "reachiter.hh"
#include "dot.hh"

namespace spot
{
  namespace
  {
    class copy_iter: public tgba_reachable_iterator_depth_first
    {
    public:
      copy_iter(const const_twa_ptr& a, twa::prop_set p,
		bool preserve_names)
	: tgba_reachable_iterator_depth_first(a),
	  out_(make_twa_graph(a->get_dict()))
      {
	out_->copy_acceptance_of(a);
	out_->copy_ap_of(a);
	out_->prop_copy(a, p);
	if (preserve_names)
	  {
	    names_ = new std::vector<std::string>;
	    out_->set_named_prop("state-names", names_);
	  }
      }

      twa_graph_ptr
      result()
      {
	return out_;
      }

      virtual void
      process_state(const state* s, int n, twa_succ_iterator*)
      {
	unsigned ns = out_->new_state();
	if (names_)
	  names_->emplace_back(aut_->format_state(s));
	assert(ns == static_cast<unsigned>(n) - 1);
	(void)ns;
	(void)n;
      }

      virtual void
      process_link(const state*, int in,
		   const state*, int out,
		   const twa_succ_iterator* si)
      {
	out_->new_edge
	  (in - 1, out - 1, si->cond(),
	   si->acc());
      }

    protected:
      twa_graph_ptr out_;
      std::vector<std::string>* names_ = nullptr;
    };

  } // anonymous

  twa_graph_ptr
  copy(const const_twa_ptr& aut, twa::prop_set p, bool preserve_names)
  {
    copy_iter di(aut, p, preserve_names);
    di.run();
    return di.result();
  }
}
