// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include "mask.hh"

namespace spot
{
  tgba_digraph_ptr mask_acc_sets(const const_tgba_digraph_ptr& in,
				 acc_cond::mark_t to_remove)
  {
    auto& inacc = in->acc();
    auto res = make_tgba_digraph(in->get_dict());
    res->copy_ap_of(in);
    res->prop_copy(in, { true, false, true, true });
    unsigned na = inacc.num_sets();
    unsigned tr = to_remove.count();
    assert(tr <= na);
    res->set_acceptance_conditions(na - tr);
    transform_mask(in, res, [&](bdd& cond,
				acc_cond::mark_t& acc,
				unsigned)
		   {
		     if (acc & to_remove)
		       cond = bddfalse;
		     else
		       acc = inacc.strip(acc, to_remove);
		   });
    return res;
  }

}
