// -*- coding: utf-8 -*-
// Copyright (C) 2016 Laboratoire de Recherche et Développement
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

#include <spot/twaalgos/parity.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/product.hh>
#include <vector>
#include <utility>
#include <functional>
#include <queue>
#include <spot/twaalgos/hoa.hh>

namespace spot
{
  namespace
  {
    unsigned change_set(unsigned x, unsigned num_sets,
                        bool change_kind, bool change_style)
    {
      // If the parity acceptance kind is changed,
      // then the index of the sets are reversed
      if (change_kind)
        x = num_sets - x - 1;
      // If the parity style is changed, then all the existing acceptance
      // sets are shifted
      x += change_style;
      return x;
    }

    void
    change_acc(twa_graph_ptr& aut, unsigned num_sets, bool change_kind,
               bool change_style, bool output_max, bool input_max)
    {
      for (auto& e: aut->edge_vector())
        if (e.acc)
          {
            unsigned msb = (input_max ? e.acc.max_set() : e.acc.min_set()) - 1;
            e.acc = acc_cond::mark_t{change_set(msb, num_sets, change_kind,
                                                change_style)};
          }
        else if (output_max && change_style)
          {
            // If the parity is changed, a new set is introduced.
            // This new set is used to mark all the transitions of the input
            // that don't belong to any acceptance sets.
            e.acc.set(0);
          }
    }
  }

  twa_graph_ptr
  change_parity(const const_twa_graph_ptr& aut,
                parity_kind kind, parity_style style)
  {
    return change_parity_here(make_twa_graph(aut, twa::prop_set::all()),
                              kind, style);
  }

  twa_graph_ptr
  change_parity_here(twa_graph_ptr aut, parity_kind kind, parity_style style)
  {
    bool current_max;
    bool current_odd;
    if (!aut->acc().is_parity(current_max, current_odd, true))
      throw new std::invalid_argument("change_parity: input must have a parity "
                                      "acceptance.");
    auto old_num_sets = aut->num_sets();

    bool output_max = true;
    switch (kind)
      {
        case parity_kind_max:
          output_max = true;
          break;
        case parity_kind_min:
          output_max = false;
          break;
        case parity_kind_same:
          output_max = current_max;
          break;
        case parity_kind_any:
          // If we need to change the style we may change the kind not to
          // introduce new accset.
          output_max = (((style == parity_style_odd && !current_odd)
                         || (style == parity_style_even && current_odd))
                        && old_num_sets % 2 == 0) != current_max;
          break;
      }

    bool change_kind = current_max != output_max;
    bool toggle_style = change_kind && (old_num_sets % 2 == 0);

    bool output_odd = true;
    switch (style)
      {
        case parity_style_odd:
          output_odd = true;
          break;
        case parity_style_even:
          output_odd = false;
          break;
        case parity_style_same:
          output_odd = current_odd;
          break;
        case parity_style_any:
          output_odd = current_odd != toggle_style;
          // If we need to change the kind we may change the style not to
          // introduce new accset.
          break;
      }

    current_odd = current_odd != toggle_style;
    bool change_style = false;
    auto num_sets = old_num_sets;
    // If the parity neeeds to be changed, then a new acceptance set is created.
    // The old acceptance sets are shifted
    if (output_odd != current_odd)
      {
        change_style = true;
        ++num_sets;
      }

    if (change_kind || change_style)
      {
        auto new_acc = acc_cond::acc_code::parity(output_max,
                                                  output_odd, num_sets);
        aut->set_acceptance(num_sets, new_acc);
      }
    change_acc(aut, old_num_sets, change_kind,
               change_style, output_max, current_max);
    return aut;
  }
}
