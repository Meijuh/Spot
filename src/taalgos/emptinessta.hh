// Copyright (C) 2008 Laboratoire de Recherche et Development de
// l'Epita (LRDE).
// Copyright (C) 2003, 2004, 2005, 2006 Laboratoire d'Informatique de
// Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#ifndef SPOT_TAALGOS_EMPTINESS_HH
# define SPOT_TAALGOS_EMPTINESS_HH

#include "ta/ta.hh"
#include "misc/optionmap.hh"
#include "tgbaalgos/gtec/nsheap.hh"
#include "tgbaalgos/emptiness_stats.hh"
#include <stack>

namespace spot
{

  namespace
  {
    typedef std::pair<spot::state*, ta_succ_iterator*> pair_state_iter;
  }
  /// \brief An implementation of the ta emptiness-check algorithm.
  ///
  /// See the documentation for spot::ta.
  class ta_check : public ec_statistics
  {
  public:
    ta_check(const ta* a, option_map o = option_map());
    virtual
    ~ta_check();

    /// Check whether the automaton's language is empty.
    virtual bool
    check();

    virtual bool
    livelock_detection(const ta* t);

    virtual std::ostream&
    print_stats(std::ostream& os) const;

    /// \brief Return the status of the emptiness-check.
    ///
    /// When check() succeed, the status should be passed along
    /// to spot::counter_example.
    ///
    /// This status should not be deleted, it is a pointer
    /// to a member of this class that will be deleted when
    /// the ta object is deleted.
    //  const tgba_check_status* result() const;

  protected:
    void
    clear(numbered_state_heap* h, std::stack<pair_state_iter> todo, std::stack<
        spot::state*> init_set);
    bool
    heuristic_livelock_detection(const state * stuttering_succ,
        numbered_state_heap* h, int h_livelock_root, std::set<const state*,
            state_ptr_less_than> liveset_curr);
    const ta* a_; ///< The automaton.
    option_map o_; ///< The options

    bool is_full_2_pass_;

    // * scc: a stack of strongly connected components (SCC)
    scc_stack_ta scc;

    // * sscc: a stack of strongly stuttering-connected components (SSCC)
    scc_stack_ta sscc;

  };

/// @}
}

#endif // SPOT_TAALGOS_EMPTINESS_HH
