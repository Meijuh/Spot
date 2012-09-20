// Copyright (C) 2012 Laboratoire de Recherche et Developpement de
// l'Epita (LRDE).
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

#ifndef SPOT_TGBAALGOS_CYCLES_HH
# define SPOT_TGBAALGOS_CYCLES_HH

#include "scc.hh"
#include "misc/hash.hh"
#include <deque>
#include <utility>

namespace spot
{

  /// \brief Enumerate cycles from a SCC.
  ///
  /// This implements the algorithm on page 170 of:
  ///
  /// \verbatim
  /// @Article{loizou.82.is,
  ///   author =  {George Loizou and Peter Thanisch},
  ///   title =   {Enumerating the Cycles of a Digraph: A New
  ///              Preprocessing Strategy},
  ///   journal = {Information Sciences},
  ///   year = 	  {1982},
  ///   volume =  {27},
  ///   number =  {3},
  ///   pages =   {163--182},
  ///   month =   aug
  /// }
  /// \endverbatim
  ///
  /// (the additional preprocessing described in that paper is not
  /// implemented).
  ///
  /// The class constructor takes an automaton, and an scc_map that
  /// should already have been built for for automaton.  Calling
  /// run(n) will enumerate all elementary cycles in SCC #n.  Each
  /// time an SCC is found, the method cycle_found() is called with
  /// the initial state of the cycle (the cycle is constituted from
  /// all the states that are on the dfs stack after this starting
  /// state).  When if cycle_found() returns false, the run() method
  /// will terminate.  If it returns true, the run() method will
  /// search the next elementary cycle.
  class enumerate_cycles
  {
  protected:
    typedef Sgi::hash_set<const state*,
			  state_ptr_hash, state_ptr_equal> set_type;

    struct state_info
    {
      // Whether the state has already left the stack at least once.
      bool reach;
      // set to true when the state current state w is stacked, and
      // reset either when the state is unstacked after having
      // contributed to a cycle, or when some state z that (1) w could
      // reach (even indirectly) without discovering a cycle, and (2)
      // that a contributed to a contributed to a cycle.
      bool mark;
      // Deleted successors (in the paper, states deleted from A(x))
      set_type del;

      // Predecessors of the current states, that could not yet
      // contribute to a cycle.
      set_type b;
    };

    typedef Sgi::hash_map<const state*, state_info,
			  state_ptr_hash, state_ptr_equal> hash_type;

    typedef hash_type::iterator tagged_state;

  public:
    enumerate_cycles(const tgba* aut, const scc_map& map);

    // Run in SCC scc, and call cycle_found() for any new elementary
    // cycle found.
    void run(unsigned scc);

    void nocycle(tagged_state x, tagged_state y);
    void unmark(tagged_state y);

    // Called whenever a cycle was found.  The cycles uses all the
    // states from the dfs stack, starting from \a start.
    virtual bool cycle_found(const state* start);

    tagged_state tag_state(const state* s);
    void push_state(tagged_state ts);

  protected:
    const tgba* aut_;
    const scc_map& sm_;

    struct dfs_entry
    {
      tagged_state ts;
      tgba_succ_iterator* succ;
      bool f;
    };
    typedef std::deque<dfs_entry> dfs_stack;
    dfs_stack dfs;

    hash_type tags;
  };

}

#endif // SPOT_TGBAALGOS_CYCLES_HH
