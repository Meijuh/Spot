// Copyright (C) 2010 Laboratoire de Recherche et Developpement
// de l Epita (LRDE).
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

#ifndef SPOT_TA_TA_HH
# define SPOT_TA_TA_HH

#include <set>

#include <cassert>
#include "misc/bddlt.hh"
#include "tgba/state.hh"
#include "tgba/succiter.hh"
#include "tgba/bdddict.hh"

namespace spot
{
  // Forward declarations.  See below.
  class ta_succ_iterator;

  /// ta representation of a Testing Automata
  class ta
  {

  public:
    virtual
    ~ta()
    {
    }

    typedef std::set<state*, state_ptr_less_than> states_set_t;

    virtual const states_set_t*
    get_initial_states_set() const  = 0;

    virtual ta_succ_iterator*
    succ_iter(const spot::state* s) const  = 0;

    virtual bdd_dict*
    get_dict() const  = 0;

    virtual std::string
    format_state(const spot::state* s) const  = 0;

    virtual bool
    is_accepting_state(const spot::state* s) const  = 0;

    virtual bool
    is_livelock_accepting_state(const spot::state* s) const  = 0;

    virtual bool
    is_initial_state(const spot::state* s) const  = 0;

    virtual bdd
    get_state_condition(const spot::state* s) const  = 0;

  };

  /// Successor iterators used by spot::ta.
  class ta_succ_iterator : public tgba_succ_iterator
  {
  public:
    virtual
    ~ta_succ_iterator()
    {
    }

    virtual void
    first() = 0;
    virtual void
    next() = 0;
    virtual bool
    done() const = 0;

    virtual state*
    current_state() const = 0;
    virtual bdd
    current_condition() const = 0;


    bdd
    current_acceptance_conditions() const
    {
      assert(!done());
      return bddfalse;
    }
  };

  // A stack of Strongly-Connected Components
  class sscc_stack
  {
  public:
    struct connected_component
    {
    public:
      connected_component(int index = -1);

      /// Index of the SCC.
      int index;

      bool is_accepting;

      bool is_initial;

      std::list<state*> rem;
    };

    /// Stack a new SCC with index \a index.
    void
    push(int index);

    /// Access the top SCC.
    connected_component&
    top();

    /// Access the top SCC.
    const connected_component&
    top() const;

    /// Pop the top SCC.
    void
    pop();

    /// How many SCC are in stack.
    size_t
    size() const;

    /// The \c rem member of the top SCC.
    std::list<state*>&
    rem();

    /// Is the stack empty?
    bool
    empty() const;

    typedef std::list<connected_component> stack_type;
    stack_type s;
  };

}

#endif // SPOT_TA_TA_HH
