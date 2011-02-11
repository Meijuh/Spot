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

#ifndef SPOT_TA_TAPRODUCT_HH
# define SPOT_TA_TAPRODUCT_HH

#include "ta.hh"
#include "kripke/kripke.hh"

namespace spot
{

  /// \brief A state for spot::ta_product.
  ///
  /// This state is in fact a pair of state: the state from the ta
  /// automaton and that of Kripke structure.
  class state_ta_product : public state
  {
  public:
    /// \brief Constructor
    /// \param ta_state The state from the ta automaton.
    /// \param kripke_state_ The state from Kripke structure.

    state_ta_product(state* ta_state, state* kripke_state) :
      ta_state_(ta_state), kripke_state_(kripke_state)
    {
    }

    /// Copy constructor
    state_ta_product(const state_ta_product& o);

    virtual
    ~state_ta_product();

    state*
    get_ta_state() const
    {
      return ta_state_;
    }

    state*
    get_kripke_state() const
    {
      return kripke_state_;
    }

    virtual int
    compare(const state* other) const;
    virtual size_t
    hash() const;
    virtual state_ta_product*
    clone() const;

  private:
    state* ta_state_; ///< State from the ta automaton.
    state* kripke_state_; ///< State from the kripke structure.
  };

  /// \brief Iterate over the successors of a product computed on the fly.
  class ta_succ_iterator_product : public ta_succ_iterator
  {
  public:
    ta_succ_iterator_product(const state_ta_product* s, const ta* t, const kripke* k);

    virtual
    ~ta_succ_iterator_product();

    // iteration
    void
    first();
    void
    next();
    bool
    done() const;

    // inspection
    state_ta_product*
    current_state() const;
    bdd
    current_condition() const;

    bool
    is_stuttering_transition() const;

  private:
    //@{
    /// Internal routines to advance to the next successor.
    void
    step_();
    void
    next_non_stuttering_();
    //@}

  protected:
    const state_ta_product* source_;
    const ta* ta_;
    const kripke* kripke_;
    ta_succ_iterator* ta_succ_it_;
    tgba_succ_iterator* kripke_succ_it_;
    state_ta_product* current_state_;
    bdd current_condition_;
    bool is_stuttering_transition_;

  };

  /// \brief A lazy product.  (States are computed on the fly.)
  class ta_product : public ta
  {
  public:
    ta_product(const ta* testing_automata, const kripke* kripke_structure);

    virtual
    ~ta_product();

    virtual const states_set_t
    get_initial_states_set() const;

    virtual ta_succ_iterator_product*
    succ_iter(const spot::state* s) const;

    virtual ta_succ_iterator_product*
    succ_iter(const spot::state* s, bdd condition) const {

      if(condition == bddtrue) return succ_iter(s);
      //TODO
      return 0;
    }

    virtual bdd_dict*
    get_dict() const;

    virtual std::string
    format_state(const spot::state* s) const;

    virtual bool
    is_accepting_state(const spot::state* s) const;

    virtual bool
    is_livelock_accepting_state(const spot::state* s) const;

    virtual bool
    is_initial_state(const spot::state* s) const;

    virtual bdd
    get_state_condition(const spot::state* s) const;

    virtual void
    free_state(const spot::state* s) const;

  private:
    bdd_dict* dict_;
    const ta* ta_;
    const kripke* kripke_;

    // Disallow copy.
    ta_product(const ta_product&);
    ta_product&
    operator=(const ta_product&);
  };

}

#endif // SPOT_TA_TAPRODUCT_HH
