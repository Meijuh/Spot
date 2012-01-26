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

#ifndef SPOT_TGBAALGOS_SBA2TA_HH
# define SPOT_TGBAALGOS_SBA2TA_HH

#include "misc/hash.hh"
#include <list>
#include <map>
#include <set>
#include "tgba/tgbatba.hh"
#include "ltlast/formula.hh"
#include <cassert>
#include "misc/bddlt.hh"
#include "ta/taexplicit.hh"
#include "ta/tgbtaexplicit.hh"

namespace spot
{
  /// \brief Build a spot::tgba_explicit* from an LTL formula.
  /// \ingroup tgba_ta
  ///
  /// This is based on the following paper.
  /// \verbatim
  ///  @InProceedings{        geldenhuys.06.spin,
  ///  author        = {Jaco Geldenhuys and Henri Hansen},
  ///  title         = {Larger Automata and Less Work for {LTL} Model Checking},
  ///  booktitle     = {Proceedings of the 13th International SPIN Workshop
  ///                  (SPIN'06)},
  ///  year          = {2006},
  ///  pages         = {53--70},
  ///  series        = {Lecture Notes in Computer Science},
  ///  volume        = {3925},
  ///  publisher     = {Springer}
  /// }
  /// \endverbatim
  ///
  /// \param tgba_to_convert The TGBA automaton to convert into a TA automaton
  ///
  /// \param atomic_propositions_set The set of atomic propositions used in the
  /// input TGBA \a tgba_to_convert
  ///
  /// \param artificial_initial_state_mode When set, the algorithm will build
  /// a TA automaton with an unique initial state.  This
  /// artificial initial state have one transition to each real initial state,
  /// and this transition is labeled by the corresponding initial condition.
  /// (see spot::ta::get_artificial_initial_state())
  ///
  /// \param STA_mode When set, the returned TA
  /// automaton is a STA (Single-pass Testing Automata): a STA automaton is a TA
  /// where: for every livelock-accepting state s, if s is not also a
  /// Buchi-accepting state, then s has no successors. A STA product requires
  /// only one-pass emptiness check algorithm (see spot::ta_check::check)
  ///
  /// \param degeneralized When false, the returned automaton is a generalized
  /// form of TA, called TGTA (Transition-based Generalized Testing Automaton).
  /// Like TGBA, TGTA use Generalized Büchi acceptance
  /// conditions intead of Büchi-accepting states: there are several acceptance
  /// sets (of transitions), and a path is accepted if it traverses
  /// at least one transition of each set infinitely often or if it contains a
  /// livelock-accepting cycle.
  ///
  /// \return A spot::ta_explicit that recognizes the same language as the
  /// TGBA \a tgba_to_convert.
  ta_explicit*
  tgba_to_ta(const tgba* tgba_to_convert, bdd atomic_propositions_set,
      bool artificial_initial_state_mode = true, bool STA_mode = false,
      bool degeneralized = true);

  stgta_explicit*
  tgba_to_stgta(const tgba* tgba_to_convert, bdd atomic_propositions_set);


  //artificial_livelock_accepting_state is used in the case of
    //STA (Single-pass Testing Automata) or in the case
    //STGTA (Single-pass Transition-based Generalised Testing Automata)
    void
    compute_livelock_acceptance_states(ta_explicit* testing_automata,
        state_ta_explicit* artificial_livelock_accepting_state = 0);

    //artificial_livelock_accepting_state is added to transform TA into
    //STA (Single-pass Testing Automata) or to transform TGTA into
    //STGTA (Single-pass Transition-based Generalised Testing Automata)
    void
    add_artificial_livelock_accepting_state(ta_explicit* testing_automata,
        state_ta_explicit* artificial_livelock_accepting_state);

}

#endif // SPOT_TGBAALGOS_SBA2TA_HH
