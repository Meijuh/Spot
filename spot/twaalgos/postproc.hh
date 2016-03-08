// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014, 2015 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#pragma once

#include <spot/twa/twagraph.hh>

namespace spot
{
  class option_map;

  /// \addtogroup twa_reduction
  /// @{

  /// \brief Wrap TGBA/BA/Monitor post-processing algorithms in an
  /// easy interface.
  ///
  /// This class is a shell around scc_filter(),
  /// minimize_obligation(), simulation(), iterated_simulations(),
  /// degeneralize(), to_generalized_buchi() and tgba_determinize().
  /// These different algorithms will be combined depending on the
  /// various options set with set_type(), set_pref(), and
  /// set_level().
  ///
  /// This helps hiding some of the logic required to combine these
  /// simplifications efficiently (e.g., there is no point calling
  /// degeneralize() or any simulation when minimize_obligation()
  /// succeeded.)
  ///
  /// Use set_type() to select desired output type.
  ///
  /// Use the set_pref() method to specify whether you favor
  /// deterministic automata or small automata.  If you don't care,
  /// less post processing will be done.
  ///
  /// The set_level() method lets you set the optimization level.
  /// A higher level enables more costly post-processings.  For instance
  /// pref=Small,level=High will try two different post-processings
  /// (one with minimize_obligation(), and one with
  /// iterated_simulations()) an keep the smallest result.
  /// pref=Small,level=Medium will only try the iterated_simulations()
  /// when minimized_obligation failed to produce an automaton smaller
  /// than its input.  pref=Small,level=Low will only run
  /// simulation().
  ///
  ///
  class SPOT_API postprocessor
  {
  public:
    /// \brief Construct a postprocessor.
    ///
    /// The \a opt argument can be used to pass extra fine-tuning
    /// options used for debugging or benchmarking.
    postprocessor(const option_map* opt = nullptr);

    enum output_type { TGBA, BA, Monitor, Generic };

    /// \brief Select the desired output type.
    ///
    /// \c TGBA requires transition-based generalized Büchi acceptance
    /// while \c BA requests state-based Büchi acceptance.  In both
    /// cases, automata with more complex acceptance conditions will
    /// be converted into these simpler acceptance.  \c Monitor
    /// requests an automaton with the "all paths are accepting
    /// condition": this is less expressive, and may output automata
    /// that recognize a larger language than the input.  Finally \c
    /// Generic remove all constraints about the acceptance condition.
    /// Using \c Generic can be needed to force the determinization of
    /// some automata (e.g., not all TGBA can be degeneralized, using
    /// \c Generic will allow parity acceptance to be used instead).
    ///
    /// If set_type() is not called, the default \c output_type is \c TGBA.
    void
    set_type(output_type type)
    {
      type_ = type;
    }

    enum
    {
      Any = 0,
      Small = 1,                // Small and Deterministic
      Deterministic = 2,        // are exclusive choices.
      Complete = 4,
      SBAcc = 8,                // State-based acceptance.
      Unambiguous = 16,
    };
    typedef int output_pref;

    /// \brief Select the desired characteristics of the output automaton.
    ///
    /// Use \c Any if you do not care about any feature of the output
    /// automaton: less processing will be done.
    ///
    /// \c Small and \c Deterministic are exclusive choices and indicate
    /// whether a smaller non-deterministic automaton should be preferred
    /// over a deterministic automaton.  These are preferences.  The \c Small
    /// option does not guarantee that the resulting automaton will be minimal.
    /// The \c Deterministic option may not manage to produce a deterministic
    /// automaton if the target acceptance set with set_type() is TGBA or BA
    /// (and even if such automaton exists).
    ///
    /// Use
    /// \code
    /// set_type(postprocessor::Generic);
    /// set_pref(postprocessor::Deterministic);
    /// \endcode
    /// if you absolutely want a deterministic automaton.
    ///
    /// The above options can be combined with \c Complete and \c
    /// SBAcc, to request a complete automaton, and an automaton with
    /// state-based acceptance.
    ///
    /// Note: the postprocessor::Unambiguous option is not actually
    /// supported by spot::postprocessor; it is only honored by
    /// spot::translator.
    ///
    /// If set_pref() is not called, the default \c output_type is \c Small.
    void
    set_pref(output_pref pref)
    {
      pref_ = pref;
    }

    enum optimization_level { Low, Medium, High };
    /// \brief Set the optimization level
    ///
    /// At \c Low level, very few simplifications are performed on the
    /// automaton.  Use this level if you need a result that matches
    /// the other constraints, but want it fast.
    ///
    /// At \c High level, several simplifications are chained, but
    /// also the result of different algorithms may be compared to
    /// pick the best result.  This might be slow.
    ///
    /// At \c Medium level, several simplifications are chained, but
    /// only one such "pipeline" is used.
    ///
    /// If set_level() is not called, the default \c output_type is \c High.
    void
    set_level(optimization_level level)
    {
      level_ = level;
    }

    /// \brief Optimize an automaton.
    ///
    /// The returned automaton might be a new automaton,
    /// or an in-place modification of the \a input automaton.
    twa_graph_ptr run(twa_graph_ptr input, formula f = nullptr);

  protected:
    twa_graph_ptr do_simul(const twa_graph_ptr& input, int opt);
    twa_graph_ptr do_sba_simul(const twa_graph_ptr& input, int opt);
    twa_graph_ptr do_degen(const twa_graph_ptr& input);
    twa_graph_ptr do_scc_filter(const twa_graph_ptr& a, bool arg);
    twa_graph_ptr do_scc_filter(const twa_graph_ptr& a);

    output_type type_ = TGBA;
    int pref_ = Small;
    optimization_level level_ = High;
    // Fine-tuning options fetched from the option_map.
    bool degen_reset_ = true;
    bool degen_order_ = false;
    int degen_cache_ = true;
    bool degen_lskip_ = true;
    bool degen_lowinit_ = false;
    bool det_scc_ = true;
    bool det_simul_ = true;
    bool det_stutter_ = true;
    int simul_ = -1;
    int scc_filter_ = -1;
    int ba_simul_ = -1;
    bool tba_determinisation_ = false;
    int sat_minimize_ = 0;
    int sat_acc_ = 0;
    int sat_states_ = 0;
    bool state_based_ = false;
    bool wdba_minimize_ = true;
  };
  /// @}
}
