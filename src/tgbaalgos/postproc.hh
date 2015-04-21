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

#include "tgba/tgbagraph.hh"

namespace spot
{
  class option_map;

  /// \addtogroup twa_reduction
  /// @{

  /// \brief Wrap TGBA/BA/Monitor post-processing algorithms in an
  /// easy interface.
  ///
  /// This class is a shell around scc_filter(),
  /// minimize_obligation(), simulation(), iterated_simulations(), and
  /// degeneralize().  These different algorithms will be combined
  /// depending on the various options set with set_type(),
  /// set_pref(), and set_level().
  ///
  /// This helps hiding some of the logic required to combine these
  /// simplifications efficiently (e.g., there is no point calling
  /// degeneralize() or any simulation when minimize_obligation()
  /// succeeded.)
  ///
  /// Use set_pref() method to specify whether you favor
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
  class SPOT_API postprocessor
  {
  public:
    /// \brief Construct a postprocessor.
    ///
    /// The \a opt argument can be used to pass extra fine-tuning
    /// options used for debugging or benchmarking.
    postprocessor(const option_map* opt = 0);

    enum output_type { TGBA, BA, Monitor, Generic };
    void
    set_type(output_type type)
    {
      type_ = type;
    }

    enum
    {
      Any = 0,
      Small = 1,
      Deterministic = 2,
      // 3 reserved for unambiguous
      // Combine Complete as 'Small | Complete' or 'Deterministic | Complete'
      Complete = 4
    };
    typedef int output_pref;

    void
    set_pref(output_pref pref)
    {
      pref_ = pref;
    }

    enum optimization_level { Low, Medium, High };
    void
    set_level(optimization_level level)
    {
      level_ = level;
    }

    /// \brief Optimize an automaton.
    ///
    /// The returned automaton might be a new automaton,
    /// or an in-place modification of the \a input automaton.
    twa_graph_ptr run(twa_graph_ptr input,
			 const ltl::formula* f);

  protected:
    twa_graph_ptr do_simul(const twa_graph_ptr& input, int opt);
    twa_graph_ptr do_ba_simul(const twa_graph_ptr& input, int opt);
    twa_graph_ptr do_degen(const twa_graph_ptr& input);

    output_type type_;
    int pref_;
    optimization_level level_;
    // Fine-tuning options fetched from the option_map.
    bool degen_reset_;
    bool degen_order_;
    int degen_cache_;
    bool degen_lskip_;
    bool degen_lowinit_;
    int simul_;
    int scc_filter_;
    int ba_simul_;
    bool tba_determinisation_;
    int sat_minimize_;
    int sat_acc_;
    int sat_states_;
    bool state_based_;
    bool wdba_minimize_;
  };
  /// @}
}
