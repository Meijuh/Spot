// -*- coding: utf-8 -*-
// Copyright (C) 2012 Laboratoire de Recherche et Développement de
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

#ifndef SPOT_TGBAALGOS_POSTPROC_HH
# define SPOT_TGBAALGOS_POSTPROC_HH

#include "tgba/tgba.hh"

namespace spot
{
  /// \addtogroup tgba_reduction
  /// @{

  /// \brief Wrap TGBA/BA post-processing algorithms in an easy interface.
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
  /// The set_level() method let you set the optimization level.
  /// Higher level enable more costly postprocessign.  For instance
  /// pref=Small,level=High will try two different postprocessings
  /// (one with minimize_obligation(), and one with
  /// iterated_simulations()) an keep the smallest result.
  /// pref=Small,level=Medium will only try the iterated_simulations()
  /// when minimized_obligation failed to produce an automaton smaller
  /// than its input.  pref=Small,level=Low will only run
  /// simulation().
  class postprocessor
  {
  public:
    postprocessor()
      : type_(TGBA), pref_(Small), level_(High)
    {
    }

    enum output_type { TGBA, BA };
    void
    set_type(output_type type)
    {
      type_ = type;
    }

    enum output_pref { Any, Small, Deterministic };
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

    /// Return the optimized automaton and delete \a input.
    const tgba* run(const tgba* input, const ltl::formula* f);

  private:
    output_type type_;
    output_pref pref_;
    optimization_level level_;
  };
  /// @}
}

#endif // SPOT_TGBAALGOS_POSTPROC_HH