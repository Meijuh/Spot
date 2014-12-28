// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et Développement
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

#ifndef SPOT_BIN_COMMON_AOUTPUT_HH
#define SPOT_BIN_COMMON_AOUTPUT_HH

#include "common_sys.hh"

#include <argp.h>

#include "hoaparse/public.hh"

#include "tgbaalgos/stats.hh"
#include "tgbaalgos/sccinfo.hh"
#include "tgbaalgos/gtec/gtec.hh"
#include "tgbaalgos/reducerun.hh"
#include "tgbaalgos/word.hh"
#include "tgbaalgos/isdet.hh"


// Format for automaton output
enum automaton_format_t {
  Dot,
  Lbtt,
  Lbtt_t,
  Spin,
  Spot,
  Stats,
  Hoa,
  Quiet,
  Count,
};

// The format to use in output_automaton()
extern automaton_format_t automaton_format;
// Any option to pass to Dot
extern const char* opt_dot;
// Options to pass to the HOA printer
extern const char* hoa_opt;
// How to name the automaton
extern const char* opt_name;

/// \brief prints various statistics about a TGBA
///
/// This object can be configured to display various statistics
/// about a TGBA.  Some %-sequence of characters are interpreted in
/// the format string, and replaced by the corresponding statistics.
class hoa_stat_printer: protected spot::stat_printer
{
public:
  hoa_stat_printer(std::ostream& os, const char* format)
    : spot::stat_printer(os, format)
  {
    declare('A', &haut_acc_);
    declare('C', &haut_scc_);
    declare('E', &haut_edges_);
    declare('F', &filename_);
    declare('f', &filename_);	// Override the formula printer.
    declare('L', &haut_loc_);
    declare('M', &haut_name_);
    declare('m', &aut_name_);
    declare('S', &haut_states_);
    declare('T', &haut_trans_);
    declare('w', &aut_word_);
  }

  /// \brief print the configured statistics.
  ///
  /// The \a f argument is not needed if the Formula does not need
  /// to be output.
  std::ostream&
  print(const spot::const_hoa_aut_ptr& haut,
	const spot::const_tgba_digraph_ptr& aut,
	const char* filename, double run_time)
  {
    filename_ = filename;
    haut_loc_ = haut->loc;

    if (has('T'))
	{
	  spot::tgba_sub_statistics s = sub_stats_reachable(haut->aut);
	  haut_states_ = s.states;
	  haut_edges_ = s.transitions;
	  haut_trans_ = s.sub_transitions;
	}
    else if (has('E'))
	{
	  spot::tgba_sub_statistics s = sub_stats_reachable(haut->aut);
	  haut_states_ = s.states;
	  haut_edges_ = s.transitions;
	}
    if (has('M'))
	{
	  auto n = haut->aut->get_named_prop<std::string>("automaton-name");
	  if (n)
	    haut_name_ = *n;
	  else
	    haut_name_.val().clear();
	}
    if (has('m'))
	{
	  auto n = aut->get_named_prop<std::string>("automaton-name");
	  if (n)
	    aut_name_ = *n;
	  else
	    aut_name_.val().clear();
	}
    if (has('S'))
	{
	  haut_states_ = haut->aut->num_states();
	}

    if (has('A'))
	haut_acc_ = haut->aut->acc().num_sets();

    if (has('C'))
	haut_scc_ = spot::scc_info(haut->aut).scc_count();

    if (has('w'))
	{
	  auto res = spot::couvreur99(aut)->check();
	  if (res)
	    {
	      auto run = res->accepting_run();
	      assert(run);
	      run = reduce_run(aut, run);
	      spot::tgba_word w(run);
	      w.simplify();
	      std::ostringstream out;
	      w.print(out, aut->get_dict());
	      aut_word_ = out.str();
	    }
	  else
	    {
	      aut_word_.val().clear();
	    }
	}

    return this->spot::stat_printer::print(aut, 0, run_time);
  }

private:
  spot::printable_value<const char*> filename_;
  spot::printable_value<std::string> haut_name_;
  spot::printable_value<std::string> aut_name_;
  spot::printable_value<std::string> aut_word_;
  spot::printable_value<unsigned> haut_states_;
  spot::printable_value<unsigned> haut_edges_;
  spot::printable_value<unsigned> haut_trans_;
  spot::printable_value<unsigned> haut_acc_;
  spot::printable_value<unsigned> haut_scc_;
  spot::printable_value<spot::location> haut_loc_;
};


class automaton_printer
{
  hoa_stat_printer statistics;
  std::ostringstream name;
  hoa_stat_printer namer;

public:

  automaton_printer(const char* stats)
    : statistics(std::cout, stats), namer(name, opt_name)
  {
  }

  void
  print(const spot::tgba_digraph_ptr& aut,
	// Input location for errors and statistics.
	const char* filename = nullptr,
	// Time and input automaton for statistics
	double time = 0.0,
	const spot::const_hoa_aut_ptr& haut = nullptr);
};



#endif // SPOT_BIN_COMMON_AOUTPUT_HH
