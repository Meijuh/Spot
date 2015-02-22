// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et Développement
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
#include <memory>

#include "hoaparse/public.hh"

#include "tgbaalgos/stats.hh"
#include "tgbaalgos/sccinfo.hh"
#include "tgbaalgos/gtec/gtec.hh"
#include "tgbaalgos/reducerun.hh"
#include "tgbaalgos/word.hh"
#include "tgbaalgos/isdet.hh"
#include "common_file.hh"


// Format for automaton output
enum automaton_format_t {
  Dot,
  Lbtt,
  Lbtt_t,
  Spin,
  Stats,
  Hoa,
  Quiet,
  Count,
};

// The format to use in output_automaton()
extern automaton_format_t automaton_format;
// Set to the argument of --name, else nullptr.
extern const char* opt_name;
// Output options
extern const struct argp aoutput_argp;

// help text for %F and %L
extern char F_doc[32];
extern char L_doc[32];

// FORMAT help text
extern const struct argp aoutput_io_format_argp;
extern const struct argp aoutput_o_format_argp;

// Parse output options
int parse_opt_aoutput(int key, char* arg, struct argp_state* state);


enum stat_style { no_input, aut_input, ltl_input };

/// \brief prints various statistics about a TGBA
///
/// This object can be configured to display various statistics
/// about a TGBA.  Some %-sequence of characters are interpreted in
/// the format string, and replaced by the corresponding statistics.
class hoa_stat_printer: protected spot::stat_printer
{
public:
  hoa_stat_printer(std::ostream& os, const char* format,
		   stat_style input = no_input)
    : spot::stat_printer(os, format)
  {
    if (input == aut_input)
      {
	declare('A', &haut_acc_);
	declare('C', &haut_scc_);
	declare('E', &haut_edges_);
	declare('G', &haut_gen_acc_);
	declare('M', &haut_name_);
	declare('S', &haut_states_);
	declare('T', &haut_trans_);
      }
    declare('F', &filename_);
    declare('L', &location_);
    if (input != ltl_input)
      declare('f', &filename_);	// Override the formula printer.
    declare('m', &aut_name_);
    declare('w', &aut_word_);
  }

  using spot::formater::declare;
  using spot::formater::set_output;

  /// \brief print the configured statistics.
  ///
  /// The \a f argument is not needed if the Formula does not need
  /// to be output.
  std::ostream&
  print(const spot::const_hoa_aut_ptr& haut,
	const spot::const_tgba_digraph_ptr& aut,
	const spot::ltl::formula* f,
	const char* filename, int loc, double run_time)
  {
    filename_ = filename;
    if (loc >= 0 && has('L'))
      {
	std::ostringstream os;
	os << loc;
	location_ = os.str();
      }
    if (haut)
      {
	if (loc < 0 && has('L'))
	  {
	    std::ostringstream os;
	    os << haut->loc;
	    location_ = os.str();
	  }

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
	if (has('S'))
	  haut_states_ = haut->aut->num_states();

	if (has('A'))
	  haut_acc_ = haut->aut->acc().num_sets();

	if (has('C'))
	  haut_scc_ = spot::scc_info(haut->aut).scc_count();

	if (has('G'))
	  {
	    std::ostringstream os;
	    os << haut->aut->get_acceptance();
	    haut_gen_acc_ = os.str();
	  }
      }

    if (has('m'))
	{
	  auto n = aut->get_named_prop<std::string>("automaton-name");
	  if (n)
	    aut_name_ = *n;
	  else
	    aut_name_.val().clear();
	}
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

    return this->spot::stat_printer::print(aut, f, run_time);
  }

private:
  spot::printable_value<const char*> filename_;
  spot::printable_value<std::string> location_;
  spot::printable_value<std::string> haut_name_;
  spot::printable_value<std::string> aut_name_;
  spot::printable_value<std::string> aut_word_;
  spot::printable_value<std::string> haut_gen_acc_;
  spot::printable_value<unsigned> haut_states_;
  spot::printable_value<unsigned> haut_edges_;
  spot::printable_value<unsigned> haut_trans_;
  spot::printable_value<unsigned> haut_acc_;
  spot::printable_value<unsigned> haut_scc_;
};


class automaton_printer
{
  hoa_stat_printer statistics;
  std::ostringstream name;
  hoa_stat_printer namer;
  std::ostringstream outputname;
  hoa_stat_printer outputnamer;
  std::map<std::string, std::unique_ptr<output_file>> outputfiles;

public:

  automaton_printer(stat_style input = no_input);

  void
  print(const spot::tgba_digraph_ptr& aut,
	const spot::ltl::formula* f = nullptr,
	// Input location for errors and statistics.
	const char* filename = nullptr,
	int loc = -1,
	// Time and input automaton for statistics
	double time = 0.0,
	const spot::const_hoa_aut_ptr& haut = nullptr);

  void add_stat(char c, const spot::printable* p);
};



#endif // SPOT_BIN_COMMON_AOUTPUT_HH
