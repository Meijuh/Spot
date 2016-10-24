// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015, 2016 Laboratoire de Recherche et
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

#include "common_sys.hh"
#include "common_file.hh"

#include <argp.h>
#include <memory>
#include <spot/misc/timer.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/gtec/gtec.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/stats.hh>
#include <spot/twaalgos/word.hh>


// Format for automaton output
enum automaton_format_t {
  Dot,
  Lbtt,
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


struct printable_automaton final:
  public spot::printable_value<spot::const_twa_graph_ptr>
{
  using spot::printable_value<spot::const_twa_graph_ptr>::operator=;
  void print(std::ostream& os, const char* pos) const override;
};


struct process_timer
{
  void start()
  {
    sw.start();
    dt.start();
  }

  void stop()
  {
    // sw.stop() --> It always returns the duration since the last call to
    // start(). Therefore, it wont't stop timing, moreover, it can be called
    // multiple times.
    sw_lap_ = sw.stop();
    dt.stop();
  }
  double get_lap_sw()
  {
    return sw_lap_;
  }

  spot::timer dt;
  spot::stopwatch sw;
  double sw_lap_ = 0;
};

struct printable_timer final:
  public spot::printable_value<spot::timer>
{
  using spot::printable_value<spot::timer>::operator=;
  void print(std::ostream& os, const char* pos) const override;
};

/// \brief prints various statistics about a TGBA
///
/// This object can be configured to display various statistics
/// about a TGBA.  Some %-sequence of characters are interpreted in
/// the format string, and replaced by the corresponding statistics.
class hoa_stat_printer: protected spot::stat_printer
{
public:
  hoa_stat_printer(std::ostream& os, const char* format,
      stat_style input = no_input);

  using spot::formater::declare;
  using spot::formater::set_output;

  /// \brief print the configured statistics.
  ///
  /// The \a f argument is not needed if the Formula does not need
  /// to be output.
  std::ostream&
    print(const spot::const_parsed_aut_ptr& haut,
        const spot::const_twa_graph_ptr& aut,
        spot::formula f,
        const char* filename, int loc, process_timer& ptimer,
        const char* csv_prefix, const char* csv_suffix);

private:
  spot::printable_value<const char*> filename_;
  spot::printable_value<std::string> location_;
  spot::printable_value<std::string> haut_name_;
  spot::printable_value<std::string> aut_name_;
  spot::printable_value<std::string> aut_word_;
  spot::printable_value<std::string> haut_word_;
  spot::printable_value<std::string> haut_gen_acc_;
  spot::printable_value<unsigned> haut_states_;
  spot::printable_value<unsigned> haut_edges_;
  spot::printable_value<unsigned> haut_trans_;
  spot::printable_value<unsigned> haut_acc_;
  spot::printable_scc_info haut_scc_;
  spot::printable_value<unsigned> haut_deterministic_;
  spot::printable_value<unsigned> haut_nondetstates_;
  spot::printable_value<unsigned> haut_complete_;
  spot::printable_value<const char*> csv_prefix_;
  spot::printable_value<const char*> csv_suffix_;
  printable_timer timer_;
  printable_automaton input_aut_;
  printable_automaton output_aut_;
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
  ~automaton_printer();

  void
  print(const spot::twa_graph_ptr& aut,
        process_timer& ptimer,
        spot::formula f = nullptr,
        // Input location for errors and statistics.
        const char* filename = nullptr,
        int loc = -1,
        // Time and input automaton for statistics
        const spot::const_parsed_aut_ptr& haut = nullptr,
        const char* csv_prefix = nullptr,
        const char* csv_suffix = nullptr);

  void add_stat(char c, const spot::printable* p);
};

void setup_default_output_format();
