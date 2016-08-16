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

#include <argp.h>
#include <memory>

#include <spot/parseaut/public.hh>

#include <spot/twaalgos/stats.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/gtec/gtec.hh>
#include <spot/twaalgos/word.hh>
#include <spot/twaalgos/isdet.hh>
#include "common_file.hh"


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
        declare('D', &haut_deterministic_);
        declare('E', &haut_edges_);
        declare('G', &haut_gen_acc_);
        declare('H', &input_aut_);
        declare('M', &haut_name_);
        declare('N', &haut_nondetstates_);
        declare('P', &haut_complete_);
        declare('S', &haut_states_);
        declare('T', &haut_trans_);
        declare('W', &haut_word_);
      }
    declare('<', &csv_prefix_);
    declare('>', &csv_suffix_);
    declare('F', &filename_);
    declare('L', &location_);
    if (input != ltl_input)
      declare('f', &filename_);        // Override the formula printer.
    declare('h', &output_aut_);
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
  print(const spot::const_parsed_aut_ptr& haut,
        const spot::const_twa_graph_ptr& aut,
        spot::formula f,
        const char* filename, int loc, double run_time,
        const char* csv_prefix, const char* csv_suffix)
  {
    filename_ = filename ? filename : "";
    csv_prefix_ = csv_prefix ? csv_prefix : "";
    csv_suffix_ = csv_suffix ? csv_suffix : "";
    if (loc >= 0 && has('L'))
      {
        std::ostringstream os;
        os << loc;
        location_ = os.str();
      }
    output_aut_ = aut;
    if (haut)
      {
        input_aut_ = haut->aut;
        if (loc < 0 && has('L'))
          {
            std::ostringstream os;
            os << haut->loc;
            location_ = os.str();
          }

        if (has('T'))
          {
            spot::twa_sub_statistics s = sub_stats_reachable(haut->aut);
            haut_states_ = s.states;
            haut_edges_ = s.edges;
            haut_trans_ = s.transitions;
          }
        else if (has('E'))
          {
            spot::twa_sub_statistics s = sub_stats_reachable(haut->aut);
            haut_states_ = s.states;
            haut_edges_ = s.edges;
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

        if (has('N'))
          {
            haut_nondetstates_ = count_nondet_states(haut->aut);
            haut_deterministic_ = (haut_nondetstates_ == 0);
          }
        else if (has('D'))
          {
            // This is more efficient than calling count_nondet_state().
            haut_deterministic_ = is_deterministic(haut->aut);
          }

        if (has('p'))
          haut_complete_ = is_complete(haut->aut);

        if (has('G'))
          {
            std::ostringstream os;
            os << haut->aut->get_acceptance();
            haut_gen_acc_ = os.str();
          }
        if (has('W'))
          {
            if (auto word = haut->aut->accepting_word())
              {
                std::ostringstream out;
                out << *word;
                haut_word_ = out.str();
              }
            else
              {
                haut_word_.val().clear();
              }
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
          if (auto word = aut->accepting_word())
            {
              std::ostringstream out;
              out << *word;
              aut_word_ = out.str();
            }
          else
            {
              aut_word_.val().clear();
            }
        }

    auto& res = this->spot::stat_printer::print(aut, f, run_time);
    // Make sure we do not store the automaton until the next one is
    // printed, as the registered APs will affect how the next
    // automata are built.
    output_aut_ = nullptr;
    input_aut_ = nullptr;
    return res;
  }

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
  spot::printable_value<unsigned> haut_scc_;
  spot::printable_value<unsigned> haut_deterministic_;
  spot::printable_value<unsigned> haut_nondetstates_;
  spot::printable_value<unsigned> haut_complete_;
  spot::printable_value<const char*> csv_prefix_;
  spot::printable_value<const char*> csv_suffix_;
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
        spot::formula f = nullptr,
        // Input location for errors and statistics.
        const char* filename = nullptr,
        int loc = -1,
        // Time and input automaton for statistics
        double time = 0.0,
        const spot::const_parsed_aut_ptr& haut = nullptr,
        const char* csv_prefix = nullptr,
        const char* csv_suffix = nullptr);

  void add_stat(char c, const spot::printable* p);
};

void setup_default_output_format();
