// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015, 2016 Laboratoire de Recherche et
// Développement de l'Epita.
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

#include "config.h"
#include <spot/misc/formater.hh>
#include <cstdlib>
#include <sstream>
#include <stdexcept>
#include <spot/misc/satsolver.hh>
#include <picosat/picosat.h>
#include <fstream>
#include <limits>
#include <sys/wait.h>

namespace spot
{
  satsolver::solution
  satsolver_get_solution(const char* filename)
  {
    satsolver::solution sol;
    std::istream* in;
    if (filename[0] == '-' && filename[1] == 0)
      in = &std::cin;
    else
      in = new std::ifstream(filename);

    int c;
    while ((c = in->get()) != EOF)
      {
        // If a line does not start with 'v ', ignore it.
        if (c != 'v' || in->get() != ' ')
          {
            in->ignore(std::numeric_limits<std::streamsize>::max(), '\n');
            continue;
          }
        // Otherwise, read integers one by one.
        int i;
        while (*in >> i)
          {
            if (i == 0)
              goto done;
            sol.emplace_back(i);
          }
        if (!in->eof())
          // If we haven't reached end-of-file, then we just attempted
          // to extract something that wasn't an integer.  Clear the
          // fail bit so that will loop over.
          in->clear();
      }
  done:
    if (in != &std::cin)
      delete in;
    return sol;
  }

  // In other functions, command_given() won't be called anymore as it is more
  // easy to check if psat_ was initialized or not.
  satsolver::satsolver()
    : cnf_tmp_(nullptr), cnf_stream_(nullptr), nclauses_(0), nvars_(0),
      psat_(nullptr)
  {
    if (cmd_.command_given())
    {
      start();
    }
    else
    {
      psat_ = picosat_init();
      picosat_set_seed(psat_, 0);
    }
  }

  satsolver::~satsolver()
  {
    if (psat_)
    {
      picosat_reset(psat_);
      psat_ = nullptr;
    }
    else
    {
      delete cnf_tmp_;
      delete cnf_stream_;
    }
  }

  void satsolver::start()
  {
    cnf_tmp_ = create_tmpfile("sat-", ".cnf");
    cnf_stream_ = new std::ofstream(cnf_tmp_->name(), std::ios_base::trunc);
    cnf_stream_->exceptions(std::ofstream::failbit | std::ofstream::badbit);

    // Add empty line for the header
    *cnf_stream_ << "                                                 \n";
  }

  // Must be called only when SPOT_SATSOLVER is given
  void satsolver::end_clause()
  {
    *cnf_stream_ << '\n';
    nclauses_ += 1;
    if (nclauses_ < 0)
      throw std::runtime_error("too many SAT clauses (more than INT_MAX)");
  }

  void satsolver::adjust_nvars(int nvars)
  {
    if (nvars < 0)
      throw std::runtime_error("variable number must be at least 0");

    if (psat_)
    {
      picosat_adjust(psat_, nvars);
    }
    else
    {
      if (nvars < nvars_)
      {
        throw std::runtime_error(
            "wrong number of variables, a bigger one was already added");
      }
      nvars_ = nvars;
    }
  }

  void satsolver::add(std::initializer_list<int> values)
  {
    for (auto& v : values)
    {
      if (psat_)
      {
        picosat_add(psat_, v);
      }
      else
      {
        *cnf_stream_ << v << ' ';
        if (!v) // ..., 0)
          end_clause();

        if (nvars_ < v)
          nvars_ = v;
      }
    }
  }

  void satsolver::add(int v)
  {
    if (psat_)
    {
      picosat_add(psat_, v);
    }
    else
    {
      *cnf_stream_ << v << ' ';
      if (!v) // 0
        end_clause();

      if (v && nvars_ < v)
        nvars_ = v;
    }
  }

  int satsolver::get_nb_clauses() const
  {
    if (psat_)
      return picosat_added_original_clauses(psat_);
    return nclauses_;
  }

  int satsolver::get_nb_vars() const
  {
    if (psat_)
      return picosat_variables(psat_);
    return nvars_;
  }

  std::pair<int, int> satsolver::stats()
  {
    return std::make_pair(get_nb_vars(), get_nb_clauses());
  }

  satsolver::solution
  satsolver::picosat_get_solution(int res)
  {
    satsolver::solution sol;
    if (res == PICOSAT_SATISFIABLE)
    {
      int nvars = get_nb_vars();
      for (int lit = 1; lit <= nvars; ++lit)
      {
        if (picosat_deref(psat_, lit) > 0)
          sol.push_back(lit);
        else
          sol.push_back(-lit);
      }
    }
    return sol;
  }

  satsolver::solution_pair
  satsolver::get_solution()
  {
    solution_pair p;
    if (psat_)
    {
      p.first = 0; // A subprocess was not executed so nothing failed.
      int res = picosat_sat(psat_, -1); // -1: no limit (number of decisions).
      p.second = picosat_get_solution(res);
    }
    else
    {
      // Update header
      cnf_stream_->seekp(0);
      *cnf_stream_ << "p cnf " << get_nb_vars() << ' ' << get_nb_clauses();
      cnf_stream_->seekp(0, std::ios_base::end);
      if (!*cnf_stream_)
        throw std::runtime_error("Failed to update cnf header");

      temporary_file* output = create_tmpfile("sat-", ".out");
      p.first = cmd_.run(cnf_tmp_, output);
      p.second = satsolver_get_solution(output->name());
      delete output;
    }
    return p;
  }

  satsolver_command::satsolver_command() : satsolver(nullptr)
  {
    satsolver = getenv("SPOT_SATSOLVER");
    if (!satsolver)
      return;

    prime(satsolver);
    if (!has('I'))
      throw std::runtime_error("SPOT_SATSOLVER should contain %I to "
          "indicate how to use the input filename.");
    if (!has('O'))
      throw std::runtime_error("SPOT_SATSOLVER should contain %O to "
          "indicate how to use the output filename.");
  }

  bool
  satsolver_command::command_given()
  {
    return satsolver != nullptr;
  }

  int
  satsolver_command::run(printable* in, printable* out)
  {
    declare('I', in);
    declare('O', out);
    std::ostringstream s;
    format(s, satsolver);

    int res = system(s.str().c_str());
    if (res < 0 || (WIFEXITED(res) && WEXITSTATUS(res) == 127))
    {
      s << ": failed to execute";
      throw std::runtime_error(s.str());
    }

    // For POSIX shells, "The exit status of a command that
    // terminated because it received a signal shall be reported
    // as greater than 128."
    if (WIFEXITED(res) && WEXITSTATUS(res) >= 128)
    {
      s << ": terminated by signal";
      throw std::runtime_error(s.str());
    }

    if (WIFSIGNALED(res))
    {
      s << ": terminated by signal " << WTERMSIG(res);
      throw std::runtime_error(s.str());
    }

    return res;
  }
}
