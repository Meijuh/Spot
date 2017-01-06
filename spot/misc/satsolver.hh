// -*- coding: utf-8 -*-
// Copyright (C) 2013 Laboratoire de Recherche et Développement
// de l'Epita.
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

#include <spot/misc/common.hh>
#include <spot/misc/tmpfile.hh>
#include <vector>
#include <stdexcept>
#include <iosfwd>
#include <initializer_list>

namespace spot
{
  class printable;

  class clause_counter
  {
  private:
    int count_;

  public:
    clause_counter()
      : count_(0)
    {
    }

    void check() const
    {
      if (count_ < 0)
        throw std::runtime_error("too many SAT clauses (more than INT_MAX)");
    }

    clause_counter& operator++()
    {
      ++count_;
      check();
      return *this;
    }

    clause_counter& operator+=(int n)
    {
      count_ += n;
      check();
      return *this;
    }

    int nb_clauses() const
    {
      return count_;
    }
  };

  /// \brief Interface with a SAT solver.
  ///
  /// Call start() to initialize the cnf file. This class provides the
  /// necessary functions to handle the cnf file, add clauses, count them,
  /// update the header, add some comments...
  /// It is not possible to write in the file without having to call these
  /// functions.
  ///
  /// The satsolver called can be configured via the
  /// <code>SPOT_SATSOLVER</code> environment variable. It must be this set
  /// following this: "satsolver -verb=0 %I >%O".
  ///
  /// where %I and %O are replaced by input and output files.
  class SPOT_API satsolver
  {
  public:
    satsolver();
    ~satsolver();

    /// \brief Initialize private attributes
    void start();

    /// \brief Add a list of lit. to the current clause.
    void add(std::initializer_list<int> values);

    /// \brief Add a single lit. to the current clause.
    void add(int v);

    /// \breif Get the current number of clauses.
    int get_nb_clauses() const;

    /// \breif Update cnf_file's header with the correct stats.
    std::pair<int, int> stats(int nvars);

    /// \breif Create an unsatisfiable cnf_file, return stats about it.
    std::pair<int, int> stats();

    /// \breif Add a comment in cnf file.
    template<typename T>
    void comment_rec(T single)
    {
      *cnf_stream_ << single << ' ';
    }

    /// \breif Add a comment in cnf_file.
    template<typename T, typename... Args>
    void comment_rec(T first, Args... args)
    {
      *cnf_stream_ << first << ' ';
      comment_rec(args...);
    }

    /// \breif Add a comment in the cnf_file, starting with 'c'.
    template<typename T>
    void comment(T single)
    {
      *cnf_stream_ << "c " << single << ' ';
    }

    /// \breif Add comment in the cnf_file, starting with 'c'.
    template<typename T, typename... Args>
    void comment(T first, Args... args)
    {
      *cnf_stream_ << "c " << first << ' ';
      comment_rec(args...);
    }

    typedef std::vector<int> solution;
    typedef std::pair<int, solution> solution_pair;
    solution_pair get_solution();

  private:
    /// \breif End the current clause and increment the counter.
    void end_clause();

  private:
    temporary_file* cnf_tmp_;
    std::ostream* cnf_stream_;
    clause_counter* nclauses_;

  };

  /// \brief Extract the solution of a SAT solver output.
  SPOT_API satsolver::solution
  satsolver_get_solution(const char* filename);
}
