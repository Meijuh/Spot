// -*- coding: utf-8 -*-
// Copyright (C) 2008, 2011, 2012, 2013, 2014, 2015, 2016 Laboratoire
// de Recherche et Développement de l'Epita (LRDE).
// Copyright (C) 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include <iostream>
#include <sstream>
#include <spot/twa/twa.hh>
#include <spot/twaalgos/stats.hh>
#include <spot/twaalgos/reachiter.hh>
#include <spot/tl/print.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  namespace
  {
    class stats_bfs: public twa_reachable_iterator_breadth_first
    {
    public:
      stats_bfs(const const_twa_ptr& a, twa_statistics& s)
        : twa_reachable_iterator_breadth_first(a), s_(s)
      {
      }

      void
      process_state(const state*, int, twa_succ_iterator*) override final
      {
        ++s_.states;
      }

      void
      process_link(const state*, int, const state*, int,
                   const twa_succ_iterator*) override
      {
        ++s_.edges;
      }

    private:
      twa_statistics& s_;
    };

    class sub_stats_bfs final: public stats_bfs
    {
    public:
      sub_stats_bfs(const const_twa_ptr& a, twa_sub_statistics& s)
        : stats_bfs(a, s), s_(s), seen_(a->ap_vars())
      {
      }

      void
      process_link(const state*, int, const state*, int,
                   const twa_succ_iterator* it) override
      {
        ++s_.edges;
        bdd cond = it->cond();
        while (cond != bddfalse)
          {
            cond -= bdd_satoneset(cond, seen_, bddtrue);
            ++s_.transitions;
          }
      }

    private:
      twa_sub_statistics& s_;
      bdd seen_;
    };
  } // anonymous


  std::ostream& twa_statistics::dump(std::ostream& out) const
  {
    out << "edges: " << edges << '\n';
    out << "states: " << states << '\n';
    return out;
  }

  std::ostream& twa_sub_statistics::dump(std::ostream& out) const
  {
    out << "transitions: " << transitions << '\n';
    this->twa_statistics::dump(out);
    return out;
  }

  twa_statistics
  stats_reachable(const const_twa_ptr& g)
  {
    twa_statistics s;
    stats_bfs d(g, s);
    d.run();
    return s;
  }

  twa_sub_statistics
  sub_stats_reachable(const const_twa_ptr& g)
  {
    twa_sub_statistics s;
    sub_stats_bfs d(g, s);
    d.run();
    return s;
  }

  void printable_formula::print(std::ostream& os, const char*) const
  {
    print_psl(os, val_);
  };

  void printable_scc_info::print(std::ostream& os, const char*) const
  {
    os << val_->scc_count();
  };


  stat_printer::stat_printer(std::ostream& os, const char* format)
    : format_(format)
  {
    declare('a', &acc_);
    declare('c', &scc_);
    declare('d', &deterministic_);
    declare('e', &edges_);
    declare('f', &form_);
    declare('g', &gen_acc_);
    declare('n', &nondetstates_);
    declare('p', &complete_);
    declare('r', &run_time_);
    declare('s', &states_);
    declare('S', &scc_);        // Historical.  Deprecated.  Use %c instead.
    declare('t', &trans_);
    set_output(os);
    if (format)
      prime(format);
  }

  std::ostream&
  stat_printer::print(const const_twa_graph_ptr& aut,
                      formula f, double run_time)
  {
    form_ = f;
    run_time_ = run_time;

    if (has('t'))
      {
        twa_sub_statistics s = sub_stats_reachable(aut);
        states_ = s.states;
        edges_ = s.edges;
        trans_ = s.transitions;
      }
    else if (has('s') || has('e'))
      {
        twa_sub_statistics s = sub_stats_reachable(aut);
        states_ = s.states;
        edges_ = s.edges;
      }

    if (has('a'))
      acc_ = aut->num_sets();

    // %S was renamed to %c in Spot 1.2, so that autfilt could use %S
    // and %s to designate the state numbers in input and output
    // automate.  We still recognize %S an obsolete and undocumented
    // alias for %c, if it is not overridden by a subclass.
    if (has('c') || has('S'))
      scc_.automaton(aut);

    if (has('n'))
      {
        nondetstates_ = count_nondet_states(aut);
        deterministic_ = (nondetstates_ == 0);
      }
    else if (has('d'))
      {
        // This is more efficient than calling count_nondet_state().
        deterministic_ = is_deterministic(aut);
      }

    if (has('p'))
      {
        complete_ = is_complete(aut);
      }

    if (has('g'))
      {
        std::ostringstream os;
        os << aut->get_acceptance();
        gen_acc_ = os.str();
      }

    auto& os = format(format_);
    scc_.reset(); // Make sure we do not hold a pointer to the automaton
    return os;
  }

}
