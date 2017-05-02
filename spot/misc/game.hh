// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement
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

#pragma once

#include <algorithm>
#include <memory>
#include <ostream>
#include <unordered_map>
#include <vector>

#include <bddx.h>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/parity.hh>

namespace spot
{

class SPOT_API parity_game
{
private:
  const const_twa_graph_ptr dpa_;
  const std::vector<bool> owner_;

public:
  /// \a parity_game provides an interface to manipulate a deterministic parity
  /// automaton as a parity game, including methods to solve the game.
  ///
  /// \param dpa the underlying deterministic parity automaton
  /// \param owner a vector of Booleans indicating the owner of each state,
  /// with the convention that true represents player 1 and false represents
  /// player 0.
  parity_game(const twa_graph_ptr dpa, std::vector<bool> owner)
    : dpa_(dpa), owner_(owner)
  {
    bool max;
    bool odd;
    dpa_->acc().is_parity(max, odd, true);
    SPOT_ASSERT(max && odd);
    SPOT_ASSERT(owner_.size() == dpa_->num_states());
  }

  unsigned num_states() const
  {
    return dpa_->num_states();
  }

  unsigned get_init_state_number() const
  {
    return dpa_->get_init_state_number();
  }

  internal::state_out<const twa_graph::graph_t>
  out(unsigned src) const
  {
    return dpa_->out(src);
  }

  internal::state_out<const twa_graph::graph_t>
  out(unsigned src)
  {
    return dpa_->out(src);
  }

  bool owner(unsigned src) const
  {
    return owner_[src];
  }

  unsigned max_parity() const
  {
    unsigned max_parity = 0;
      for (auto& e: dpa_->edges())
        max_parity = std::max(max_parity, e.acc.max_set());
    SPOT_ASSERT(max_parity);
    return max_parity - 1;
  }

  /// Print the parity game in PGSolver's format.
  void print(std::ostream& os);

  typedef std::unordered_set<unsigned> region_t;
  // Map state number to index of the transition to take.
  typedef std::unordered_map<unsigned, unsigned> strategy_t;

  /// Compute the winning strategy and winning region of this game for player
  /// 1 using Zielonka's recursive algorithm.
  /** \verbatim
      @article{ zielonka.98.tcs
        title = "Infinite games on finitely coloured graphs with applications to
        automata on infinite trees",
        journal = "Theoretical Computer Science",
        volume = "200",
        number = "1",
        pages = "135 - 183",
        year = "1998",
        author = "Wieslaw Zielonka",
      }
      \endverbatim */
  std::pair<region_t, strategy_t> solve() const;

  /// Whether player 1 has a winning strategy from the initial state.
  /// Implements Calude et al.'s quasipolynomial time algorithm.
  /** \verbatim
      @inproceedings{calude.17.stoc,
        author = {Calude, Cristian S. and Jain, Sanjay and Khoussainov,
                  Bakhadyr and Li, Wei and Stephan, Frank},
        title = {Deciding Parity Games in Quasipolynomial Time},
        booktitle = {Proceedings of the 49th Annual ACM SIGACT Symposium on
                     Theory of Computing},
        series = {STOC 2017},
        year = {2017},
        isbn = {978-1-4503-4528-6},
        location = {Montreal, Canada},
        pages = {252--263},
        numpages = {12},
        url = {http://doi.acm.org/10.1145/3055399.3055409},
        doi = {10.1145/3055399.3055409},
        acmid = {3055409},
        publisher = {ACM},
        address = {New York, NY, USA},
        keywords = {Muller Games, Parity Games, Quasipolynomial Time Algorithm},
      }
      \endverbatim */
  bool solve_qp() const;

private:
  typedef twa_graph::graph_t::edge_storage_t edge_t;

  // Compute (in place) a set of states from which player can force a visit
  // through set, and a strategy to do it.
  // if attr_max is true, states that can force a visit through an edge with
  // max parity are also counted in.
  strategy_t attractor(const region_t& subgame, region_t& set,
                       unsigned max_parity, bool odd,
                       bool attr_max = false) const;

  // Compute the winning strategy and winning region for player 1.
  std::pair<region_t, strategy_t>
  solve_rec(region_t& subgame, unsigned max_parity) const;
};


class reachability_state: public state
{
private:
  unsigned num_;
  std::vector<unsigned> b_;
  bool anke_;

public:
  reachability_state(unsigned state, const std::vector<unsigned>& b,
                          bool anke)
    : num_(state), b_(b), anke_(anke)
  {
  }

  int compare(const state* other) const override;

  bool operator==(const reachability_state& o) const
  {
    return compare(&o) == 0;
  }

  bool operator!=(const reachability_state& o) const
  {
    return compare(&o) != 0;
  }

  bool operator<(const reachability_state& o) const;

  size_t hash() const override
  {
    size_t hash = wang32_hash(num_);
    for (unsigned i = 0; i < b_.size(); ++i)
      hash ^= wang32_hash(b_[i]) ^ wang32_hash(i);
    return hash;
  }

  reachability_state* clone() const override
  {
    return new reachability_state(*this);
  }

  std::vector<unsigned> b() const
  {
    return b_;
  }

  unsigned num() const
  {
    return num_;
  }

  bool anke() const
  {
    return anke_;
  }
};

typedef std::shared_ptr<const reachability_state>
  const_reachability_state_ptr;

struct reachability_state_hash
{
  size_t operator()(const reachability_state& state) const
  {
    return state.hash();
  }
};

class reachability_game_succ_iterator final: public twa_succ_iterator
{
private:
  const parity_game& pg_;
  const reachability_state& state_;
  internal::edge_iterator<const twa_graph::graph_t> it_;

public:
  reachability_game_succ_iterator(const parity_game& pg,
                                  const reachability_state& s)
    : pg_(pg), state_(s)
  {
  }

  bool first() override
  {
    it_ = pg_.out(state_.num()).begin();
    return it_ != pg_.out(state_.num()).end();
  }

  bool next() override
  {
    ++it_;
    return it_ != pg_.out(state_.num()).end();
  }

  bool done() const override
  {
    return it_ == pg_.out(state_.num()).end();
  }

  const reachability_state* dst() const override;

  bdd cond() const override
  {
    return bddtrue;
  }

  acc_cond::mark_t acc() const override
  {
    return 0;
  }
};

// On-the-fly reachability game interface for a max even parity game such
// that a target is reachable iff there is a memoryless winning strategy
// in the parity game for player 1.
class reachability_game final: public twa
{
private:
  typedef std::unordered_map<spot::reachability_state, unsigned,
                             spot::reachability_state_hash> wincount_t;
  typedef std::unordered_map<spot::reachability_state,
                             std::vector<spot::reachability_state>,
                             spot::reachability_state_hash> parents_t;

  const parity_game& pg_;
  // number of successors that need to have a winning strategy in order for
  // a given node to have a winning strategy.
  wincount_t c_;
  parents_t parents_;
  const_reachability_state_ptr init_state_; // cache

public:

  reachability_game(const parity_game& pg)
    : twa(std::make_shared<bdd_dict>()), pg_(pg)
  {
    init_state_ = std::shared_ptr<const reachability_state>(get_init_state());
  }

  const reachability_state* get_init_state() const override;

  reachability_game_succ_iterator* succ_iter(const state* s) const override;

  std::string format_state(const state* s) const override;

  bool is_reachable();

private:
  bool mark(const spot::reachability_state& s);

  bool is_target(const reachability_state& s);

};

}
