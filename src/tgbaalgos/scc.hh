// -*- coding: utf-8 -*-
// Copyright (C) 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015
// Laboratoire de Recherche et Développement de l'Epita.
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

#ifndef SPOT_TGBAALGOS_SCC_HH
# define SPOT_TGBAALGOS_SCC_HH

#include <map>
#include <stack>
#include <vector>
#include "tgba/tgba.hh"
#include <iosfwd>
#include "misc/hash.hh"
#include "misc/bddlt.hh"

namespace spot
{

  /// Build a map of Strongly Connected components in in a TGBA.
  class SPOT_API scc_map
  {
  public:
    typedef std::map<unsigned, bdd> succ_type;
    typedef std::set<bdd, bdd_less_than> cond_set;

    /// \brief Constructor.
    ///
    /// This will note compute the map initially.  You should call
    /// build_map() to do so.
    scc_map(const const_tgba_ptr& aut);

    ~scc_map();

    /// Actually compute the graph of strongly connected components.
    void build_map();

    /// Get the automaton for which the map has been constructed.
    const_tgba_ptr get_aut() const;

    /// \brief Get the number of SCC in the automaton.
    ///
    /// SCCs are labelled from 0 to scc_count()-1.
    ///
    /// \pre This should only be called once build_map() has run.
    unsigned scc_count() const;

    /// \brief Get number of the SCC containing the initial state.
    ///
    /// \pre This should only be called once build_map() has run.
    unsigned initial() const;

    /// \brief Successor SCCs of a SCC.
    ///
    /// \pre This should only be called once build_map() has run.
    const succ_type& succ(unsigned n) const;

    /// \brief Return whether an SCC is trivial.
    ///
    /// Trivial SCCs have one state and no self-loop.
    ///
    /// \pre This should only be called once build_map() has run.
    bool trivial(unsigned n) const;

    /// \brief Return whether an SCC is accepting.
    ///
    /// \pre This should only be called once build_map() has run.
    bool accepting(unsigned n) const;

    /// \brief Return the set of conditions occurring in an SCC.
    ///
    /// \pre This should only be called once build_map() has run.
    const cond_set& cond_set_of(unsigned n) const;

    /// \brief Return the set of atomic properties occurring on the
    /// transitions leaving states from SCC \a n.
    ///
    /// The transitions considered are all transitions inside SCC
    /// \a n, as well as the transitions leaving SCC \a n.
    ///
    /// \return a BDD that is a conjuction of all atomic properties
    /// occurring on the transitions leaving the states of SCC \a n.
    ///
    /// \pre This should only be called once build_map() has run.
    bdd ap_set_of(unsigned n) const;

    /// \brief Return the set of atomic properties reachable from this SCC.
    ///
    /// \return a BDD that is a conjuction of all atomic properties
    /// occurring on the transitions reachable from this SCC n.
    ///
    /// \pre This should only be called once build_map() has run.
    bdd aprec_set_of(unsigned n) const;

    /// \brief Return the set of acceptance conditions occurring in an SCC.
    ///
    /// \pre This should only be called once build_map() has run.
    acc_cond::mark_t acc_set_of(unsigned n) const;

    /// \brief Return the set of useful acceptance conditions of SCC \a n.
    ///
    /// Useless acceptances conditions are always implied by other acceptances
    /// conditions.  This returns all the other acceptance conditions.
    const std::set<acc_cond::mark_t>& useful_acc_of(unsigned n) const;

    /// \brief Return the set of states of an SCC.
    ///
    /// The states in the returned list are still owned by the scc_map
    /// instance.  They should NOT be destroyed by the client code.
    ///
    /// \pre This should only be called once build_map() has run.
    const std::list<const state*>& states_of(unsigned n) const;

    /// \brief Return one state of an SCC.
    ///
    /// The state in the returned list is still owned by the scc_map
    /// instance.  It should NOT be destroyed by the client code.
    ///
    /// \pre This should only be called once build_map() has run.
    const state* one_state_of(unsigned n) const;

    /// \brief Return the number of the SCC a state belongs too.
    ///
    /// \pre This should only be called once build_map() has run.
    unsigned scc_of_state(const state* s) const;

    /// \brief Return the number of self loops in the automaton.
    unsigned self_loops() const;

  protected:
    bdd update_supp_rec(unsigned state);
    int relabel_component();

    struct scc
    {
    public:
      scc(int index) : index(index), acc(0U),
		       supp(bddtrue), supp_rec(bddfalse),
		       trivial(true) {};
      /// Index of the SCC.
      int index;
      /// The union of all acceptance conditions of transitions which
      /// connect the states of the connected component.
      acc_cond::mark_t acc;
      /// States of the component.
      std::list<const state*> states;
      /// Set of conditions used in the SCC.
      cond_set conds;
      /// Conjunction of atomic propositions used in the SCC.
      bdd supp;
      /// Conjunction of atomic propositions used in the SCC.
      bdd supp_rec;
      /// Successor SCC.
      succ_type succ;
      /// Trivial SCC have one state and no self-loops.
      bool trivial;
      /// \brief Set of acceptance combinations used in the SCC.
      std::set<acc_cond::mark_t> useful_acc;
    };

    const_tgba_ptr aut_;		// Automata to decompose.
    typedef std::list<scc> stack_type;
    stack_type root_;		// Stack of SCC roots.
    std::stack<acc_cond::mark_t> arc_acc_; // A stack of acceptance conditions
				// between each of these SCC.
    std::stack<bdd> arc_cond_;	// A stack of conditions
				// between each of these SCC.
    typedef std::unordered_map<const state*, int,
			       state_ptr_hash, state_ptr_equal> hash_type;
    hash_type h_;		// Map of visited states.  Values >= 0
                                // designate maximal SCC.  Values < 0
                                // number states that are part of
                                // incomplete SCCs being completed.
    int num_;			// Number of visited nodes, negated.
    typedef std::pair<const spot::state*, tgba_succ_iterator*> pair_state_iter;
    std::stack<pair_state_iter> todo_; // DFS stack.  Holds (STATE,
				       // ITERATOR) pairs where
				       // ITERATOR is an iterator over
				       // the successors of STATE.
				       // ITERATOR should always be
				       // freed when TODO is popped,
				       // but STATE should not because
				       // it is used as a key in H.

    typedef std::vector<scc> scc_map_type;
    scc_map_type scc_map_; // Map of constructed maximal SCC.
			   // SCC number "n" in H_ corresponds to entry
                           // "n" in SCC_MAP_.
    unsigned self_loops_; // Self loops count.
 };

  SPOT_API std::ostream&
  dump_scc_dot(const const_tgba_ptr& a,
	       std::ostream& out, bool verbose = false);
  SPOT_API std::ostream&
  dump_scc_dot(const scc_map& m, std::ostream& out, bool verbose = false);
}

#endif // SPOT_TGBAALGOS_SCC_HH
