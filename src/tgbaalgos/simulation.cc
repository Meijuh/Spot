// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014 Laboratoire de Recherche et Développement
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

#include <queue>
#include <map>
#include <utility>
#include <cmath>
#include <limits>
#include "tgba/tgbaexplicit.hh"
#include "simulation.hh"
#include "priv/acccompl.hh"
#include "misc/minato.hh"
#include "tgba/bddprint.hh"
#include "tgbaalgos/reachiter.hh"
#include "tgbaalgos/sccfilter.hh"
#include "tgbaalgos/scc.hh"
#include "tgbaalgos/dupexp.hh"

// The way we developed this algorithm is the following: We take an
// automaton, and reverse all these acceptance conditions.  We reverse
// them to go make the meaning of the signature easier. We are using
// bdd, and we want to let it make all the simplification. Because of
// the format of the acceptance condition, it doesn't allow easy
// simplification. Instead of encoding them as: "a!b!c + !ab!c", we
// use them as: "ab". We complement them because we want a
// simplification if the condition of the transition A implies the
// transition of B, and if the acceptance condition of A is included
// in the acceptance condition of B. To let the bdd makes the job, we
// revert them.

// Then, to check if a transition i-dominates another, we'll use the bdd:
// "sig(transA) = cond(trans) & acc(trans) & implied(class(trans->state))"
// Idem for sig(transB). The 'implied'
// (represented by a hash table 'relation_' in the implementation) is
// a conjunction of all the class dominated by the class of the
// destination. This is how the relation is included in the
// signature. It makes the simplifications alone, and the work is
// done.  The algorithm is cut into several step:
//
// 1. Run through the tgba and switch the acceptance condition to their
//    negation, and initializing relation_ by the 'init_ -> init_' where
//    init_ is the bdd which represents the class. This function is the
//    constructor of Simulation.
// 2. Enter in the loop (run).
//    - Rename the class.
//    - run through the automaton and computing the signature of each
//      state. This function is `update_sig'.
//    - Enter in a double loop to adapt the partial order, and set
//      'relation_' accordingly. This function is `update_po'.
// 3. Rename the class (to actualize the name in the previous_class and
//    in relation_).
// 4. Building an automaton with the result, with the condition:
// "a transition in the original automaton appears in the simulated one
// iff this transition is included in the set of i-maximal neighbour."
// This function is `build_output'.
// The automaton simulated is recomplemented to come back to its initial
// state when the object Simulation is destroyed.
//
// Obviously these functions are possibly cut into several little one.
// This is just the general development idea.

// How to use isop:
// I need all variable non_acceptance & non_class.
// bdd_support(sig(X)): All var
// bdd_support(sig(X)) - allacc - allclassvar


// TODO LIST: Play on the order of the selection in the
// dont_care_simulation. The good place to work is in add_to_map_imply.


namespace spot
{
  namespace
  {
    // Some useful typedef:

    // Used to get the signature of the state.
    typedef std::vector<bdd> vector_state_bdd;

    typedef std::vector<const state*> vector_state_state;


    // Get the list of state for each class.
    typedef std::map<bdd, std::list<unsigned>,
                     bdd_less_than> map_bdd_lstate;

    typedef std::map<bdd, unsigned, bdd_less_than> map_bdd_state;

    // Our constraint: (state_src, state_dst) = to_add.
    // We define the couple of state as the key of the constraint.
    typedef std::pair<const state*, const state*> constraint_key;

    // But we need a comparator for that key.
    struct constraint_key_comparator
    {
      bool operator()(const constraint_key& l,
                      const constraint_key& r) const
      {
        if (l.first->compare(r.first) < 0)
          return true;
        else
          if (l.first->compare(r.first) > 0)
            return false;

        if (l.second->compare(r.second) < 0)
          return true;
        else
          if (l.second->compare(r.second) > 0)
            return false;

        return false;
      }
    };

    // The full definition of the constraint.
    typedef std::map<constraint_key, bdd,
                     constraint_key_comparator> map_constraint;

    typedef std::tuple<const state*, const state*, bdd> constraint;

    // Helper to create the map of constraints to give to the
    // simulation.
    void add_to_map(const std::list<constraint>& list,
                    map_constraint& feed_me)
    {
      for (auto& p: list)
	feed_me.insert(std::make_pair(std::make_pair(std::get<0>(p),
						     std::get<1>(p)),
				      std::get<2>(p)));
    }


    // This class helps to compare two automata in term of
    // size.
    struct automaton_size
    {
      automaton_size()
        : transitions(0),
          states(0)
      {
      }

      inline bool operator!=(const automaton_size& r)
      {
        return transitions != r.transitions || states != r.states;
      }

      inline bool operator<(const automaton_size& r)
      {
        if (states < r.states)
          return true;
        if (states > r.states)
          return false;

        if (transitions < r.transitions)
          return true;
        if (transitions > r.transitions)
          return false;

        return false;
      }

      inline bool operator>(const automaton_size& r)
      {
        if (states < r.states)
          return false;
        if (states > r.states)
          return true;

        if (transitions < r.transitions)
          return false;
        if (transitions > r.transitions)
          return true;

        return false;
      }

      int transitions;
      int states;
    };

    // The direct_simulation. If Cosimulation is true, we are doing a
    // cosimulation.
    template <bool Cosimulation, bool Sba>
    class direct_simulation
    {
    protected:
      // Shortcut used in update_po and go_to_next_it.
      typedef std::map<bdd, bdd, bdd_less_than> map_bdd_bdd;
    public:
      direct_simulation(const tgba* t, const map_constraint* map_cst = 0)
        : a_(0),
          po_size_(0),
          all_class_var_(bddtrue),
          map_cst_(map_cst),
          original_(t)
      {
        // We need to do a dupexp for being able to run scc_map later.
        // new_original_ is the map that contains the relation between
        // the names (addresses) of the states in the automaton
        // returned by dupexp, and in automaton given in argument to
        // the constructor.
        a_ = tgba_dupexp_dfs(t, new_original_);
        scc_map_ = new scc_map(a_);
        scc_map_->build_map();
        old_a_ = a_;


	acc_compl ac(a_->all_acceptance_conditions(),
		     a_->neg_acceptance_conditions());

	// Replace all the acceptance conditions by their complements.
	// (In the case of Cosimulation, we also flip the transitions.)
	{
	  if (Cosimulation)
	    {
	      bdd_dict* bd = a_->get_dict();
	      a_ = new tgba_digraph(bd);
	      bd->register_all_variables_of(old_a_, a_);
	      a_->copy_acceptance_conditions_of(old_a_);
	    }
	  tgba_digraph::graph_t& gout = a_->get_graph();
	  tgba_digraph::graph_t& gin = old_a_->get_graph();
	  unsigned ns = gin.num_states();
	  if (Cosimulation)
	    gout.new_states(ns);
	  for (unsigned s = 0; s < ns; ++s)
	    {
	      for (auto& t: gin.out(s))
		{
		  bdd acc;
		  if (Sba && Cosimulation)
		    {
		      // If the acceptance is interpreted as
		      // state-based, to apply the reverse simulation
		      // on a SBA, we should pull the acceptance of
		      // the destination state on its incoming arcs
		      // (which now become outgoing arcs after
		      // transposition).
		      acc = bddfalse;
		      for (auto& td: gin.out(t.dst))
			{
			  acc = ac.complement(td.acc);
			  break;
			}
		    }
		  else
		    {
		      acc = ac.complement(t.acc);
		    }
		  if (Cosimulation)
		    gout.new_transition(t.dst, s, t.cond, acc);
		  else
		    t.acc = acc;
		}
	    }
	  size_a_ = ns;
	}

	// Now, we have to get the bdd which will represent the
	// class. We register one bdd by state, because in the worst
	// case, |Class| == |State|.
	unsigned set_num = a_->get_dict()
	  ->register_anonymous_variables(size_a_ + 1, this);

        all_acceptance_conditions_ = a_->all_acceptance_conditions();
        all_proms_ = bdd_support(all_acceptance_conditions_);

        bdd_initial = bdd_ithvar(set_num++);
	bdd init = bdd_ithvar(set_num++);

	used_var_.push_back(init);

	// Initialize all classes to init.
	previous_class_.resize(size_a_);
	for (unsigned s = 0; s < size_a_; ++s)
	  previous_class_[s] = init;

	// Put all the anonymous variable in a queue, and record all
	// of these in a variable all_class_var_ which will be used
	// to understand the destination part in the signature when
	// building the resulting automaton.
	all_class_var_ = init;
	for (unsigned i = set_num; i < set_num + size_a_ - 1; ++i)
          {
            free_var_.push(i);
            all_class_var_ &= bdd_ithvar(i);
          }

	relation_[init] = init;
      }


      // Reverse all the acceptance condition at the destruction of
      // this object, because it occurs after the return of the
      // function simulation.
      virtual ~direct_simulation()
      {
	a_->get_dict()->unregister_all_my_variables(this);
        delete scc_map_;

	delete old_a_;
        // a_ is a new automaton only if we are doing a cosimulation.
        if (Cosimulation)
          delete a_;
      }

      // Update the name of the classes.
      void update_previous_class()
      {
	std::list<bdd>::iterator it_bdd = used_var_.begin();

	// We run through the map bdd/list<state>, and we update
	// the previous_class_ with the new data.
	for (auto& p: bdd_lstate_)
          {
	    // If the signature of a state is bddfalse (no
	    // transitions) the class of this state is bddfalse
	    // instead of an anonymous variable. It allows
	    // simplifications in the signature by removing a
	    // transition which has as a destination a state with
	    // no outgoing transition.
	    if (p.first == bddfalse)
	      for (auto s: p.second)
		previous_class_[s] = bddfalse;
	    else
	      for (auto s: p.second)
		previous_class_[s] = *it_bdd;
	    ++it_bdd;
          }
      }

      void main_loop()
      {
	unsigned int nb_partition_before = 0;
	unsigned int nb_po_before = po_size_ - 1;
	while (nb_partition_before != bdd_lstate_.size()
	       || nb_po_before != po_size_)
          {
            update_previous_class();
            nb_partition_before = bdd_lstate_.size();
            bdd_lstate_.clear();
            nb_po_before = po_size_;
            po_size_ = 0;
            update_sig();
            go_to_next_it();
          }

	update_previous_class();
      }

      // The core loop of the algorithm.
      tgba_digraph* run()
      {
        main_loop();
	return build_result();
      }

      // Take a state and compute its signature.
      bdd compute_sig(unsigned src)
      {
        bdd res = bddfalse;

        for (auto& t: a_->get_graph().out(src))
          {
            bdd acc = bddtrue;

	    map_constraint::const_iterator it;
	    // Check if we have a constraint about this edge in the
	    // original automaton.
	    if (map_cst_
		&& ((it = map_cst_
		     ->find(std::make_pair(new_original_[src],
					   new_original_[t.dst])))
		    != map_cst_->end()))
	      {
		acc = it->second;
	      }
	    else
	      {
		acc = t.acc;
	      }

	    // to_add is a conjunction of the acceptance condition,
	    // the label of the transition and the class of the
	    // destination and all the class it implies.
	    bdd to_add = acc & t.cond & relation_[previous_class_[t.dst]];

	    res |= to_add;
	  }

        // When we Cosimulate, we add a special flag to differentiate
        // the initial state from the other.
        if (Cosimulation && src == 0)
          res |= bdd_initial;

        return res;
      }


      void update_sig()
      {
	for (unsigned s = 0; s < size_a_; ++s)
	  bdd_lstate_[compute_sig(s)].push_back(s);
      }


      // This method rename the color set, update the partial order.
      void go_to_next_it()
      {
	int nb_new_color = bdd_lstate_.size() - used_var_.size();


        // If we have created more partitions, we need to use more
        // variables.
	for (int i = 0; i < nb_new_color; ++i)
          {
            assert(!free_var_.empty());
            used_var_.push_back(bdd_ithvar(free_var_.front()));
            free_var_.pop();
          }


        // If we have reduced the number of partition, we 'free' them
        // in the free_var_ list.
	for (int i = 0; i > nb_new_color; --i)
          {
            assert(!used_var_.empty());
            free_var_.push(bdd_var(used_var_.front()));
            used_var_.pop_front();
          }


	assert((bdd_lstate_.size() == used_var_.size())
               || (bdd_lstate_.find(bddfalse) != bdd_lstate_.end()
                   && bdd_lstate_.size() == used_var_.size() + 1));

	// Now we make a temporary hash_table which links the tuple
	// "C^(i-1), N^(i-1)" to the new class coloring.  If we
	// rename the class before updating the partial order, we
	// loose the information, and if we make it after, I can't
	// figure out how to apply this renaming on rel_.
	// It adds a data structure but it solves our problem.
	map_bdd_bdd now_to_next;

	std::list<bdd>::iterator it_bdd = used_var_.begin();

	for (auto& p: bdd_lstate_)
          {
	    // If the signature of a state is bddfalse (no
	    // transitions) the class of this state is bddfalse
	    // instead of an anonymous variable. It allows
	    // simplifications in the signature by removing a
	    // transition which has as a destination a state with
	    // no outgoing transition.
	    now_to_next[p.first] =
	      (p.first == bddfalse) ? bddfalse : *it_bdd;
	    ++it_bdd;
          }

	update_po(now_to_next, relation_);
      }

      // This function computes the new po with previous_class_ and
      // the argument. `now_to_next' contains the relation between the
      // signature and the future name of the class.  We need a
      // template parameter because we use this function with a
      // map_bdd_bdd, but later, we need a list_bdd_bdd. So to
      // factorize some code we use a template.
      template <typename container_bdd_bdd>
      void update_po(const container_bdd_bdd& now_to_next,
                     map_bdd_bdd& relation)
      {
	// This loop follows the pattern given by the paper.
	// foreach class do
	// |  foreach class do
	// |  | update po if needed
	// |  od
	// od

	for (typename container_bdd_bdd::const_iterator it1
               = now_to_next.begin();
	     it1 != now_to_next.end();
	     ++it1)
          {
            bdd accu = it1->second;
            for (typename container_bdd_bdd::const_iterator it2
                   = now_to_next.begin();
                 it2 != now_to_next.end();
                 ++it2)
              {
                // Skip the case managed by the initialization of accu.
                if (it1 == it2)
                  continue;

                if (bdd_implies(it1->first, it2->first))
                  {
                    accu &= it2->second;
                    ++po_size_;
                  }
              }
            relation[it1->second] = accu;
          }
      }

      automaton_size get_stat() const
      {
        assert(stat.states != 0);

        return stat;
      }

      bool result_is_deterministic() const
      {
        assert(stat.states != 0);

        return res_is_deterministic;
      }



      // Build the minimal resulting automaton.
      tgba_digraph* build_result()
      {
	// We have all the a_'s acceptances conditions
	// complemented.  So we need to complement it when adding a
	// transition.  We *must* keep the complemented because it
	// is easy to know if an acceptance condition is maximal or
	// not.
	acc_compl reverser(all_acceptance_conditions_,
			   a_->neg_acceptance_conditions());

	bdd_dict* d = a_->get_dict();
	tgba_digraph* res = new tgba_digraph(d);
	d->register_all_variables_of(a_, res);
	res->set_acceptance_conditions(all_acceptance_conditions_);

	bdd sup_all_acc = bdd_support(all_acceptance_conditions_);
	// Non atomic propositions variables (= acc and class)
	bdd nonapvars = sup_all_acc & bdd_support(all_class_var_);

	auto* gb = res->create_namer<int>();

	// Create one state per partition.
	for (auto& p: bdd_lstate_)
          {
            bdd cl = previous_class_[p.second.front()];
	    // A state may be referred to either by
	    // its class, or by all the implied classes.
	    auto s = gb->new_state(cl.id());
	    gb->alias_state(s, relation_[cl].id());
          }

	// Acceptance of states.  Only used if Sba && Cosimulation.
	std::vector<bdd> accst;
	if (Sba && Cosimulation)
	  accst.resize(res->num_states(), bddfalse);

        stat.states = bdd_lstate_.size();
        stat.transitions = 0;

        unsigned nb_satoneset = 0;
        unsigned nb_minato = 0;

	// For each class, we will create
	// all the transitions between the states.
	for (auto& p: bdd_lstate_)
          {
	    // All states in p.second have the same class, so just
	    // pick the class of the first one first one.
	    bdd src = previous_class_[p.second.front()];

            // Get the signature to derive successors.
            bdd sig = compute_sig(p.second.front());

            if (Cosimulation)
              sig = bdd_compose(sig, bddfalse, bdd_var(bdd_initial));

            // Get all the variable in the signature.
            bdd sup_sig = bdd_support(sig);

            // Get the variable in the signature which represents the
            // conditions.
            bdd sup_all_atomic_prop = bdd_exist(sup_sig, nonapvars);

            // Get the part of the signature composed only with the atomic
            // proposition.
            bdd all_atomic_prop = bdd_exist(sig, nonapvars);

	    // First loop over all possible valuations atomic properties.
            while (all_atomic_prop != bddfalse)
	      {
		bdd one = bdd_satoneset(all_atomic_prop,
					sup_all_atomic_prop,
					bddtrue);
		all_atomic_prop -= one;

		// For each possible valuation, iterate over all possible
		// destination classes.   We use minato_isop here, because
		// if the same valuation of atomic properties can go
		// to two different classes C1 and C2, iterating on
		// C1 + C2 with the above bdd_satoneset loop will see
		// C1 then (!C1)C2, instead of C1 then C2.
		// With minatop_isop, we ensure that the no negative
		// class variable will be seen (likewise for promises).
		minato_isop isop(sig & one);

                ++nb_satoneset;

		bdd cond_acc_dest;
		while ((cond_acc_dest = isop.next()) != bddfalse)
		  {
                    ++stat.transitions;

                    ++nb_minato;

		    // Take the transition, and keep only the variable which
		    // are used to represent the class.
		    bdd dst = bdd_existcomp(cond_acc_dest,
					     all_class_var_);

		    // Keep only ones who are acceptance condition.
		    bdd acc = bdd_existcomp(cond_acc_dest, sup_all_acc);

		    // Keep the other!
		    bdd cond = bdd_existcomp(cond_acc_dest,
					     sup_all_atomic_prop);

		    // Because we have complemented all the acceptance
		    // conditions on the input automaton, we must
		    // revert them to create a new transition.
		    acc = reverser.reverse_complement(acc);

		    if (Cosimulation)
		      {
			gb->new_transition(dst.id(), src.id(),
					   cond, Sba ? bddfalse : acc);
			if (Sba)
			  // acc should be attached to src, or rather,
			  // in our transition-based representation)
			  // to all transitions leaving src.  As we
			  // can't do this here, store this in a table
			  // so we can fix it later.
			  accst[gb->get_state(src.id())] = acc;
		      }
		    else
		      {
			gb->new_transition(src.id(), dst.id(), cond, acc);
		      }
		  }
	      }
          }

	res->set_init_state(gb->get_state(previous_class_
					  [a_->get_init_state_number()].id()));

	res->merge_transitions(); // FIXME: is this really needed?

	// Mark all accepting state in a second pass, when
	// dealing with SBA in cosimulation.
	if (Sba && Cosimulation)
	  {
	    tgba_digraph::graph_t& g = res->get_graph();
	    unsigned ns = res->num_states();
	    for (unsigned s = 0; s < ns; ++s)
	      {
		bdd acc = accst[s];
		if (acc == bddfalse)
		  continue;
		for (auto& t: g.out(s))
		  t.acc = acc;
	      }
	  }

	delete gb;
        res_is_deterministic = nb_minato == nb_satoneset;

	return res;
      }


      // Debug:
      // In a first time, print the signature, and the print a list
      // of each state in this partition.
      // In a second time, print foreach state, who is where,
      // where is the new class name.
      void print_partition()
      {
	for (auto& p: bdd_lstate_)
          {
            std::cerr << "partition: "
                      << bdd_format_isop(a_->get_dict(), p.first)
                      << std::endl;
            for (auto s: p.second)
	      std::cerr << "  - "
			<< a_->format_state(a_->state_from_number(s))
			<< '\n';
          }

	std::cerr << "\nPrevious iteration\n" << std::endl;

	unsigned ps = previous_class_.size();
	for (unsigned p = 0; p < ps; ++p)
          {
            std::cerr << a_->format_state(a_->state_from_number(p))
                      << " was in "
                      << bdd_format_set(a_->get_dict(), previous_class_[p])
                      << '\n';
          }
      }

    protected:
      // The automaton which is simulated.
      tgba_digraph* a_;
      tgba_digraph* old_a_;

      // Relation is aimed to represent the same thing than
      // rel_. The difference is in the way it does.
      // If A => A /\ A => B, rel will be (!A U B), but relation_
      // will have A /\ B at the key A. This trick is due to a problem
      // with the computation of the resulting automaton with the signature.
      // rel_ will pollute the meaning of the signature.
      map_bdd_bdd relation_;

      // Represent the class of each state at the previous iteration.
      vector_state_bdd previous_class_;

      // The list of state for each class at the current_iteration.
      // Computed in `update_sig'.
      map_bdd_lstate bdd_lstate_;

      // The queue of free bdd. They will be used as the identifier
      // for the class.
      std::queue<int> free_var_;

      // The list of used bdd. They are in used as identifier for class.
      std::list<bdd> used_var_;

      // Size of the automaton.
      unsigned int size_a_;

      // Used to know when there is no evolution in the po. Updated
      // in the `update_po' method.
      unsigned int po_size_;

      // All the class variable:
      bdd all_class_var_;

      // The flag to say if the outgoing state is initial or not
      bdd bdd_initial;

      bdd all_proms_;

      automaton_size stat;

      scc_map* scc_map_;
      std::vector<const state*> new_original_;

      const map_constraint* map_cst_;

      const tgba* original_;

      bdd all_acceptance_conditions_;

      bool res_is_deterministic;
    };

    // For now, we don't try to handle cosimulation.
    class direct_simulation_dont_care: public direct_simulation<false, false>
    {
      typedef std::vector<std::list<constraint> > constraints;
      typedef std::map<bdd,                  // Source Class.
                       std::map<bdd,         // Destination (implied) Class.
                                std::list<constraint>, // Constraints list.
                                bdd_less_than>,
                       bdd_less_than> constraint_list;
      typedef std::list<std::pair<bdd, bdd> > list_bdd_bdd;


    public:
      direct_simulation_dont_care(const tgba* t)
      : direct_simulation<false, false>(t)
      {
        // This variable is used in the new signature.
        on_cycle_ =
          bdd_ithvar(a_->get_dict()->register_anonymous_variables(1, this));

        // This one is used for the iteration on all the
        // possibilities. Avoid computing two times "no constraints".
        empty_seen_ = false;


        // If this variable is set to true, we have a number limit of
        // simulation to run.
        has_limit_ = false;

	notap = (bdd_support(all_acceptance_conditions_)
                 & all_class_var_ & on_cycle_);
      }

      // This function computes the don't care signature of the state
      // src. This signature is similar to the classic one, excepts
      // that if the transition is on a SCC, we add a on_cycle_ on it,
      // otherwise we add !on_cycle_. This allows us to split the
      // signature later.
      bdd dont_care_compute_sig(unsigned src)
      {
        bdd res = bddfalse;

        unsigned scc = scc_map_->scc_of_state(old_a_->state_from_number(src));
        bool sccacc = scc_map_->accepting(scc);

	for (auto& t: a_->get_graph().out(src))
          {
            bdd cl = previous_class_[t.dst];
            bdd acc;

            if (scc != scc_map_->scc_of_state(old_a_->state_from_number(t.dst)))
              acc = !on_cycle_;
            else if (sccacc)
              acc = on_cycle_ & t.acc;
            else
              acc = on_cycle_ & all_proms_;

            bdd to_add = acc & t.cond & relation_[cl];
            res |= to_add;
          }
        return res;
      }

      // We used to have
      //   sig(s1) = (f1 | g1)
      //   sig(s2) = (f2 | g2)
      // and we say that s2 simulates s1 if sig(s1)=>sig(s2).
      // This amount to testing whether (f1|g1)=>(f2|g2),
      // which is equivalent to testing both
      //    f1=>(f2|g2)  and g1=>(f2|g2)
      // separately.
      //
      // Now we have a slightly improved version of this rule.
      // g1 and g2 are not on cycle, so they can make as many
      // promises as we wish, if that helps.  Adding promises
      // to g2 will not help, but adding promises to g1 can.
      //
      // So we test whether
      //    f1=>(f2|g2)
      //    g1=>noprom(f2|g2)
      // Where noprom(f2|g2) removes all promises from f2|g2.
      // (g1 do not have promises, and neither do g2).

      bool could_imply_aux(bdd f1, bdd g1, bdd left_class,
			   bdd right, bdd right_class)
      {
        (void) left_class;
        (void) right_class;

        bdd f2g2 = bdd_exist(right, on_cycle_);
        bdd f2g2n = bdd_exist(f2g2, all_proms_);

	bdd both = left_class & right_class;
	int lc = bdd_var(left_class);
        f1 = bdd_compose(f1, both, lc);
        g1 = bdd_compose(g1, both, lc);
        f2g2 = bdd_compose(f2g2, both, lc);
        f2g2n = bdd_compose(f2g2n, both, lc);

        return bdd_implies(f1, f2g2) && bdd_implies(g1, f2g2n);
      }

      bool could_imply(bdd left, bdd left_class,
		       bdd right, bdd right_class)
      {
	bdd f1 = bdd_relprod(left, on_cycle_, on_cycle_);
	bdd g1 = bdd_relprod(left, !on_cycle_, on_cycle_);

        //bdd f1 = bdd_restrict(left, on_cycle_);
        //bdd g1 = bdd_restrict(left, !on_cycle_);
	return could_imply_aux(f1, g1, left_class,
			       right, right_class);
      }

      void dont_care_update_po(const list_bdd_bdd& now_to_next,
                               map_bdd_bdd& relation)
      {
        // This loop follows the pattern given by the paper.
        // foreach class do
        // |  foreach class do
        // |  | update po if needed
        // |  od
        // od

        for (list_bdd_bdd::const_iterator it1 = now_to_next.begin();
             it1 != now_to_next.end();
             ++it1)
          {
            bdd accu = it1->second;

	    bdd f1 = bdd_relprod(it1->first, on_cycle_, on_cycle_);
	    bdd g1 = bdd_relprod(it1->first, !on_cycle_, on_cycle_);

            // bdd f1 = bdd_restrict(it1->first_, on_cycle_);
            // bdd g1 = bdd_restrict(it1->first_, !on_cycle_);

            for (list_bdd_bdd::const_iterator it2 = now_to_next.begin();
                 it2 != now_to_next.end();
                 ++it2)
              {
                // Skip the case managed by the initialization of accu.
                if (it1 == it2)
                  continue;

		if (could_imply_aux(f1, g1, it1->second,
				    it2->first, it2->second))
                  {
                    accu &= it2->second;
                    ++po_size_;
                  }
              }
            relation[it1->second] = accu;
          }
      }

#define ISOP(bdd) #bdd" - " << bdd_format_isop(a_->get_dict(), bdd)

      inline bool is_out_scc(bdd b)
      {
	return bddfalse !=  bdd_relprod(b, !on_cycle_, on_cycle_);
        // return bddfalse != bdd_restrict(b, !on_cycle_);
      }

      // This method solves three kind of problems, where we have two
      // conjunctions of variable (that corresponds to a particular
      // transition), and where left could imply right.
      // Three cases:
      //   - αP₁ ⇒ xβP₁ where x is unknown.
      //   - xβP₁ ⇒ αP₁ where x is unknown.
      //   - xαP₁ ⇒ yβP₁ where x, y are unknown.
      void create_simple_constraint(bdd left, bdd right,
                                    unsigned src_left,
                                    unsigned src_right,
                                    std::list<constraint>& constraint)
      {
	assert(src_left != src_right);
        // Determine which is the current case.
        bool out_scc_left = is_out_scc(left);
        bool out_scc_right = is_out_scc(right);
        bdd dest_class = bdd_existcomp(left, all_class_var_);
        assert(revert_relation_.find(dest_class) != revert_relation_.end());
        unsigned dst_left = revert_relation_[dest_class];
        dest_class = bdd_existcomp(right, all_class_var_);
        unsigned dst_right = revert_relation_[dest_class];

	assert(src_left != dst_left || src_right != dst_right);

        left = bdd_exist(left, all_class_var_ & on_cycle_);
        right = bdd_exist(right, all_class_var_ & on_cycle_);

        if (!out_scc_left && out_scc_right)
          {
            bdd b = bdd_exist(right, notap);
            bdd add = bdd_exist(left & b, bdd_support(b));

            if (add != bddfalse
                && bdd_exist(add, all_acceptance_conditions_) == bddtrue)
              {
		assert(src_right != dst_right);

                constraint.emplace_back(new_original_[src_right],
					new_original_[dst_right],
					add);
              }
          }
        else if (out_scc_left && !out_scc_right)
          {
            bdd b = bdd_exist(left, notap);
            bdd add = bdd_exist(right & b, bdd_support(b));

            if (add != bddfalse
                && bdd_exist(add, all_acceptance_conditions_) == bddtrue)
              {
		assert(src_left != dst_left);

                constraint.emplace_back(new_original_[src_left],
					new_original_[dst_left],
					add);
              }
          }
        else if (out_scc_left && out_scc_right)
          {
            bdd b = bdd_exist(left, notap);
            bdd add = bdd_exist(right & b, bdd_support(b));

            if (add != bddfalse
                && bdd_exist(add, all_acceptance_conditions_) == bddtrue)
              {
		assert(src_left != dst_left && src_right != dst_right);
		// FIXME: cas pas compris.
                constraint.emplace_back(new_original_[src_left],
					new_original_[dst_left],
					add);
		constraint.emplace_back(new_original_[src_right],
					new_original_[dst_right],
					add);
              }

          }
        else
          assert(0);
      }


      // This function run over the signatures, and select the
      // transitions that are out of a SCC and call the function
      // create_simple_constraint to solve the problem.

      // NOTE: Currently, this may not be the most accurate method,
      // because we check for equality in the destination part of the
      // signature. We may just check the destination that can be
      // implied instead.
      std::list<constraint> create_new_constraint(unsigned left,
                                                  unsigned right,
                                                  vector_state_bdd& state2sig)
      {
	bdd pcl = previous_class_[left];
	bdd pcr = previous_class_[right];

        bdd sigl = state2sig[left];
        bdd sigr = state2sig[right];

        std::list<constraint> res;

	bdd ex = all_class_var_ & on_cycle_;

	bdd both = pcl & pcr;
	int lc = bdd_var(pcl);
#define DEST(x) bdd_compose(bdd_existcomp(x, ex), both, lc)

        // Key is destination class, value is the signature part that
        // led to this destination class.
	map_bdd_bdd sigl_map;
	{
	  minato_isop isop(sigl & on_cycle_);
	  bdd cond_acc_dest;
	  while ((cond_acc_dest = isop.next()) != bddfalse)
	    sigl_map[DEST(cond_acc_dest)]
	      |= cond_acc_dest;
	}
	{
	  minato_isop isop(sigl & !on_cycle_);
	  bdd cond_acc_dest;
	  while ((cond_acc_dest = isop.next()) != bddfalse)
	    sigl_map[DEST(cond_acc_dest)]
	      |= cond_acc_dest;
	}
        map_bdd_bdd sigr_map;
	{
	  minato_isop isop2(sigr & on_cycle_);
	  bdd cond_acc_dest2;
	  while ((cond_acc_dest2 = isop2.next()) != bddfalse)
	    sigr_map[DEST(cond_acc_dest2)]
	      |= cond_acc_dest2;
	}
	{
	  minato_isop isop2(sigr & !on_cycle_);
	  bdd cond_acc_dest2;
	  while ((cond_acc_dest2 = isop2.next()) != bddfalse)
	    sigr_map[DEST(cond_acc_dest2)]
	      |= cond_acc_dest2;
	}

        // Iterate over the transitions of both states.
        for (auto lp: sigl_map)
	  for (auto rp: sigr_map)
	    // And create constraints if any of the transitions
	    // is out of the SCC and the left could imply the right.
	    if ((is_out_scc(lp.second) || is_out_scc(rp.second))
		&& (bdd_exist(lp.first, on_cycle_) ==
		    bdd_exist(rp.first, on_cycle_)))
	      create_simple_constraint(lp.second, rp.second,
				       left, right, res);
        return res;
      }

      inline automaton_size get_stat() const
      {
        return min_size_;
      }

      tgba_digraph* run()
      {
        // Iterate the simulation until the end. We just don't return
        // an automaton. This allows us to get all the information
        // about the states and their signature.
        main_loop();

        // Compute the don't care signatures,
        map_bdd_lstate dont_care_bdd_lstate;
        // Useful to keep track of who is who.
        vector_state_bdd dont_care_state2sig(size_a_);
        vector_state_bdd state2sig(size_a_);

        list_bdd_bdd dont_care_now_to_now;
        map_bdd_state class2state;
        list_bdd_bdd now_to_now;
        bdd_lstate_.clear();

        // Compute the don't care signature for all the states.
	for (unsigned s = 0; s < size_a_; ++s)
          {
	    bdd clas = previous_class_[s];
            bdd sig = dont_care_compute_sig(s);
            dont_care_bdd_lstate[sig].push_back(s);
            dont_care_state2sig[s] = sig;
            dont_care_now_to_now.emplace_back(sig, clas);
            class2state[clas] = s;

            sig = compute_sig(s);
            bdd_lstate_[sig].push_back(s);
            state2sig[s] = sig;
            now_to_now.push_back(std::make_pair(sig, clas));
          }

        map_bdd_bdd dont_care_relation;
        map_bdd_bdd relation;
        update_po(now_to_now, relation);
        dont_care_update_po(dont_care_now_to_now, dont_care_relation);

        constraint_list cc;

        for (auto p: relation)
	  revert_relation_[p.second] = class2state[p.first];

        int number_constraints = 0;
        relation_ = relation;


        // make the diff between the two tables: imply and
        // could_imply.
	for (unsigned s = 0; s < size_a_; ++s)
          {
            bdd clas = previous_class_[s];
            assert(relation.find(clas) != relation.end());
            assert(dont_care_relation.find(clas) != dont_care_relation.end());

            bdd care_rel = relation[clas];
            bdd dont_care_rel = dont_care_relation[clas];

            if (care_rel == dont_care_rel)
              continue;

            // If they are different we necessarily have
	    // dont_care_rel == care_rel & diff
            bdd diff = bdd_exist(dont_care_rel, care_rel);
	    assert(dont_care_rel == (care_rel & diff));
	    assert(diff != bddtrue);

	    do
              {
                bdd cur_diff = bdd_ithvar(bdd_var(diff));
                cc[clas][cur_diff]
                  = create_new_constraint(s,
                                          class2state[cur_diff],
                                          dont_care_state2sig);
                ++number_constraints;
                diff = bdd_high(diff);
              }
	    while (diff != bddtrue);
          }
#ifndef NDEBUG
	for (auto& i: class2state)
	  assert(previous_class_[i.second] == i.first);
#endif

        tgba_digraph* min = 0;

        map_constraint cstr;

        if (has_limit_)
          rec(cc, cstr, &min, limit_);
        else
          rec(cc, cstr, &min);

        return min;
      }

#define ERASE(inner_map, bigger_map, it)        \
      inner_map.erase(it);                      \
      if (inner_map.empty())                    \
        bigger_map.erase(bigger_map.begin())

      // Add and erase.
      void add_to_map_imply(constraint_list& constraints,
                            map_constraint& cstr)
      {
        constraint_list::iterator it = constraints.begin();
        std::map<bdd,
                 std::list<constraint>,
                 bdd_less_than>::iterator it2 = it->second.begin();

        add_to_map(it2->second, cstr);

        bdd implied_list = relation_[it2->first]; // it2->first:
                                                  // destination class.

        ERASE(it->second, constraints, it2);
        if (constraints.empty())
          return;
        it = constraints.begin();
        // At worst, implied_list is equal to it2->first.
        while (implied_list != bddtrue)
          {
            bdd cur_implied = bdd_ithvar(bdd_var(implied_list));

            std::map<bdd,
                     std::list<constraint>,
                     bdd_less_than>::iterator tmp
              = it->second.find(cur_implied);
            if (tmp != it->second.end())
              {
                add_to_map(tmp->second, cstr);
                ERASE(it->second, constraints, tmp);
                if (constraints.empty())
                  return;
              }

            implied_list = bdd_high(implied_list);
          }
      }

      // Compute recursively all the combinations.
      void rec(constraint_list constraints,
               map_constraint cstr,
               tgba_digraph** min,
               int max_depth = std::numeric_limits<int>::max())
      {
        assert(max_depth > 0);
        while (!constraints.empty())
          {
            if (!--max_depth)
                break;
            add_to_map_imply(constraints, cstr);
            rec(constraints, cstr, min, max_depth);
          }

        if (empty_seen_ && cstr.empty())
          return;
        else if (cstr.empty())
          empty_seen_ = true;

        direct_simulation<false, false> dir_sim(original_, &cstr);
        tgba_digraph* tmp = dir_sim.run();
        automaton_size cur_size = dir_sim.get_stat();
        if (*min == 0 || min_size_ > cur_size)
          {
            delete *min;
            *min = tmp;
            min_size_ = cur_size;
            res_is_deterministic = dir_sim.result_is_deterministic();
          }
        else
          {
            delete tmp;
          }
      }

      void set_limit(int n)
      {
        has_limit_ = true;
        limit_ = n;
      }

    private:
      // This bdd is used to differentiate parts of the signature that
      // are in a SCC and those that are not.
      bdd on_cycle_;

      map_bdd_bdd dont_care_relation_;

      map_bdd_state revert_relation_;

      automaton_size min_size_;

      bool empty_seen_;

      bool has_limit_;
      int limit_;

      bdd notap;
    };


  } // End namespace anonymous.


  tgba*
  simulation(const tgba* t)
  {
    direct_simulation<false, false> simul(t);
    return simul.run();
  }

  tgba*
  simulation_sba(const tgba* t)
  {
    direct_simulation<false, true> simul(t);
    return simul.run();
  }

  tgba*
  cosimulation(const tgba* t)
  {
    direct_simulation<true, false> simul(t);
    return simul.run();
  }

  tgba*
  cosimulation_sba(const tgba* t)
  {
    direct_simulation<true, true> simul(t);
    return simul.run();
  }


  template<bool Sba>
  tgba*
  iterated_simulations_(const tgba* t)
  {
    tgba* res = const_cast<tgba*> (t);
    automaton_size prev;
    automaton_size next;

    do
      {
        prev = next;
        direct_simulation<false, Sba> simul(res);
        tgba_digraph* after_simulation = simul.run();

        if (res != t)
          delete res;

        if (simul.result_is_deterministic())
          {
            res = after_simulation;
            break;
          }

        direct_simulation<true, Sba> cosimul(after_simulation);
	tgba_digraph* after_cosimulation = cosimul.run();
        next = cosimul.get_stat();
	delete after_simulation;

	if (Sba)
	  res = scc_filter_states(after_cosimulation);
	else
	  res = scc_filter(after_cosimulation, false);
	delete after_cosimulation;
      }
    while (prev != next);
    return res;
  }

  tgba*
  iterated_simulations(const tgba* t)
  {
    return iterated_simulations_<false>(t);
  }

  tgba*
  iterated_simulations_sba(const tgba* t)
  {
    return iterated_simulations_<true>(t);
  }

  tgba*
  dont_care_simulation(const tgba* t, int limit)
  {
    direct_simulation<false, false> sim(t);
    tgba* tmp = sim.run();

    direct_simulation_dont_care s(tmp);
    if (limit > 0)
      s.set_limit(limit);

    tgba* res = s.run();
    delete tmp;

    return res;
  }


  tgba*
  dont_care_iterated_simulations(const tgba* t, int limit)
  {
    tgba* res = const_cast<tgba*> (t);
    automaton_size prev;
    automaton_size next;

    do
      {
        prev = next;

	tgba* after_simulation = dont_care_simulation(res, limit);

        if (res != t)
          delete res;

        direct_simulation<true, false> cosimul(after_simulation);
	tgba* after_cosimulation = cosimul.run();
	delete after_simulation;

        next = cosimul.get_stat();
        res = scc_filter(after_cosimulation, true);
	delete after_cosimulation;
      }
    while (prev != next);

    return res;
  }

} // End namespace spot.
