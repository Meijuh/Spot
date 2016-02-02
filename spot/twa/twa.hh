// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2011, 2013, 2014, 2015, 2016 Laboratoire de
// Recherche et Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004, 2005 Laboratoire d'Informatique de
// Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
// Université Pierre et Marie Curie.
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

#include <spot/twa/fwd.hh>
#include <spot/twa/acc.hh>
#include <spot/twa/bdddict.hh>
#include <cassert>
#include <memory>
#include <unordered_map>
#include <functional>
#include <array>
#include <vector>
#include <spot/misc/casts.hh>
#include <spot/misc/hash.hh>
#include <spot/tl/formula.hh>
#include <spot/misc/trival.hh>

namespace spot
{
  /// \ingroup twa_essentials
  /// \brief Abstract class for states.
  class SPOT_API state
  {
  public:
    /// \brief Compares two states (that come from the same automaton).
    ///
    /// This method returns an integer less than, equal to, or greater
    /// than zero if \a this is found, respectively, to be less than, equal
    /// to, or greater than \a other according to some implicit total order.
    ///
    /// This method should not be called to compare states from
    /// different automata.
    ///
    /// \sa spot::state_ptr_less_than
    virtual int compare(const state* other) const = 0;

    /// \brief Hash a state.
    ///
    /// This method returns an integer that can be used as a
    /// hash value for this state.
    ///
    /// Note that the hash value is guaranteed to be unique for all
    /// equal states (in compare()'s sense) for only has long has one
    /// of these states exists.  So it's OK to use a spot::state as a
    /// key in a \c hash_map because the mere use of the state as a
    /// key in the hash will ensure the state continues to exist.
    ///
    /// However if you create the state, get its hash key, delete the
    /// state, recreate the same state, and get its hash key, you may
    /// obtain two different hash keys if the same state were not
    /// already used elsewhere.  In practice this weird situation can
    /// occur only when the state is BDD-encoded, because BDD numbers
    /// (used to build the hash value) can be reused for other
    /// formulas.  That probably doesn't matter, since the hash value
    /// is meant to be used in a \c hash_map, but it had to be noted.
    virtual size_t hash() const = 0;

    /// Duplicate a state.
    virtual state* clone() const = 0;

    /// \brief Release a state.
    ///
    /// Methods from the tgba or twa_succ_iterator always return a
    /// new state that you should deallocate with this function.
    /// Before Spot 0.7, you had to "delete" your state directly.
    /// Starting with Spot 0.7, you should update your code to use
    /// this function instead. destroy() usually call delete, except
    /// in subclasses that destroy() to allow better memory management
    /// (e.g., no memory allocation for explicit automata).
    virtual void destroy() const
    {
      delete this;
    }

  protected:
    /// \brief Destructor.
    ///
    /// Note that client code should call
    /// \code s->destroy(); \endcode
    /// instead of
    /// \code delete s; \endcode .
    virtual ~state()
    {
    }
  };

  /// \ingroup twa_essentials
  /// \brief Strict Weak Ordering for \c state*.
  ///
  /// This is meant to be used as a comparison functor for
  /// STL \c map whose key are of type \c state*.
  ///
  /// For instance here is how one could declare
  /// a map of \c state*.
  /// \code
  ///   // Remember how many times each state has been visited.
  ///   std::map<spot::state*, int, spot::state_ptr_less_than> seen;
  /// \endcode
  struct state_ptr_less_than
  {
    bool
    operator()(const state* left, const state* right) const
    {
      assert(left);
      return left->compare(right) < 0;
    }
  };

  /// \ingroup twa_essentials
  /// \brief An Equivalence Relation for \c state*.
  ///
  /// This is meant to be used as a comparison functor for
  /// an \c unordered_map whose key are of type \c state*.
  ///
  /// For instance here is how one could declare
  /// a map of \c state*.
  /// \code
  ///   // Remember how many times each state has been visited.
  ///   std::unordered_map<spot::state*, int, spot::state_ptr_hash,
  ///                                    spot::state_ptr_equal> seen;
  /// \endcode
  struct state_ptr_equal
  {
    bool
    operator()(const state* left, const state* right) const
    {
      assert(left);
      return 0 == left->compare(right);
    }
  };

  /// \ingroup twa_essentials
  /// \ingroup hash_funcs
  /// \brief Hash Function for \c state*.
  ///
  /// This is meant to be used as a hash functor for
  /// an \c unordered_map whose key are of type \c state*.
  ///
  /// For instance here is how one could declare
  /// a map of \c state*.
  /// \code
  ///   // Remember how many times each state has been visited.
  ///   std::unordered_map<spot::state*, int, spot::state_ptr_hash,
  ///                                    spot::state_ptr_equal> seen;
  /// \endcode
  struct state_ptr_hash
  {
    size_t
    operator()(const state* that) const
    {
      assert(that);
      return that->hash();
    }
  };

  /// \brief Unordered set of abstract states
  ///
  /// Destroying each state if needed is the user's responsibility.
  ///
  /// \see state_unicity_table
  typedef std::unordered_set<const state*,
			     state_ptr_hash, state_ptr_equal> state_set;

  /// \brief Unordered map of abstract states
  ///
  /// Destroying each state if needed is the user's responsibility.
  template<class val>
  using state_map = std::unordered_map<const state*, val,
				       state_ptr_hash, state_ptr_equal>;

  /// \ingroup twa_essentials
  /// \brief Render state pointers unique via a hash table.
  class SPOT_API state_unicity_table
  {
    state_set m;
  public:

    /// \brief Canonicalize state pointer.
    ///
    /// If this is the first time a state is seen, this return the
    /// state pointer as-is, otherwise it frees the state and returns
    /// a point to the previously seen copy.
    ///
    /// States are owned by the table and will be freed on
    /// destruction.
    const state* operator()(const state* s)
    {
      auto p = m.insert(s);
      if (!p.second)
	s->destroy();
      return *p.first;
    }

    /// \brief Canonicalize state pointer.
    ///
    /// Same as operator(), except that a nullptr
    /// is returned if the state is not new.
    const state* is_new(const state* s)
    {
      auto p = m.insert(s);
      if (!p.second)
	{
	  s->destroy();
	  return nullptr;
	}
      return *p.first;
    }

    ~state_unicity_table()
    {
      for (state_set::iterator i = m.begin(); i != m.end();)
	{
	  // Advance the iterator before destroying its key.  This
	  // avoid issues with old g++ implementations.
	  state_set::iterator old = i++;
	  (*old)->destroy();
	}
    }

    size_t
    size()
    {
      return m.size();
    }
  };



  // Functions related to shared_ptr.
  //////////////////////////////////////////////////

  typedef std::shared_ptr<const state> shared_state;

  inline void shared_state_deleter(state* s) { s->destroy(); }

  /// \ingroup twa_essentials
  /// \brief Strict Weak Ordering for \c shared_state
  /// (shared_ptr<const state*>).
  ///
  /// This is meant to be used as a comparison functor for
  /// STL \c map whose key are of type \c shared_state.
  ///
  /// For instance here is how one could declare
  /// a map of \c shared_state.
  /// \code
  ///   // Remember how many times each state has been visited.
  ///   std::map<shared_state, int, spot::state_shared_ptr_less_than> seen;
  /// \endcode
  struct state_shared_ptr_less_than
  {
    bool
    operator()(shared_state left,
               shared_state right) const
    {
      assert(left);
      return left->compare(right.get()) < 0;
    }
  };

  /// \ingroup twa_essentials
  /// \brief An Equivalence Relation for \c shared_state
  /// (shared_ptr<const state*>).
  ///
  /// This is meant to be used as a comparison functor for
  /// an \c unordered_map whose key are of type \c shared_state.
  ///
  /// For instance here is how one could declare
  /// a map of \c shared_state
  /// \code
  ///   // Remember how many times each state has been visited.
  ///   std::unordered_map<shared_state, int,
  ///                      state_shared_ptr_hash,
  ///                      state_shared_ptr_equal> seen;
  /// \endcode
  ///
  /// \see shared_state_set
  struct state_shared_ptr_equal
  {
    bool
    operator()(shared_state left,
               shared_state right) const
    {
      assert(left);
      return 0 == left->compare(right.get());
    }
  };

  /// \ingroup twa_essentials
  /// \ingroup hash_funcs
  /// \brief Hash Function for \c shared_state (shared_ptr<const state*>).
  ///
  /// This is meant to be used as a hash functor for
  /// an \c unordered_map whose key are of type
  /// \c shared_state.
  ///
  /// For instance here is how one could declare
  /// a map of \c shared_state.
  /// \code
  ///   // Remember how many times each state has been visited.
  ///   std::unordered_map<shared_state, int,
  ///                      state_shared_ptr_hash,
  ///                      state_shared_ptr_equal> seen;
  /// \endcode
  ///
  /// \see shared_state_set
  struct state_shared_ptr_hash
  {
    size_t
    operator()(shared_state that) const
    {
      assert(that);
      return that->hash();
    }
  };

  /// Unordered set of shared states
  typedef std::unordered_set<shared_state,
			     state_shared_ptr_hash,
			     state_shared_ptr_equal> shared_state_set;

  /// \ingroup twa_essentials
  /// \brief Iterate over the successors of a state.
  ///
  /// This class provides the basic functionalities required to
  /// iterate over the successors of a state, as well as querying
  /// transition labels.  Because transitions are never explicitely
  /// encoded, labels (conditions and acceptance conditions) can only
  /// be queried while iterating over the successors.
  class SPOT_API twa_succ_iterator
  {
  public:
    virtual
    ~twa_succ_iterator()
    {
    }

    /// \name Iteration
    //@{

    /// \brief Position the iterator on the first successor (if any).
    ///
    /// This method can be called several times to make multiple
    /// passes over successors.
    ///
    /// \warning One should always call \c done() (or better: check
    /// the return value of first()) to ensure there is a successor,
    /// even after \c first().  A common trap is to assume that there
    /// is at least one successor: this is wrong.
    ///
    /// \return whether there is actually a successor
    virtual bool first() = 0;

    /// \brief Jump to the next successor (if any).
    ///
    /// \warning Again, one should always call \c done() (or better:
    /// check the return value of next()) ensure there is a successor.
    ///
    /// \return whether there is actually a successor
    virtual bool next() = 0;

    /// \brief Check whether the iteration is finished.
    ///
    /// This function should be called after any call to \c first()
    /// or \c next() and before any enquiry about the current state.
    ///
    /// The usual way to do this is with a \c for loop.
    ///
    ///     for (s->first(); !s->done(); s->next())
    ///       ...
    virtual bool done() const = 0;

    //@}

    /// \name Inspection
    //@{

    /// \brief Get the state of the current successor.
    ///
    /// Note that the same state may occur at different points
    /// in the iteration.  These actually correspond to the same
    /// destination.  It just means there were several transitions,
    /// with different conditions, leading to the same state.
    ///
    /// The returned state should be destroyed (see state::destroy)
    /// by the caller after it is no longer used.
    virtual const state* dst() const = 0;
    /// \brief Get the condition on the transition leading to this successor.
    ///
    /// This is a boolean function of atomic propositions.
    virtual bdd cond() const = 0;
    /// \brief Get the acceptance conditions on the transition leading
    /// to this successor.
    virtual acc_cond::mark_t acc() const = 0;

    //@}
  };

  namespace internal
  {
    /// \brief Helper structure to iterate over the successor of a
    /// state using the on-the-flay interface.
    ///
    /// This one emulates an STL-like iterator over the
    /// twa_succ_iterator interface.
    struct SPOT_API succ_iterator
    {
    protected:
      twa_succ_iterator* it_;
    public:

      succ_iterator(twa_succ_iterator* it):
	it_(it)
      {
      }

      bool operator==(succ_iterator o) const
      {
	return it_ == o.it_;
      }

      bool operator!=(succ_iterator o) const
      {
	return it_ != o.it_;
      }

      const twa_succ_iterator* operator*() const
      {
	return it_;
      }

      void operator++()
      {
	if (!it_->next())
	  it_ = nullptr;
      }
    };
  }

  /// \defgroup twa TωA (Transition-based ω-Automata)
  ///
  /// Spot is centered around the spot::twa type.  This type and its
  /// cousins are listed \ref twa_essentials "here".  This is an
  /// abstract interface.  Its implementations are either \ref
  /// twa_representation "concrete representations", or \ref
  /// twa_on_the_fly_algorithms "on-the-fly algorithms".  Other
  /// algorithms that work on spot::twa are \ref twa_algorithms
  /// "listed separately".

  /// \addtogroup twa_essentials Essential TωA types
  /// \ingroup twa

  /// \ingroup twa_essentials
  /// \brief A Transition-based ω-Automaton.
  ///
  /// The acronym TωA stands for Transition-based ω-automaton.
  /// We may write it as TwA or twa, but never as TWA as the
  /// w is just a non-utf8 replacement for ω that should not be
  /// capitalized.
  ///
  /// TωAs are transition-based automata, meanings that not-only
  /// do they have labels on arcs, they also have an acceptance
  /// condition defined in term of sets of transitions.
  /// The acceptance condition can be anything supported by
  /// the HOA format (http://adl.github.io/hoaf/).  The only
  /// restriction w.r.t. the format is that this class does
  /// not support alternating automata
  ///
  /// Previous versions of Spot supported a type of automata called
  /// TGBA, which are TωA in which the acceptance condition is a set
  /// of sets of transitions that must be intersected infinitely
  /// often.
  ///
  /// In this version, TGBAs are now represented by TωAs for which
  /// <code>aut->acc().is_generalized_buchi())</code> returns true.
  ///
  /// Browsing such automaton can be achieved using two functions:
  /// \c get_init_state, and \c succ.  The former returns
  /// the initial state while the latter lists the
  /// successor states of any state.
  ///
  /// Note that although this is a transition-based automata, we never
  /// represent transitions in the API!  Transition data are
  /// obtained by querying the iterator over the successors of a
  /// state.
  class SPOT_API twa: public std::enable_shared_from_this<twa>
  {
  protected:
    twa(const bdd_dict_ptr& d);
    /// Any iterator returned via release_iter.
    mutable twa_succ_iterator* iter_cache_;
    /// BDD dictionary used by the automaton.
    bdd_dict_ptr dict_;
  public:

#ifndef SWIG
    /// \brief Helper class to iterate over the successor of a state
    /// using the on-the-fly interface
    ///
    /// This one emulates an STL-like container with begin()/end()
    /// methods so that it can be iterated using a ranged-for.
    class succ_iterable
    {
    protected:
      const twa* aut_;
      twa_succ_iterator* it_;
    public:
      succ_iterable(const twa* aut, twa_succ_iterator* it)
	: aut_(aut), it_(it)
      {
      }

      succ_iterable(succ_iterable&& other)
	: aut_(other.aut_), it_(other.it_)
      {
	other.it_ = nullptr;
      }

      ~succ_iterable()
      {
	if (it_)
	  aut_->release_iter(it_);
      }

      internal::succ_iterator begin()
      {
	return it_->first() ? it_ : nullptr;
      }

      internal::succ_iterator end()
      {
	return nullptr;
      }
    };
#endif

    virtual ~twa();

    /// \brief Get the initial state of the automaton.
    ///
    /// The state has been allocated with \c new.  It is the
    /// responsability of the caller to \c destroy it when no
    /// longer needed.
    virtual const state* get_init_state() const = 0;

    /// \brief Get an iterator over the successors of \a local_state.
    ///
    /// The iterator has been allocated with \c new.  It is the
    /// responsability of the caller to \c delete it when no
    /// longer needed.
    virtual twa_succ_iterator*
    succ_iter(const state* local_state) const = 0;

#ifndef SWIG
    /// \brief Build an iterable over the successors of \a s.
    ///
    /// This is meant to be used as
    /// \code
    /// for (auto i: aut->succ(s))
    ///   {
    ///     /* i->dst() */
    ///   }
    /// \endcode
    succ_iterable
    succ(const state* s) const
    {
      return {this, succ_iter(s)};
    }
#endif

    /// \brief Release an iterator after usage.
    ///
    /// This iterator can then be reused by succ_iter() to avoid
    /// memory allocation.
    void release_iter(twa_succ_iterator* i) const
    {
      if (iter_cache_)
	delete i;
      else
	iter_cache_ = i;
    }

    /// \brief Get a formula that must hold whatever successor is taken.
    ///
    /// \return A formula which must be verified for all successors
    ///  of \a state.
    ///
    /// This can be as simple as \c bddtrue, or more completely
    /// the disjunction of the condition of all successors.  This
    /// is used as an hint by \c succ_iter() to reduce the number
    /// of successor to compute in a product.
    ///
    /// Sub classes should implement compute_support_conditions(),
    /// this function is just a wrapper that will cache the
    /// last return value for efficiency.
    bdd support_conditions(const state* state) const;

    /// \brief Get the dictionary associated to the automaton.
    ///
    /// Atomic propositions and acceptance conditions are represented
    /// as BDDs.  The dictionary allows to map BDD variables back to
    /// formulae, and vice versa.  This is useful when dealing with
    /// several automata (which may use the same BDD variable for
    /// different formula), or simply when printing.
    bdd_dict_ptr get_dict() const
    {
      return dict_;
    }

    /// \brief Register an atomic proposition designated by formula \a ap.
    ///
    /// \return The BDD variable number.
    int register_ap(formula ap)
    {
      int res = dict_->has_registered_proposition(ap, this);
      if (res < 0)
	{
	  aps_.push_back(ap);
	  res = dict_->register_proposition(ap, this);
	  bddaps_ &= bdd_ithvar(res);
	}
      return res;
    }

    /// \brief Register an atomic proposition designated by string \a ap.
    ///
    /// \return The BDD variable number.
    int register_ap(std::string name)
    {
      return register_ap(formula::ap(name));
    }

    /// \brief Get the vector of atomic propositions used by this
    /// automaton.
    const std::vector<formula>&  ap() const
    {
      return aps_;
    }

    /// The list of atomic propositions as a conjunction.
    bdd ap_var() const
    {
      return bddaps_;
    }

    /// \brief Format the state as a string for printing.
    ///
    /// This formating is the responsability of the automata
    /// that owns the state.
    virtual std::string format_state(const state* state) const = 0;

    /// \brief Return a possible annotation for the transition
    /// pointed to by the iterator.
    ///
    /// You may decide to use annotations when building a tgba class
    /// that represents the state space of a model, for instance to
    /// indicate how the tgba transitions relate to the original model
    /// (e.g. the annotation could be the name of a PetriNet
    /// transition, or the line number of some textual formalism).
    ///
    /// Implementing this method is optional; the default annotation
    /// is the empty string.
    ///
    /// This method is used for instance in print_dot(),
    /// and replay_twa_run().
    ///
    /// \param t a non-done twa_succ_iterator for this automaton
    virtual std::string
    transition_annotation(const twa_succ_iterator* t) const;

    /// \brief Project a state on an automaton.
    ///
    /// This converts \a s, into that corresponding spot::state for \a
    /// t.  This is useful when you have the state of a product, and
    /// want restrict this state to a specific automata occuring in
    /// the product.
    ///
    /// It goes without saying that \a s and \a t should be compatible
    /// (i.e., \a s is a state of \a t).
    ///
    /// \return 0 if the projection fails (\a s is unrelated to \a t),
    ///    or a new \c state* (the projected state) that must be
    ///    destroyed by the caller.
    virtual state* project_state(const state* s,
				 const const_twa_ptr& t) const;


    /// The acceptance condition of the automaton.
    /// @{
    const acc_cond& acc() const
    {
      return acc_;
    }

    acc_cond& acc()
    {
      return acc_;
    }
    /// @}

    /// Check whether the language of the automaton is empty.
    virtual bool is_empty() const;

  private:
    acc_cond acc_;

    void set_num_sets_(unsigned num)
    {
      if (num < acc_.num_sets())
	{
	  acc_.~acc_cond();
	  new (&acc_) acc_cond;
	}
      acc_.add_sets(num - acc_.num_sets());
    }

  public:
    /// Number of acceptance sets used by the automaton.
    unsigned num_sets() const
    {
      return acc_.num_sets();
    }

    /// Acceptance formula used by the automaton.
    const acc_cond::acc_code& get_acceptance() const
    {
      return acc_.get_acceptance();
    }

    /// \brief Set the acceptance condition of the automaton.
    ///
    /// \param num the number of acceptance sets used
    /// \param c the acceptance formula
    void set_acceptance(unsigned num, const acc_cond::acc_code& c)
    {
      set_num_sets_(num);
      acc_.set_acceptance(c);
      if (num == 0)
	prop_state_acc(true);
    }

    /// Copy the acceptance condition of another TωA.
    void copy_acceptance_of(const const_twa_ptr& a)
    {
      acc_ = a->acc();
      unsigned num = acc_.num_sets();
      if (num == 0)
	prop_state_acc(true);
    }

    /// Copy the atomic propositions of another TωA
    void copy_ap_of(const const_twa_ptr& a)
    {
      for (auto f: a->ap())
	this->register_ap(f);
    }

    /// \brief Set generalized Büchi acceptance
    ///
    /// \param num the number of acceptance sets to used
    ///
    /// The acceptance formula of the form
    /// \code
    /// Inf(0)&Inf(1)&...&Inf(num-1)
    /// \endcode
    /// is generated.
    ///
    /// In the case where \a num is null, the state-acceptance
    /// property is automatically turned on.
    void set_generalized_buchi(unsigned num)
    {
      set_num_sets_(num);
      acc_.set_generalized_buchi();
      if (num == 0)
	prop_state_acc(true);
    }

    /// \brief Set Büchi acceptance.
    ///
    /// This declares a single acceptance set, and \c Inf(0)
    /// acceptance.  The returned mark \c {0} can be used to tag
    /// accepting transition.
    ///
    /// Note that this does not make the automaton as using
    /// state-based acceptance.  If you want to create a Büchi
    /// automaton with state-based acceptance, call
    /// \code
    /// prop_state_acc(true)
    /// \endcode
    /// in addition.
    ///
    /// \see prop_state_acc
    acc_cond::mark_t set_buchi()
    {
      set_generalized_buchi(1);
      return acc_.mark(0);
    }

  protected:
    /// Do the actual computation of tgba::support_conditions().
    virtual bdd compute_support_conditions(const state* state) const = 0;
    mutable const state* last_support_conditions_input_;
  private:
    mutable bdd last_support_conditions_output_;
    std::vector<formula> aps_;
    bdd bddaps_;

  protected:

    /// Helper structure used to store property flags.
    struct bprop
    {
      trival::repr_t state_based_acc:2;   // State-based acceptance.
      trival::repr_t inherently_weak:2;   // Inherently Weak automaton.
      trival::repr_t weak:2;	       // Weak automaton.
      trival::repr_t terminal:2;	       // Terminal automaton.
      trival::repr_t deterministic:2;     // Deterministic automaton.
      trival::repr_t unambiguous:2;       // Unambiguous automaton.
      trival::repr_t stutter_invariant:2; // Stutter invariant language.
    };
    union
    {
      unsigned props;
      bprop is;
    };

#ifndef SWIG
    // Dynamic properties, are given with a name and a destructor function.
    std::unordered_map<std::string,
		       std::pair<void*,
				 std::function<void(void*)>>> named_prop_;
#endif
    void* get_named_prop_(std::string s) const;

  public:

#ifndef SWIG
    /// \brief Declare a named property
    ///
    /// Arbitrary object can be attached to automata.  Those are called
    /// named properties.  They are used for instance to name all the
    /// state of an automaton.
    ///
    /// This function attaches the object \a val to the current automaton,
    /// under the name \a s.
    ///
    /// When the automaton is destroyed, the \a destructor function will
    /// be called to destroy the attached object.
    void set_named_prop(std::string s,
			void* val, std::function<void(void*)> destructor);

    /// \brief Declare a named property
    ///
    /// Arbitrary object can be attached to automata.  Those are called
    /// named properties.  They are used for instance to name all the
    /// state of an automaton.
    ///
    /// This function attaches the object \a val to the current automaton,
    /// under the name \a s.
    ///
    /// The object will be automatically destroyed when the automaton
    /// is destroyed.
    template<typename T>
    void set_named_prop(std::string s, T* val)
    {
      set_named_prop(s, val, [](void *p) { delete static_cast<T*>(p); });
    }

    /// \brief Retrieve a named property
    ///
    /// Because named property can be object of any type, retrieving
    /// the object requires knowing its type.
    ///
    /// \param s the name of the object to retrieve
    /// \tparam T the type of the object to retrieve
    ///
    /// Note that the return is a pointer to \c T, so the type should
    /// not include the pointer.
    ///
    /// Returns a nullptr if no such named property exists.
    template<typename T>
    T* get_named_prop(std::string s) const
    {
      void* p = get_named_prop_(s);
      if (!p)
	return nullptr;
      return static_cast<T*>(p);
    }
#endif

    /// \brief Destroy all named properties.
    ///
    /// This is used by the automaton destructor, but it could be used
    /// by any algorithm that want to get rid of all named properties.
    void release_named_properties()
    {
      // Destroy all named properties.
      for (auto& np: named_prop_)
	np.second.second(np.second.first);
      named_prop_.clear();
    }

    /// \brief Whether the automaton uses state-based acceptance.
    ///
    /// From the point of view of Spot, this means that all
    /// transitions leaving a state belong to the same acceptance
    /// sets.  Then it is equivalent to pretend that the state is in
    /// the acceptance set.
    trival prop_state_acc() const
    {
      return is.state_based_acc;
    }

    /// \brief Set the state-based-acceptance property.
    ///
    /// If this property is set to true, then all transitions leaving
    /// a state must belong to the same acceptance sets.
    void prop_state_acc(trival val)
    {
      is.state_based_acc = val.val();
    }

    /// \brief Whether this is a state-based Büchi automaton.
    ///
    /// An SBA has a Büchi acceptance, and should have its
    /// state-based acceptance property set.
    trival is_sba() const
    {
      return prop_state_acc() && acc().is_buchi();
    }

    /// \brief Whether the automaton is inherently weak.
    ///
    /// An automaton is inherently weak if accepting cycles and
    /// rejecting cycles are never mixed in the same strongly
    /// connected component.
    ///
    /// \see prop_weak()
    /// \see prop_terminal()
    trival prop_inherently_weak() const
    {
      return is.inherently_weak;
    }

    /// \brief Set the "inherently weak" proeprty.
    ///
    /// Setting "inherently weak" to false automatically
    /// disables "terminal" and "weak".
    ///
    /// \see prop_weak()
    /// \see prop_terminal()
    void prop_inherently_weak(trival val)
    {
      is.inherently_weak = val.val();
      if (!val)
	is.terminal = is.weak = val.val();
    }

    /// \brief Whether the automaton is terminal.
    ///
    /// An automaton is terminal if it is weak, no non-accepting cycle
    /// can be reached from an accepting cycle, and the accepting
    /// strongly components are complete (i.e., any suffix is accepted
    /// as soon as we enter an accepting component).
    ///
    /// \see prop_weak()
    /// \see prop_inherently_weak()
    trival prop_terminal() const
    {
      return is.terminal;
    }

    /// \brief Set the terminal property.
    ///
    /// Marking an automaton as "terminal" automatically marks it as
    /// "weak" and "inherently weak".
    ///
    /// \see prop_weak()
    /// \see prop_inherently_weak()
    void prop_terminal(trival val)
    {
      is.terminal = val.val();
      if (val)
	is.inherently_weak = is.weak = val.val();
    }

    /// \brief Whether the automaton is weak.
    ///
    /// An automaton is weak if inside each strongly connected
    /// component, all transitions belong to the same acceptance sets.
    ///
    /// \see prop_terminal()
    /// \see prop_inherently_weak()
    trival prop_weak() const
    {
      return is.weak;
    }

    /// \brief Set the weak property.
    ///
    /// Marking an automaton as "weak" automatically marks it as
    /// "inherently weak".  Marking an automaton as "not weak"
    /// automatically marks are as "not terminal".
    ///
    /// \see prop_terminal()
    /// \see prop_inherently_weak()
    void prop_weak(trival val)
    {
      is.weak = val.val();
      if (val)
	is.inherently_weak = val.val();
      if (!val)
	is.terminal = val.val();
    }

    /// \brief Whether the automaton is deterministic.
    ///
    /// An automaton is deterministic if the conjunction between the
    /// labels of two transitions leaving a state is always false.
    ///
    /// Note that this method may return trival::maybe() when it is
    /// unknown whether the automaton is deterministic or not.  If you
    /// need a true/false answer, prefer the is_deterministic() function.
    ///
    /// \see prop_unambiguous()
    /// \see is_deterministic()
    trival prop_deterministic() const
    {
      return is.deterministic;
    }

    /// \brief Set the deterministic property.
    ///
    /// Setting the "deterministic" property automatically
    /// sets the "unambiguous" property.
    ///
    /// \see prop_unambiguous()
    void prop_deterministic(trival val)
    {
      is.deterministic = val.val();
      if (val)
	// deterministic implies unambiguous
	is.unambiguous = val.val();
    }

    /// \brief Whether the automaton is unambiguous
    ///
    /// An automaton is unambiguous if any accepted word is recognized
    /// by exactly one accepting path in the automaton.  Any word
    /// (accepted or not) may be recognized by several rejecting paths
    /// in the automaton.
    ///
    /// Note that this method may return trival::maybe() when it is
    /// unknown whether the automaton is unambiguous or not.  If you
    /// need a true/false answer, prefer the is_unambiguous() function.
    ///
    /// \see prop_deterministic()
    /// \see is_unambiguous()
    trival prop_unambiguous() const
    {
      return is.unambiguous;
    }

    /// \brief Sets the unambiguous property
    ///
    /// Marking an automaton as "non unambiguous" automatically
    /// marks it as "non deterministic".
    ///
    /// \see prop_deterministic()
    void prop_unambiguous(trival val)
    {
      is.unambiguous = val.val();
      if (!val)
	is.deterministic = val.val();
    }

    /// \brief Whether the automaton is stutter-invariant.
    ///
    /// An automaton is stutter-invariant iff any accepted word
    /// remains accepted after removing a finite number of duplicate
    /// letters, or after duplicating finite number of letters.
    ///
    /// Note that this method may return trival::maybe() when it is
    /// unknown whether the automaton is stutter-invariant or not.  If
    /// you need a true/false answer, prefer one using of the the
    /// is_stutter_invariant() function.
    ///
    /// \see is_stutter_invariant
    trival prop_stutter_invariant() const
    {
      return is.stutter_invariant;
    }

    /// \brief Set the stutter-invariant property
    void prop_stutter_invariant(trival val)
    {
      is.stutter_invariant = val.val();
    }

    /// \brief A structure for selecting a set of automaton properties
    /// to copy.
    ///
    /// When an algorithm copies an automaton before making some
    /// modification on that automaton, it should use a \c prop_set
    /// structure to indicate which properties should be copied from
    /// the original automaton.
    ///
    /// This structure does not list all supported properties, because
    /// properties are copied by groups of related properties.  For
    /// instance if an algorithm breaks the "inherent_weak"
    /// properties, it usually also breaks the "weak" and "terminal"
    /// properties.
    ///
    /// Set the flags to true to copy the value of the original
    /// property, and to false to ignore the original property
    /// (leaving the property of the new automaton to its default
    /// value, which is trival::maybe()).
    ///
    /// This can be used for instance as:
    /// \code
    ///    aut->prop_copy(other_aut, {true, false, false, true});
    /// \endcode
    /// This would copy the "state-based acceptance" and
    /// "stutter invariant" properties from \c other_aut to \c code.
    ///
    /// The reason there is no default value for these flags is that
    /// whenever we add a new property that do not fall into any of
    /// these groups, we will be forced to review all algorithm to
    /// decide if the property should be preserved or not.
    ///
    /// \see make_twa_graph_ptr
    /// \see prop_copy
    struct prop_set
    {
      bool state_based;		///< preserve state-based acceptnace
      bool inherently_weak;	///< preserve inherently weak, weak, & terminal
      bool deterministic;	///< preserve deterministic and unambiguous
      bool stutter_inv;		///< preserve stutter invariance

      /// \brief An all-true \c prop_set
      ///
      /// Use that only in algorithms that copy an automaton without
      /// performing any modification.
      ///
      /// If an algorithm X does modifications, but preserves all the
      /// properties currently implemented, use an explicit
      ///
      /// \code
      ///    {true, true, true, true}
      /// \endcode
      ///
      /// instead of calling \c all().  This way, the day a new
      /// property is added, we will still be forced to review
      /// algorithm X, in case that new property is not preserved.
      static prop_set all()
      {
	return { true, true, true, true };
      }
    };

    /// \brief Copy the properties of another automaton.
    ///
    /// Copy the property speciefied with \a p from \a other to the
    /// current automaton.
    ///
    /// There is no default value for \a p on purpose.  This way any
    /// time we add a new property we have to update every call to
    /// prop_copy().
    ///
    /// \see prop_set
    void prop_copy(const const_twa_ptr& other, prop_set p)
    {
      if (p.state_based)
	prop_state_acc(other->prop_state_acc());
      if (p.inherently_weak)
	{
	  prop_terminal(other->prop_terminal());
	  prop_weak(other->prop_weak());
	  prop_inherently_weak(other->prop_inherently_weak());
	}
      if (p.deterministic)
	{
	  prop_deterministic(other->prop_deterministic());
	  prop_unambiguous(other->prop_unambiguous());
	}
      if (p.stutter_inv)
	prop_stutter_invariant(other->prop_stutter_invariant());
    }

    /// \brief Keep only a subset of properties of the current
    /// automaton.
    ///
    /// All properties part of a group set to \c false in \a p are reset
    /// to their default value of trival::maybe().
    void prop_keep(prop_set p)
    {
      if (!p.state_based)
	prop_state_acc(trival::maybe());
      if (!p.inherently_weak)
	{
	  prop_terminal(trival::maybe());
	  prop_weak(trival::maybe());
	  prop_inherently_weak(trival::maybe());
	}
      if (!p.deterministic)
	{
	  prop_deterministic(trival::maybe());
	  prop_unambiguous(trival::maybe());
	}
      if (!p.stutter_inv)
	prop_stutter_invariant(trival::maybe());
    }

  };

  /// \addtogroup twa_representation TGBA representations
  /// \ingroup twa

  /// \addtogroup twa_algorithms TGBA algorithms
  /// \ingroup twa

  /// \addtogroup twa_on_the_fly_algorithms TGBA on-the-fly algorithms
  /// \ingroup twa_algorithms

  /// \addtogroup twa_io Input/Output of TGBA
  /// \ingroup twa_algorithms

  /// \addtogroup twa_ltl Translating LTL formulae into TGBA
  /// \ingroup twa_algorithms

  /// \addtogroup twa_generic Algorithm patterns
  /// \ingroup twa_algorithms

  /// \addtogroup twa_reduction TGBA simplifications
  /// \ingroup twa_algorithms

  /// \addtogroup twa_misc Miscellaneous algorithms on TGBA
  /// \ingroup twa_algorithms
}
