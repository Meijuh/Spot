// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2011, 2013, 2014, 2015 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
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

#include "fwd.hh"
#include "acc.hh"
#include "bdddict.hh"
#include <cassert>
#include <memory>
#include <unordered_map>
#include <functional>
#include <array>
#include <vector>
#include "misc/casts.hh"
#include "misc/hash.hh"
#include "tl/formula.hh"

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
    /// <code>s->destroy();</code> instead of <code>delete s;</code>.
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

  typedef std::unordered_set<const state*,
			     state_ptr_hash, state_ptr_equal> state_set;


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
  /// un \c unordered_map whose key are of type \c shared_state.
  ///
  /// For instance here is how one could declare
  /// a map of \c shared_state
  /// \code
  ///   // Remember how many times each state has been visited.
  ///   std::unordered_map<shared_state, int,
  ///                      state_shared_ptr_hash,
  ///                      state_shared_ptr_equal> seen;
  /// \endcode
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
  struct state_shared_ptr_hash
  {
    size_t
    operator()(shared_state that) const
    {
      assert(that);
      return that->hash();
    }
  };

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
    virtual state* dst() const = 0;
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
  /// cousins are listed \ref tgba_essentials "here".  This is an
  /// abstract interface.  Its implementations are either \ref
  /// tgba_representation "concrete representations", or \ref
  /// tgba_on_the_fly_algorithms "on-the-fly algorithms".  Other
  /// algorithms that work on spot::twa are \ref tgba_algorithms
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
  /// Previous version of Spot supported a type of automata called
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
    // Any iterator returned via release_iter.
    mutable twa_succ_iterator* iter_cache_;
    bdd_dict_ptr dict_;
  public:

#ifndef SWIG
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
    virtual state* get_init_state() const = 0;

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
    /// <code>for (auto i: aut->succ(s)) { /* i->dst() */ }</code>.
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
      aps_.push_back(ap);
      int res = dict_->register_proposition(ap, this);
      bddaps_ &= bdd_ithvar(res);
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


    const acc_cond& acc() const
    {
      return acc_;
    }

    acc_cond& acc()
    {
      return acc_;
    }

    virtual bool is_empty() const;

  protected:
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
    unsigned num_sets() const
    {
      return acc_.num_sets();
    }

    const acc_cond::acc_code& get_acceptance() const
    {
      return acc_.get_acceptance();
    }

    void set_acceptance(unsigned num, const acc_cond::acc_code& c)
    {
      set_num_sets_(num);
      acc_.set_acceptance(c);
      if (num == 0)
	prop_state_acc(true);
    }

    /// \brief Copy the acceptance condition of another tgba.
    void copy_acceptance_of(const const_twa_ptr& a)
    {
      acc_ = a->acc();
      unsigned num = acc_.num_sets();
      if (num == 0)
	prop_state_acc(true);
    }

    void copy_ap_of(const const_twa_ptr& a)
    {
      get_dict()->register_all_propositions_of(a, this);
      for (auto f: a->ap())
	this->register_ap(f);
    }

    void set_generalized_buchi(unsigned num)
    {
      set_num_sets_(num);
      acc_.set_generalized_buchi();
      if (num == 0)
	prop_state_acc(true);
    }

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

    // Boolean properties.  Beware: true means that the property
    // holds, but false means the property is unknown.
    struct bprop
    {
      bool state_based_acc:1;	// State-based acceptance.
      bool inherently_weak:1;	// Inherently Weak automaton.
      bool weak:1;		// Weak automaton.
      bool deterministic:1;	// Deterministic automaton.
      bool unambiguous:1;	// Unambiguous automaton.
      bool stutter_invariant:1;	// Stutter invariant language.
      bool stutter_sensitive:1;	// Stutter sensitive language.
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
    void set_named_prop(std::string s,
			void* val, std::function<void(void*)> destructor);

    template<typename T>
    void set_named_prop(std::string s, T* val)
    {
      set_named_prop(s, val, [](void *p) { delete static_cast<T*>(p); });
    }

    template<typename T>
    T* get_named_prop(std::string s) const
    {
      void* p = get_named_prop_(s);
      if (!p)
	return nullptr;
      return static_cast<T*>(p);
    }
#endif

    void release_named_properties()
    {
      // Destroy all named properties.
      for (auto& np: named_prop_)
	np.second.second(np.second.first);
      named_prop_.clear();
    }

    bool prop_state_acc() const
    {
      return is.state_based_acc;
    }

    void prop_state_acc(bool val)
    {
      is.state_based_acc = val;
    }

    bool is_sba() const
    {
      return prop_state_acc() && acc().is_buchi();
    }

    bool prop_inherently_weak() const
    {
      return is.inherently_weak;
    }

    void prop_inherently_weak(bool val)
    {
      is.inherently_weak = val;
    }

    bool prop_weak() const
    {
      return is.weak;
    }

    void prop_weak(bool val)
    {
      if (val)
	is.inherently_weak = is.weak = true;
      else
	is.weak = false;
    }

    bool prop_deterministic() const
    {
      return is.deterministic;
    }

    void prop_deterministic(bool val)
    {
      if (val)
	{
	  // deterministic implies unambiguous
	  is.deterministic = true;
	  is.unambiguous = true;
	}
      else
	{
	  is.deterministic = false;
	}
    }

    bool prop_unambiguous() const
    {
      return is.unambiguous;
    }

    void prop_unambiguous(bool val)
    {
      is.unambiguous = val;
    }

    bool prop_stutter_invariant() const
    {
      return is.stutter_invariant;
    }

    bool prop_stutter_sensitive() const
    {
      return is.stutter_sensitive;
    }

    void prop_stutter_invariant(bool val)
    {
      is.stutter_invariant = val;
    }

    void prop_stutter_sensitive(bool val)
    {
      is.stutter_sensitive = val;
    }

    struct prop_set
    {
      bool state_based;
      bool inherently_weak;	// and weak
      bool deterministic;	// and unambiguous
      bool stutter_inv;		// and stutter_sensitive

      static prop_set all()
      {
	return { true, true, true, true };
      }
    };

    // There is no default value here on purpose.  This way any time we
    // add a new property we have to update every call to prop_copy().
    void prop_copy(const const_twa_ptr& other, prop_set p)
    {
      if (p.state_based)
	prop_state_acc(other->prop_state_acc());
      if (p.inherently_weak)
	{
	  prop_weak(other->prop_weak());
	  prop_inherently_weak(other->prop_inherently_weak());
	}
      if (p.deterministic)
	{
	  prop_deterministic(other->prop_deterministic());
	  prop_unambiguous(other->prop_unambiguous());
	}
      if (p.stutter_inv)
	{
	  prop_stutter_invariant(other->prop_stutter_invariant());
	  prop_stutter_sensitive(other->prop_stutter_sensitive());
	}
    }

    void prop_keep(prop_set p)
    {
      if (!p.state_based)
	prop_state_acc(false);
      if (!p.inherently_weak)
	{
	  prop_weak(false);
	  prop_inherently_weak(false);
	}
      if (!p.deterministic)
	{
	  prop_deterministic(false);
	  prop_unambiguous(false);
	}
      if (!p.stutter_inv)
	{
	  prop_stutter_invariant(false);
	  prop_stutter_sensitive(false);
	}
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
