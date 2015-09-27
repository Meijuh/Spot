// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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

/// \file ltlast/formula.hh
/// \brief LTL/PSL formula interface
#pragma once

#include "misc/common.hh"
#include <memory>
#include <cstdint>
#include <initializer_list>
#include <cassert>
#include <vector>
#include <string>
#include <iterator>
#include <iosfwd>
#include <sstream>
#include <list>
#include <cstddef>
#include <initializer_list>

namespace spot
{
  namespace ltl
  {
    enum class op: uint8_t
    {
      ff,
	tt,
	eword,
	ap,
      // unary operators
	Not,
	X,
	F,
	G,
	Closure,
	NegClosure,
	NegClosureMarked,
	// binary operators
	Xor,
	Implies,
	Equiv,
	U,		      ///< until
	R,		      ///< release (dual of until)
	W,		      ///< weak until
	M,		      ///< strong release (dual of weak until)
	EConcat,	      ///< Seq
	EConcatMarked,	      ///< Seq, Marked
	UConcat,	      ///< Triggers
	// n-ary operators
	Or,		      ///< (omega-Rational) Or
	OrRat,		      ///< Rational Or
	And,		      ///< (omega-Rational) And
	AndRat,		      ///< Rational And
	AndNLM,		      ///< Non-Length-Matching Rational-And
	Concat,
	Fusion,
	// star-like operators
	Star,		      ///< Star
	FStar,		      ///< Fustion Star
	};

#ifndef SWIG
    class SPOT_API fnode final
    {
    public:
      const fnode* clone() const
      {
	++refs_;
	return this;
      }

      void destroy() const
      {
	// last reference to a node that is not a constant?
	if (SPOT_UNLIKELY(!refs_ && id_ > 2))
	  destroy_aux();
	else
	  --refs_;
      }

      static constexpr uint8_t unbounded()
      {
	return UINT8_MAX;
      }

      static const fnode* ap(const std::string& name);
      static const fnode* unop(op o, const fnode* f);
      static const fnode* binop(op o, const fnode* f, const fnode* g);
      static const fnode* multop(op o, std::vector<const fnode*> l);
      static const fnode* bunop(op o, const fnode* f,
				  uint8_t min, uint8_t max = unbounded());

      op kind() const
      {
	return op_;
      }

      std::string kindstr() const;

      bool is(op o) const
      {
	return op_ == o;
      }

      bool is(op o1, op o2) const
      {
	return op_ == o1 || op_ == o2;
      }

      bool is(std::initializer_list<op> l) const
      {
	const fnode* n = this;
	for (auto o: l)
	  {
	    if (!n->is(o))
	      return false;
	    n = n->nth(0);
	  }
	return true;
      }

      /// \brief Remove operator \a o and return the child.
      ///
      /// This works only for unary operators.
      const fnode* get_child_of(op o) const
      {
	if (op_ != o)
	  return nullptr;
	assert(size_ == 1);
	return nth(0);
      }

      /// \brief Remove all operators in \a l and return the child.
      ///
      /// This works only for a list of unary operators.
      /// For instance if \c f  is a formula for XG(a U b),
      /// then <code>f.get_child_of({op::X, op::G})</code>
      /// will return the subformula a U b.
      const fnode* get_child_of(std::initializer_list<op> l) const
      {
	auto c = this;
	for (auto o: l)
	  {
	    c = c->get_child_of(o);
	    if (c == nullptr)
	      return c;
	  }
	return c;
      }

      uint8_t min() const
      {
	assert(op_ == op::FStar || op_ == op::Star);
	return min_;
      }

      uint8_t max() const
      {
	assert(op_ == op::FStar || op_ == op::Star);
	return max_;
      }

      uint8_t size() const
      {
	return size_;
      }

      size_t id() const
      {
	return id_;
      }

      const fnode*const* begin() const
      {
	return children;
      }

      const fnode*const* end() const
      {
	return children + size();
      }

      const fnode* nth(unsigned i) const
      {
	if (i >= size())
	  throw std::runtime_error("access to non-existing child");
	return children[i];
      }

      static const fnode* ff()
      {
	return ff_;
      }

      bool is_ff() const
      {
	return op_ == op::ff;
      }

      static const fnode* tt()
      {
	return tt_;
      }

      bool is_tt() const
      {
	return op_ == op::tt;
      }

      static const fnode* eword()
      {
	return ew_;
      }

      bool is_eword() const
      {
	return op_ == op::eword;
      }

      bool is_constant() const
      {
	return op_ == op::ff || op_ == op::tt || op_ == op::eword;
      }

      bool is_Kleene_star() const
      {
	if (op_ != op::Star)
	  return false;
	return min_ == 0 && max_ == unbounded();
      }

      static const fnode* one_star()
      {
	if (!one_star_)
	  one_star_ = bunop(op::Star, tt(), 0);
	return one_star_;
      }

      const std::string& ap_name() const;
      std::ostream& dump(std::ostream& os) const;

      const fnode* all_but(unsigned i) const;

      unsigned boolean_count() const
      {
	unsigned pos = 0;
	unsigned s = size();
	while (pos < s && children[pos]->is_boolean())
	  ++pos;
	return pos;
      }

      const fnode* boolean_operands(unsigned* width = nullptr) const;

      /// return true if the unicity map contains only the globally
      /// pre-allocated formulas.
      static bool instances_check();

      ////////////////
      // Properties //
      ////////////////

      /// Whether the formula use only boolean operators.
      bool is_boolean() const
      {
	return is_.boolean;
      }

      /// Whether the formula use only AND, OR, and NOT operators.
      bool is_sugar_free_boolean() const
      {
	return is_.sugar_free_boolean;
      }

      /// \brief Whether the formula is in negative normal form.
      ///
      /// A formula is in negative normal form if the not operators
      /// occur only in front of atomic propositions.
      bool is_in_nenoform() const
      {
	return is_.in_nenoform;
      }

      /// Whether the formula is syntactically stutter_invariant
      bool is_syntactic_stutter_invariant() const
      {
	return is_.syntactic_si;
      }

      /// Whether the formula avoids the F and G operators.
      bool is_sugar_free_ltl() const
      {
	return is_.sugar_free_ltl;
      }

      /// Whether the formula uses only LTL operators.
      bool is_ltl_formula() const
      {
	return is_.ltl_formula;
      }

      /// Whether the formula uses only PSL operators.
      bool is_psl_formula() const
      {
	return is_.psl_formula;
      }

      /// Whether the formula uses only SERE operators.
      bool is_sere_formula() const
      {
	return is_.sere_formula;
      }

      /// Whether a SERE describes a finite language, or an LTL
      /// formula uses no temporal operator but X.
      bool is_finite() const
      {
	return is_.finite;
      }

      /// \brief Whether the formula is purely eventual.
      ///
      /// Pure eventuality formulae are defined in
      /** \verbatim
          @InProceedings{	  etessami.00.concur,
          author  	= {Kousha Etessami and Gerard J. Holzmann},
          title		= {Optimizing {B\"u}chi Automata},
          booktitle	= {Proceedings of the 11th International Conference on
          		  Concurrency Theory (Concur'2000)},
          pages		= {153--167},
          year		= {2000},
          editor  	= {C. Palamidessi},
          volume  	= {1877},
          series  	= {Lecture Notes in Computer Science},
          publisher	= {Springer-Verlag}
          }
          \endverbatim */
      ///
      /// A word that satisfies a pure eventuality can be prefixed by
      /// anything and still satisfies the formula.
      bool is_eventual() const
      {
	return is_.eventual;
      }

      /// \brief Whether a formula is purely universal.
      ///
      /// Purely universal formulae are defined in
      /** \verbatim
          @InProceedings{	  etessami.00.concur,
          author  	= {Kousha Etessami and Gerard J. Holzmann},
          title		= {Optimizing {B\"u}chi Automata},
          booktitle	= {Proceedings of the 11th International Conference on
          		  Concurrency Theory (Concur'2000)},
          pages		= {153--167},
          year		= {2000},
          editor  	= {C. Palamidessi},
          volume  	= {1877},
          series  	= {Lecture Notes in Computer Science},
          publisher	= {Springer-Verlag}
          }
          \endverbatim */
      ///
      /// Any (non-empty) suffix of a word that satisfies a purely
      /// universal formula also satisfies the formula.
      bool is_universal() const
      {
	return is_.universal;
      }

      /// Whether a PSL/LTL formula is syntactic safety property.
      bool is_syntactic_safety() const
      {
	return is_.syntactic_safety;
      }

      /// Whether a PSL/LTL formula is syntactic guarantee property.
      bool is_syntactic_guarantee() const
      {
	return is_.syntactic_guarantee;
      }

      /// Whether a PSL/LTL formula is syntactic obligation property.
      bool is_syntactic_obligation() const
      {
	return is_.syntactic_obligation;
      }

      /// Whether a PSL/LTL formula is syntactic recurrence property.
      bool is_syntactic_recurrence() const
      {
	return is_.syntactic_recurrence;
      }

      /// Whether a PSL/LTL formula is syntactic persistence property.
      bool is_syntactic_persistence() const
      {
	return is_.syntactic_persistence;
      }

      /// Whether the formula has an occurrence of EConcatMarked.
      bool is_marked() const
      {
	return !is_.not_marked;
      }

      /// Whether the formula accepts [*0].
      bool accepts_eword() const
      {
	return is_.accepting_eword;
      }

      bool has_lbt_atomic_props() const
      {
	return is_.lbt_atomic_props;
      }

      bool has_spin_atomic_props() const
      {
	return is_.spin_atomic_props;
      }

    private:
      void setup_props(op o);
      void destroy_aux() const;

      static const fnode* unique(const fnode*);

      // Destruction may only happen via destroy().
      ~fnode() = default;
      // Disallow copies.
      fnode(const fnode&) = delete;
      fnode& operator=(const fnode&) = delete;



      template<class iter>
      fnode(op o, iter begin, iter end)
      {
	size_t s = std::distance(begin, end);
	if (s > (size_t) UINT16_MAX)
	  throw std::runtime_error("too many children for formula");
	size_ = s;
	auto pos = children;
	for (auto i = begin; i != end; ++i)
	  *pos++ = *i;
	setup_props(o);
      }

      fnode(op o, std::initializer_list<const fnode*> l)
	: fnode(o, l.begin(), l.end())
      {
      }

      fnode(op o, const fnode* f, uint8_t min, uint8_t max)
      {
	size_ = 1;
	children[0] = f;
	min_ = min;
	max_ = max;
	setup_props(o);
      }

      static const fnode* ff_;
      static const fnode* tt_;
      static const fnode* ew_;
      static const fnode* one_star_;

      op op_;			// operator
      uint8_t min_;		// range minimum (for star-like operators)
      uint8_t max_;		// range maximum;
      //uint8_t unused_;
      uint16_t size_;		// number of children
      mutable uint16_t refs_ = 0; // reference count - 1;
      size_t id_;		// Also used as hash.
      static size_t next_id_;

      struct ltl_prop
      {
	// All properties here should be expressed in such a a way
	// that property(f && g) is just property(f)&property(g).
	// This allows us to compute all properties of a compound
	// formula in one operation.
	//
	// For instance we do not use a property that says "has
	// temporal operator", because it would require an OR between
	// the two arguments.  Instead we have a property that
	// says "no temporal operator", and that one is computed
	// with an AND between the arguments.
	//
	// Also choose a name that makes sense when prefixed with
	// "the formula is".
	bool boolean:1;		   // No temporal operators.
	bool sugar_free_boolean:1; // Only AND, OR, and NOT operators.
	bool in_nenoform:1;	   // Negative Normal Form.
	bool syntactic_si:1;	   // LTL-X or siPSL
	bool sugar_free_ltl:1;	   // No F and G operators.
	bool ltl_formula:1;	   // Only LTL operators.
	bool psl_formula:1;	   // Only PSL operators.
	bool sere_formula:1;	   // Only SERE operators.
	bool finite:1;		   // Finite SERE formulae, or Bool+X forms.
	bool eventual:1;	   // Purely eventual formula.
	bool universal:1;	   // Purely universal formula.
	bool syntactic_safety:1;   // Syntactic Safety Property.
	bool syntactic_guarantee:1;   // Syntactic Guarantee Property.
	bool syntactic_obligation:1;  // Syntactic Obligation Property.
	bool syntactic_recurrence:1;  // Syntactic Recurrence Property.
	bool syntactic_persistence:1; // Syntactic Persistence Property.
	bool not_marked:1;	   // No occurrence of EConcatMarked.
	bool accepting_eword:1;	   // Accepts the empty word.
	bool lbt_atomic_props:1;   // Use only atomic propositions like p42.
	bool spin_atomic_props:1;  // Use only spin-compatible atomic props.
      };
      union
      {
	// Use an unsigned for fast computation of all properties.
	unsigned props;
	ltl_prop is_;
      };

      const fnode* children[1];
    };

    /// Order two atomic propositions.
    SPOT_API
    int atomic_prop_cmp(const fnode* f, const fnode* g);

    /// \brief Strict Weak Ordering for <code>const fnode*</code>
    ///        inside n-ary operators
    /// \ingroup ltl_essentials
    ///
    /// This is the comparison functor used by to order the
    /// n-ary operands.  It keeps Boolean formulae first in
    /// order to speed up implication checks.
    ///
    /// Also keep literal alphabetically ordered.
    struct formula_ptr_less_than_bool_first
    {
      bool
      operator()(const fnode* left, const fnode* right) const
      {
	assert(left);
	assert(right);
	if (left == right)
	  return false;

	// We want Boolean formulae first.
	bool lib = left->is_boolean();
	if (lib != right->is_boolean())
	  return lib;

	// We have two Boolean formulae
	if (lib)
	  {
	    bool lconst = left->is_constant();
	    if (lconst != right->is_constant())
	      return lconst;
	    if (!lconst)
	      {
		auto get_literal = [](const fnode* f) -> const fnode*
		  {
		    if (f->is(op::Not))
		      f = f->nth(0);
		    if (f->is(op::ap))
		      return f;
		    return nullptr;
		  };
		// Literals should come first
		const fnode* litl = get_literal(left);
		const fnode* litr = get_literal(right);
		if (!litl != !litr)
		  return litl;
		if (litl)
		  {
		    // And they should be sorted alphabetically
		    int cmp = atomic_prop_cmp(litl, litr);
		    if (cmp)
		      return cmp < 0;
		  }
	      }
	  }

	size_t l = left->id();
	size_t r = right->id();
	if (l != r)
	  return l < r;
	// Because the hash code assigned to each formula is the
	// number of formulae constructed so far, it is very unlikely
	// that we will ever reach a case were two different formulae
	// have the same hash.  This will happen only ever with have
	// produced 256**sizeof(size_t) formulae (i.e. max_count has
	// looped back to 0 and started over).  In that case we can
	// order two formulas by looking at their text representation.
	// We could be more efficient and look at their AST, but it's
	// not worth the burden.  (Also ordering pointers is ruled out
	// because it breaks the determinism of the implementation.)
	std::ostringstream old;
	left->dump(old);
	std::ostringstream ord;
	right->dump(ord);
	return old.str() < ord.str();
      }
    };

#endif // SWIG

    class SPOT_API formula final
    {
      const fnode* ptr_;
    public:
      explicit formula(const fnode* f) noexcept
	: ptr_(f)
      {
      }

      formula(std::nullptr_t) noexcept
	: ptr_(nullptr)
      {
      }

      formula() noexcept
	: ptr_(nullptr)
      {
      }

      formula(const formula& f) noexcept
	: ptr_(f.ptr_)
      {
	if (ptr_)
	  ptr_->clone();
      }

      formula(formula&& f) noexcept
	: ptr_(f.ptr_)
      {
	f.ptr_ = nullptr;
      }

      ~formula()
      {
	if (ptr_)
	  ptr_->destroy();
      }

      const formula& operator=(std::nullptr_t)
      {
	this->~formula();
	ptr_ = nullptr;
	return *this;
      }

      const formula& operator=(const formula& f)
      {
	this->~formula();
	if ((ptr_ = f.ptr_))
	  ptr_->clone();
	return *this;
      }

      const formula& operator=(formula&& f) noexcept
      {
	std::swap(f.ptr_, ptr_);
	return *this;
      }

      bool operator<(const formula& other) const noexcept
      {
	if (SPOT_UNLIKELY(!other.ptr_))
	  return false;
	if (SPOT_UNLIKELY(!ptr_))
	  return true;
	return id() < other.id();
      }

      bool operator<=(const formula& other) const noexcept
      {
	if (SPOT_UNLIKELY(!other.ptr_))
	  return !ptr_;
	if (SPOT_UNLIKELY(!ptr_))
	  return true;
	return id() <= other.id();
      }

      bool operator>(const formula& other) const noexcept
      {
	if (SPOT_UNLIKELY(!ptr_))
	  return false;
	if (SPOT_UNLIKELY(!other.ptr_))
	  return true;
	return id() > other.id();
      }

      bool operator>=(const formula& other) const noexcept
      {
	if (SPOT_UNLIKELY(!ptr_))
	  return !!other.ptr_;
	if (SPOT_UNLIKELY(!other.ptr_))
	  return true;
	return id() >= other.id();
      }

      bool operator==(const formula& other) const noexcept
      {
	return other.ptr_ == ptr_;
      }

      bool operator==(std::nullptr_t) const noexcept
      {
	return ptr_ == nullptr;
      }

      bool operator!=(const formula& other) const noexcept
      {
	return other.ptr_ != ptr_;
      }

      bool operator!=(std::nullptr_t) const noexcept
      {
	return ptr_ != nullptr;
      }

      operator bool() const
      {
	return ptr_ != nullptr;
      }

      /////////////////////////
      // Forwarded functions //
      /////////////////////////

      static constexpr uint8_t unbounded()
      {
	return fnode::unbounded();
      }

      static formula ap(const std::string& name)
      {
	return formula(fnode::ap(name));
      }

      static formula unop(op o, const formula& f)
      {
	return formula(fnode::unop(o, f.ptr_->clone()));
      }

#ifndef SWIG
      static formula unop(op o, formula&& f)
      {
	return formula(fnode::unop(o, f.to_node_()));
      }
#endif // !SWIG

#ifdef SWIG
#define SPOT_DEF_UNOP(Name)			\
      static formula Name(const formula& f)	\
      {						\
	return unop(op::Name, f);		\
      }
#else // !SWIG
#define SPOT_DEF_UNOP(Name)			\
      static formula Name(const formula& f)	\
      {						\
	return unop(op::Name, f);		\
      }						\
      static formula Name(formula&& f)		\
      {						\
	return unop(op::Name, std::move(f));	\
      }
#endif // !SWIG
      SPOT_DEF_UNOP(Not);
      SPOT_DEF_UNOP(X);
      SPOT_DEF_UNOP(F);
      SPOT_DEF_UNOP(G);
      SPOT_DEF_UNOP(Closure);
      SPOT_DEF_UNOP(NegClosure);
      SPOT_DEF_UNOP(NegClosureMarked);
#undef SPOT_DEF_UNOP

      static formula binop(op o, const formula& f, const formula& g)
      {
	return formula(fnode::binop(o, f.ptr_->clone(), g.ptr_->clone()));
      }

#ifndef SWIG
      static formula binop(op o, const formula& f, formula&& g)
      {
	return formula(fnode::binop(o, f.ptr_->clone(), g.to_node_()));
      }

      static formula binop(op o, formula&& f, const formula& g)
      {
	return formula(fnode::binop(o, f.to_node_(), g.ptr_->clone()));
      }

      static formula binop(op o, formula&& f, formula&& g)
      {
	return formula(fnode::binop(o, f.to_node_(), g.to_node_()));
      }
#endif //SWIG

#ifdef SWIG
#define SPOT_DEF_BINOP(Name)					\
      static formula Name(const formula& f, const formula& g)	\
      {								\
	return binop(op::Name, f, g);				\
      }
#else // !SWIG
#define SPOT_DEF_BINOP(Name)					\
      static formula Name(const formula& f, const formula& g)	\
      {								\
	return binop(op::Name, f, g);				\
      }								\
      static formula Name(const formula& f, formula&& g)	\
      {								\
	return binop(op::Name, f, std::move(g));		\
      }								\
      static formula Name(formula&& f, const formula& g)	\
      {								\
	return binop(op::Name, std::move(f), g);		\
      }								\
      static formula Name(formula&& f, formula&& g)		\
      {								\
	return binop(op::Name, std::move(f), std::move(g));	\
      }
#endif // !SWIG
      SPOT_DEF_BINOP(Xor);
      SPOT_DEF_BINOP(Implies);
      SPOT_DEF_BINOP(Equiv);
      SPOT_DEF_BINOP(U);
      SPOT_DEF_BINOP(R);
      SPOT_DEF_BINOP(W);
      SPOT_DEF_BINOP(M);
      SPOT_DEF_BINOP(EConcat);
      SPOT_DEF_BINOP(EConcatMarked);
      SPOT_DEF_BINOP(UConcat);
#undef SPOT_DEF_BINOP

      static formula multop(op o, const std::vector<formula>& l)
      {
	std::vector<const fnode*> tmp;
	tmp.reserve(l.size());
	for (auto f: l)
	  if (f.ptr_)
	    tmp.push_back(f.ptr_->clone());
	return formula(fnode::multop(o, std::move(tmp)));
      }

#ifndef SWIG
      static formula multop(op o, std::vector<formula>&& l)
      {
	std::vector<const fnode*> tmp;
	tmp.reserve(l.size());
	for (auto f: l)
	  if (f.ptr_)
	    tmp.push_back(f.to_node_());
	return formula(fnode::multop(o, std::move(tmp)));
      }
#endif // !SWIG

#ifdef SWIG
#define SPOT_DEF_MULTOP(Name)					\
      static formula Name(const std::vector<formula>& l)	\
      {								\
	return multop(op::Name, l);				\
      }
#else // !SWIG
#define SPOT_DEF_MULTOP(Name)					\
      static formula Name(const std::vector<formula>& l)	\
      {								\
	return multop(op::Name, l);				\
      }								\
								\
      static formula Name(std::vector<formula>&& l)		\
      {								\
	return multop(op::Name, std::move(l));			\
      }
#endif // !SWIG
      SPOT_DEF_MULTOP(Or);
      SPOT_DEF_MULTOP(OrRat);
      SPOT_DEF_MULTOP(And);
      SPOT_DEF_MULTOP(AndRat);
      SPOT_DEF_MULTOP(AndNLM);
      SPOT_DEF_MULTOP(Concat);
      SPOT_DEF_MULTOP(Fusion);
#undef SPOT_DEF_MULTOP

      static formula bunop(op o, const formula& f,
			   uint8_t min = 0U,
			   uint8_t max = unbounded())
      {
	return formula(fnode::bunop(o, f.ptr_->clone(), min, max));
      }

#ifndef SWIG
      static formula bunop(op o, formula&& f,
			   uint8_t min = 0U,
			   uint8_t max = unbounded())
      {
	return formula(fnode::bunop(o, f.to_node_(), min, max));
      }
#endif // !SWIG

#if SWIG
#define SPOT_DEF_BUNOP(Name)				\
      static formula Name(const formula& f,		\
			  uint8_t min = 0U,		\
			  uint8_t max = unbounded())	\
      {							\
	return bunop(op::Name, f, min, max);		\
      }
#else // !SWIG
#define SPOT_DEF_BUNOP(Name)				\
      static formula Name(const formula& f,		\
			  uint8_t min = 0U,		\
			  uint8_t max = unbounded())	\
      {							\
	return bunop(op::Name, f, min, max);		\
      }							\
      static formula Name(formula&& f,			\
			  uint8_t min = 0U,		\
			  uint8_t max = unbounded())	\
      {							\
	return bunop(op::Name, std::move(f), min, max);	\
      }
#endif
      SPOT_DEF_BUNOP(Star);
      SPOT_DEF_BUNOP(FStar);
#undef SPOT_DEF_BUNOP

      static formula sugar_goto(const formula& b, uint8_t min, uint8_t max);

      static formula sugar_equal(const formula& b, uint8_t min, uint8_t max);

#ifndef SWIG
      const fnode* to_node_()
      {
	auto tmp = ptr_;
	ptr_ = nullptr;
	return tmp;
      }
#endif

      op kind() const
      {
	return ptr_->kind();
      }

      std::string kindstr() const
      {
	return ptr_->kindstr();
      }

      bool is(op o) const
      {
	return ptr_->is(o);
      }

#ifndef SWIG
      bool is(op o1, op o2) const
      {
	return ptr_->is(o1, o2);
      }

      bool is(std::initializer_list<op> l) const
      {
	return ptr_->is(l);
      }
#endif

      formula get_child_of(op o) const
      {
	auto f = ptr_->get_child_of(o);
	if (f)
	  f->clone();
	return formula(f);
      }

#ifndef SWIG
      formula get_child_of(std::initializer_list<op> l) const
      {
	auto f = ptr_->get_child_of(l);
	if (f)
	  f->clone();
	return formula(f);
      }
#endif

      uint8_t min() const
      {
	return ptr_->min();
      }

      uint8_t max() const
      {
	return ptr_->max();
      }

      uint8_t size() const
      {
	return ptr_->size();
      }

      size_t id() const
      {
	return ptr_->id();
      }

#ifndef SWIG
      class SPOT_API formula_child_iterator final
      {
	const fnode*const* ptr_;
      public:
	formula_child_iterator()
	  : ptr_(nullptr)
	{
	}

	formula_child_iterator(const fnode*const* f)
	  : ptr_(f)
	{
	}

	bool operator==(formula_child_iterator o)
	{
	  return ptr_ == o.ptr_;
	}

	bool operator!=(formula_child_iterator o)
	{
	  return ptr_ != o.ptr_;
	}

	formula operator*()
	{
	  return formula((*ptr_)->clone());
	}

	formula_child_iterator operator++()
	{
	  ++ptr_;
	  return *this;
	}

	formula_child_iterator operator++(int)
	{
	  auto tmp = *this;
	  ++ptr_;
	  return tmp;
	}
      };

      formula_child_iterator begin() const
      {
	return ptr_->begin();
      }

      formula_child_iterator end() const
      {
	return ptr_->end();
      }

      formula operator[](unsigned i) const
      {
	return formula(ptr_->nth(i)->clone());
      }
#endif

      static formula ff()
      {
	return formula(fnode::ff());
      }

      bool is_ff() const
      {
	return ptr_->is_ff();
      }

      static formula tt()
      {
	return formula(fnode::tt());
      }

      bool is_tt() const
      {
	return ptr_->is_tt();
      }

      static formula eword()
      {
	return formula(fnode::eword());
      }

      bool is_eword() const
      {
	return ptr_->is_eword();
      }

      bool is_constant() const
      {
	return ptr_->is_constant();
      }

      bool is_Kleene_star() const
      {
	return ptr_->is_Kleene_star();
      }

      static formula one_star()
      {
	return formula(fnode::one_star()->clone());
      }

      bool is_literal()
      {
	return (is(op::ap) ||
		// If f is in nenoform, Not can only occur in front of
		// an atomic proposition.  So this way we do not have
		// to check the type of the child.
		(is(op::Not) && is_boolean() && is_in_nenoform()));
      }

      const std::string& ap_name() const
      {
	return ptr_->ap_name();
      }

      std::ostream& dump(std::ostream& os) const
      {
	return ptr_->dump(os);
      }

      formula all_but(unsigned i) const
      {
	return formula(ptr_->all_but(i));
      }

      unsigned boolean_count() const
      {
	return ptr_->boolean_count();
      }

      formula boolean_operands(unsigned* width = nullptr) const
      {
	return formula(ptr_->boolean_operands(width));
      }

#define SPOT_DEF_PROP(Name)			\
      bool Name() const				\
      {						\
	return ptr_->Name();			\
      }
      SPOT_DEF_PROP(is_boolean);
      SPOT_DEF_PROP(is_sugar_free_boolean);
      SPOT_DEF_PROP(is_in_nenoform);
      SPOT_DEF_PROP(is_syntactic_stutter_invariant);
      SPOT_DEF_PROP(is_sugar_free_ltl);
      SPOT_DEF_PROP(is_ltl_formula);
      SPOT_DEF_PROP(is_psl_formula);
      SPOT_DEF_PROP(is_sere_formula);
      SPOT_DEF_PROP(is_finite);
      SPOT_DEF_PROP(is_eventual);
      SPOT_DEF_PROP(is_universal);
      SPOT_DEF_PROP(is_syntactic_safety);
      SPOT_DEF_PROP(is_syntactic_guarantee);
      SPOT_DEF_PROP(is_syntactic_obligation);
      SPOT_DEF_PROP(is_syntactic_recurrence);
      SPOT_DEF_PROP(is_syntactic_persistence);
      SPOT_DEF_PROP(is_marked);
      SPOT_DEF_PROP(accepts_eword);
      SPOT_DEF_PROP(has_lbt_atomic_props);
      SPOT_DEF_PROP(has_spin_atomic_props);
#undef SPOT_DEF_PROP

      template<typename Trans>
      formula map(Trans trans)
      {
	switch (op o = kind())
	  {
	  case op::ff:
	  case op::tt:
	  case op::eword:
	  case op::ap:
	    return *this;
	  case op::Not:
	  case op::X:
	  case op::F:
	  case op::G:
	  case op::Closure:
	  case op::NegClosure:
	  case op::NegClosureMarked:
	    return unop(o, trans((*this)[0]));
	  case op::Xor:
	  case op::Implies:
	  case op::Equiv:
	  case op::U:
	  case op::R:
	  case op::W:
	  case op::M:
	  case op::EConcat:
	  case op::EConcatMarked:
	  case op::UConcat:
	    {
	      formula tmp = trans((*this)[0]);
	      return binop(o, tmp, trans((*this)[1]));
	    }
	  case op::Or:
	  case op::OrRat:
	  case op::And:
	  case op::AndRat:
	  case op::AndNLM:
	  case op::Concat:
	  case op::Fusion:
	    {
	      std::vector<formula> tmp;
	      tmp.reserve(size());
	      for (auto f: *this)
		tmp.push_back(trans(f));
	      return multop(o, std::move(tmp));
	    }
	  case op::Star:
	  case op::FStar:
	    return bunop(o, trans((*this)[0]), min(), max());
	  }
	SPOT_UNREACHABLE();
      }

      template<typename Func>
      void traverse(Func func)
      {
	if (func(*this))
	  return;
	for (auto f: *this)
	  f.traverse(func);
      }
    };

    /// Print the properties of formula \a f on stream \a out.
    SPOT_API
    std::ostream& print_formula_props(std::ostream& out, const formula& f,
				      bool abbreviated = false);

    /// List the properties of formula \a f.
    SPOT_API
    std::list<std::string> list_formula_props(const formula& f);
  }
}

#ifndef SWIG
namespace std
{
  template <>
  struct hash<spot::ltl::formula>
  {
    size_t operator()(const spot::ltl::formula& x) const noexcept
    {
      return x.id();
    }
  };
}
#endif
