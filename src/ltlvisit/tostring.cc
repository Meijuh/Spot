// Copyright (C) 2008, 2010, 2012 Laboratoire de Recherche et
// Développement de l'Epita (LRDE)
// Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.	 See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#include <cassert>
#include <sstream>
#include <ctype.h>
#include <ostream>
#include <cstring>
#include "ltlast/allnodes.hh"
#include "ltlast/visitor.hh"
#include "lunabbrev.hh"
#include "tostring.hh"


namespace spot
{
  namespace ltl
  {
    namespace
    {
      enum keyword {
	KFalse = 0,
	KTrue = 1,
	KEmptyWord = 2,
	KXor,
	KImplies,
	KEquiv,
	KU,
	KR,
	KW,
	KM,
	KEConcat,
	KEConcatNext,
	KEConcatMarked,
	KEConcatMarkedNext,
	KUConcat,
	KUConcatNext,
	KNot,
	KX,
	KF,
	KG,
	KOr,
	KAnd,
	KAndLM,
	KAndNLM,
	KConcat,
	KFusion
      };

      const char* spot_kw[] = {
	"0",
	"1",
	"[*0]",
	" xor ",
	" -> ",
	" <-> ",
	" U ",
	" R ",
	" W ",
	" M ",
	" <>-> ",
	" <>=> ",
	" <>+> ",
	" <>=+> ",
	" []-> ",
	" []=> ",
	"!",
	"X",
	"F",
	"G",
	" | ",
	" & ",
	" && ",
	" & ",
	" ; ",
	" : "
      };

      const char* spin_kw[] = {
	"0",
	"1",
	"[*0]",			// not supported
	" xor ",		// rewritten
	" -> ",			// rewritten
	" <-> ",		// rewritten
	" U ",
	" V ",
	" W ",			// not supported
	" M ",			// not supported
	" <>-> ",		// not supported
	" <>=> ",		// not supported
	" <>+> ",		// not supported
	" <>=+> ",		// not supported
	" []-> ",		// not supported
	" []=> ",		// not supported
	"!",
	"()",
	"<>",
	"[]",
	" || ",
	" && ",
	" && ",			// not supported
	" & ",			// not supported
	" ; ",			// not supported
	" : ",			// not supported
      };

      static bool
      is_bare_word(const char* str)
      {
	// Bare words cannot be empty, start with the letter of a unary
	// operator, or be the name of an existing constant.  Also they
	// should start with an letter.
	if (!*str
	    || *str == 'F'
	    || *str == 'G'
	    || *str == 'X'
	    || !(isalpha(*str) || *str == '_')
	    || !strcasecmp(str, "true")
	    || !strcasecmp(str, "false"))
	  return false;
	// The remaining of the word must be alphanumeric.
	while (*++str)
	  if (!(isalnum(*str) || *str == '_'))
	    return false;
	return true;
      }

      class to_string_visitor: public const_visitor
      {
      public:
	to_string_visitor(std::ostream& os,
			  bool full_parent = false,
			  bool ratexp = false,
			  const char** kw = spot_kw)
	  : os_(os), top_level_(true),
	    full_parent_(full_parent), in_ratexp_(ratexp),
	    kw_(kw)
	{
	}

	virtual
	~to_string_visitor()
	{
	}

	void
	openp() const
	{
	  os_ << (in_ratexp_ ? "{" : "(");
	}

	void
	closep() const
	{
	  os_ << (in_ratexp_ ? "}" : ")");
	}

	std::ostream&
	emit(int symbol)
	{
	  return os_ << kw_[symbol];
	}

	void
	visit(const atomic_prop* ap)
	{
	  std::string str = ap->name();
	  if (full_parent_)
	    os_ << "(";
	  if (!is_bare_word(str.c_str()))
	    {
	      os_ << '"' << str << '"';
	    }
	  else
	    {
	      os_ << str;
	    }
	  if (full_parent_)
	    os_ << ")";
	}

	void
	visit(const constant* c)
	{
	  if (full_parent_)
	    openp();
	  switch (c->val())
	    {
	    case constant::False:
	      emit(KFalse);
	      break;
	    case constant::True:
	      emit(KTrue);
	      break;
	    case constant::EmptyWord:
	      emit(KEmptyWord);
	      break;
	    }
	  if (full_parent_)
	    closep();
	}

	void
	visit(const binop* bo)
	{
	  bool top_level = top_level_;
	  top_level_ = false;
	  if (!top_level)
	    openp();

	  bool onelast = false;

	  switch (bo->op())
	    {
	    case binop::UConcat:
	    case binop::EConcat:
	    case binop::EConcatMarked:
	      os_ << "{";
	      in_ratexp_ = true;
	      top_level_ = true;
	      {
		multop* m = is_multop(bo->first(), multop::Concat);
		if (m)
		  {
		    unsigned s = m->size();
		    if (m->nth(s - 1) == constant::true_instance())
		      {
			formula* tmp = m->all_but(s - 1);
			tmp->accept(*this);
			tmp->destroy();
			onelast = true;
			break;
		      }
		  }
	      }
	      // fall through
	    default:
	      bo->first()->accept(*this);
	      break;
	    }

	  switch (bo->op())
	    {
	    case binop::Xor:
	      emit(KXor);
	      break;
	    case binop::Implies:
	      emit(KImplies);
	      break;
	    case binop::Equiv:
	      emit(KEquiv);
	      break;
	    case binop::U:
	      emit(KU);
	      break;
	    case binop::R:
	      emit(KR);
	      break;
	    case binop::W:
	      emit(KW);
	      break;
	    case binop::M:
	      emit(KM);
	      break;
	    case binop::UConcat:
	      os_ << "}";
	      emit(onelast ? KUConcatNext : KUConcat);
	      in_ratexp_ = false;
	      top_level_ = top_level;
	      break;
	    case binop::EConcat:
	      if (bo->second() == constant::true_instance())
		{
		  os_ << "}!";
		  in_ratexp_ = false;
		  goto second_done;
		}
	      os_ << "}";
	      emit(onelast ? KEConcatNext : KEConcat);
	      in_ratexp_ = false;
	      top_level_ = false;
	      break;
	    case binop::EConcatMarked:
	      os_ << "}";
	      emit(onelast ? KEConcatMarkedNext : KEConcatMarked);
	      in_ratexp_ = false;
	      top_level_ = false;
	      break;
	    }

	  bo->second()->accept(*this);
	second_done:
	  if (!top_level)
	    closep();
	}

	void
	visit(const bunop* bo)
	{
	  // Abbreviate "1[*]" as "[*]".
	  if (bo->child() != constant::true_instance())
	    {
	      // a[*] is OK, no need to print {a}[*].
	      // However want braces for {!a}[*], the only unary
	      // operator that can be nested with [*].

	      formula::opkind ck = bo->child()->kind();
	      bool need_parent = (full_parent_
				  || ck == formula::UnOp
				  || ck == formula::BinOp
				  || ck == formula::MultOp);

	      if (need_parent)
		openp();
	      bo->child()->accept(*this);
	      if (need_parent)
		closep();
	    }

	  os_ << bo->format();
	}

	void
	visit(const unop* uo)
	{
	  top_level_ = false;
	  // The parser treats F0, F1, G0, G1, X0, and X1 as atomic
	  // propositions.  So make sure we output F(0), G(1), etc.
	  bool need_parent = (uo->child()->kind() == formula::Constant);
	  bool top_level = top_level_;

	  if (full_parent_)
	    {
	      need_parent = false; // These will be printed by each subformula

	      if (!top_level)
		openp();
	    }

	  switch (uo->op())
	    {
	    case unop::Not:
	      emit(KNot);
	      need_parent = false;
	      break;
	    case unop::X:
	      emit(KX);
	      break;
	    case unop::F:
	      emit(KF);
	      break;
	    case unop::G:
	      emit(KG);
	      break;
	    case unop::Finish:
	      os_ << "finish";
	      need_parent = true;
	      break;
	    case unop::Closure:
	      os_ << "{";
	      in_ratexp_ = true;
	      top_level_ = true;
	      break;
	    case unop::NegClosure:
	      os_ << "!{";
	      in_ratexp_ = true;
	      top_level_ = true;
	      break;
	    }

	  if (need_parent || full_parent_)
	    openp();
	  uo->child()->accept(*this);
	  if (need_parent || full_parent_)
	    closep();

	  switch (uo->op())
	    {
	    case unop::Closure:
	    case unop::NegClosure:
	      os_ << "}";
	      in_ratexp_ = false;
	      top_level_ = false;
	      break;
	    default:
	      break;
	    }

	  if (full_parent_ && !top_level)
	    closep();
	}

	void
	visit(const automatop* ao)
	{
	  // Warning: this string isn't parsable because the automaton
	  // operators used may not be defined.
	  bool top_level = top_level_;
	  top_level_ = false;
	  if (!top_level)
	    os_ << "(";
	  os_ << ao->get_nfa()->get_name() << "(";
	  unsigned max = ao->size();
	  ao->nth(0)->accept(*this);
	  for (unsigned n = 1; n < max; ++n)
	    {
	      os_ << ",";
	      ao->nth(n)->accept(*this);
	    }
	  os_ << ")";
	  if (!top_level)
	    os_ << ")";
	}

	void
	visit(const multop* mo)
	{
	  bool top_level = top_level_;
	  top_level_ = false;
	  if (!top_level)
	    openp();
	  unsigned max = mo->size();
	  mo->nth(0)->accept(*this);
	  keyword k = KFalse;	// Initialize to something to please GCC.
	  switch (mo->op())
	    {
	    case multop::Or:
	      k = KOr;
	      break;
	    case multop::And:
	      k = in_ratexp_ ? KAndLM : KAnd;
	      break;
	    case multop::AndNLM:
	      k = KAndNLM;
	      break;
	    case multop::Concat:
	      k = KConcat;
	      break;
	    case multop::Fusion:
	      k = KFusion;
	      break;
	    }
	  assert(k != KFalse);

	  for (unsigned n = 1; n < max; ++n)
	    {
	      emit(k);
	      mo->nth(n)->accept(*this);
	    }
	  if (!top_level)
	    closep();
	}
      protected:
	std::ostream& os_;
	bool top_level_;
	bool full_parent_;
	bool in_ratexp_;
	const char** kw_;
      };

    } // anonymous

    std::ostream&
    to_string(const formula* f, std::ostream& os, bool full_parent,
	      bool ratexp)
    {
      to_string_visitor v(os, full_parent, ratexp, spot_kw);
      f->accept(v);
      return os;
    }

    std::string
    to_string(const formula* f, bool full_parent, bool ratexp)
    {
      std::ostringstream os;
      to_string(f, os, full_parent, ratexp);
      return os.str();
    }

    std::ostream&
    to_spin_string(const formula* f, std::ostream& os, bool full_parent)
    {
      // Remove xor, ->, and <-> first.
      formula* fu = unabbreviate_logic(f);
      to_string_visitor v(os, full_parent, false, spin_kw);
      fu->accept(v);
      fu->destroy();
      return os;
    }

    std::string
    to_spin_string(const formula* f, bool full_parent)
    {
      std::ostringstream os;
      to_spin_string(f, os, full_parent);
      return os.str();
    }
  }
}
