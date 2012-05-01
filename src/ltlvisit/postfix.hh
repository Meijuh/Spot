// Copyright (C) 2009, 2010, 2012  Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
// Copyright (C) 2003, 2004  Laboratoire d'Informatique de Paris 6 (LIP6),
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
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#ifndef SPOT_LTLVISIT_POSTFIX_HH
# define SPOT_LTLVISIT_POSTFIX_HH

#include "ltlast/formula.hh"
#include "ltlast/visitor.hh"

namespace spot
{
  namespace ltl
  {
    /// \brief Apply an algorithm on each node of an AST,
    /// during a postfix traversal.
    /// \ingroup ltl_visitor
    ///
    /// Override one or more of the postifix_visitor::doit methods
    /// with the algorithm to apply.
    class postfix_visitor : public visitor
    {
    public:
      postfix_visitor();
      virtual ~postfix_visitor();

      void visit(const atomic_prop* ap);
      void visit(const unop* uo);
      void visit(const binop* bo);
      void visit(const multop* mo);
      void visit(const automatop* c);
      void visit(const constant* c);
      void visit(const bunop* c);

      virtual void doit(const atomic_prop* ap);
      virtual void doit(const unop* uo);
      virtual void doit(const binop* bo);
      virtual void doit(const multop* mo);
      virtual void doit(const automatop* mo);
      virtual void doit(const constant* c);
      virtual void doit(const bunop* c);
      virtual void doit_default(const formula* f);
    };
  }
}

#endif // SPOT_LTLVISIT_POSTFIX_HH
