// Copyright (C) 2009, 2010 Laboratoire de Recherche et D�veloppement
// de l'Epita (LRDE).
// Copyright (C) 2003, 2004 Laboratoire d'Informatique de Paris 6 (LIP6),
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

/// \file ltlast/constant.hh
/// \brief LTL constants
#ifndef SPOT_LTLAST_CONSTANT_HH
# define SPOT_LTLAST_CONSTANT_HH

#include "formula.hh"

namespace spot
{
  namespace ltl
  {

    /// \brief A constant (True or False)
    /// \ingroup ltl_ast
    class constant : public formula
    {
    public:
      enum type { False, True, EmptyWord };
      virtual void accept(visitor& v);
      virtual void accept(const_visitor& v) const;

      /// Return the value of the constant.
      type val() const;
      /// Return the value of the constant as a string.
      const char* val_name() const;

      virtual std::string dump() const;

      /// Get the sole instance of spot::ltl::constant::constant(True).
      static constant* true_instance() { return &true_instance_; }
      /// Get the sole instance of spot::ltl::constant::constant(False).
      static constant* false_instance() { return &false_instance_; }
      /// Get the sole instance of spot::ltl::constant::constant(EmptyWord).
      static constant* empty_word_instance() { return &empty_word_instance_; }

    protected:
      constant(type val);
      virtual ~constant();

    private:
      type val_;

      static constant true_instance_;
      static constant false_instance_;
      static constant empty_word_instance_;
      // If you add new constants here, be sure to update the
      // formula::formula() constructor.
    };

  }
}

#endif // SPOT_LTLAST_CONSTANT_HH
