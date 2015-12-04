// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include <spot/twaalgos/emptiness.hh>

namespace spot
{
  class bdd_dict;

  /// \brief An infinite word stored as a lasso.
  struct SPOT_API twa_word final
  {
    twa_word(const twa_run_ptr run);
    ~twa_word()
    {
      dict_->unregister_all_my_variables(this);
    }

    void simplify();

    typedef std::list<bdd> seq_t;
    seq_t prefix;
    seq_t cycle;

    bdd_dict_ptr get_dict() const
    {
      return dict_;
    }

    SPOT_API
    friend std::ostream& operator<<(std::ostream& os, const twa_word& w);
  private:
    bdd_dict_ptr dict_;
  };

}
