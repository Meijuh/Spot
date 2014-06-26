// -*- coding: utf-8 -*-
// Copyright (C) 2014  Laboratoire de Recherche et Developpement de
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

#ifndef SPOT_PRIV_ACCMAP_HH
# define SPOT_PRIV_ACCMAP_HH

#include <bdd.h>
#include "misc/hash.hh"
#include "ltlast/formula.hh"
#include "ltlenv/defaultenv.hh"
#include "tgba/tgbagraph.hh"

namespace spot
{
  class acc_mapper
  {
    bdd_dict* dict_;
    tgba_digraph* aut_;
    ltl::environment& env_;
    std::unordered_map<std::string, int> map_;
    bdd neg_;

  public:
    acc_mapper(tgba_digraph *aut,
	       ltl::environment& env = ltl::default_environment::instance())
      : dict_(aut->get_dict()), aut_(aut), env_(env), neg_(bddtrue)
    {
    }

    const ltl::environment& get_env() const
    {
      return env_;
    }

    // Declare an acceptance name.
    bool declare(const std::string& name)
    {
      auto i = map_.find(name);
      if (i != map_.end())
	return true;
      const ltl::formula* f = env_.require(name);
      if (!f)
	return false;
      int v = dict_->register_acceptance_variable(f, aut_);
      f->destroy();
      map_[name] = v;
      neg_ &= bdd_nithvar(v);
      return true;
    }

    // Commit all acceptance set to the automaton.
    void commit()
    {
       aut_->set_acceptance_conditions(neg_);
    }

    std::pair<bool, bdd> lookup(std::string name) const
    {
       auto p = map_.find(name);
       if (p == map_.end())
	 return std::make_pair(false, bddfalse);
       return std::make_pair(true, bdd_compose(neg_,
					       bdd_nithvar(p->second),
					       p->second));
    }

  };

}

#endif // SPOT_PRIV_ACCCONV_HH
