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
  class acc_mapper_common
  {
  protected:
    bdd_dict_ptr dict_;
    tgba_digraph* aut_;
    ltl::environment& env_;
    bdd neg_;

    acc_mapper_common(tgba_digraph *aut, ltl::environment& env)
      : dict_(aut->get_dict()), aut_(aut), env_(env), neg_(bddtrue)
    {
    }

  public:
    const ltl::environment& get_env() const
    {
      return env_;
    }

    // Commit all acceptance set to the automaton.
    void commit()
    {
       aut_->set_acceptance_conditions(neg_);
    }
  };

  class acc_mapper_string: public acc_mapper_common
  {
    std::unordered_map<std::string, int> map_;

  public:
    acc_mapper_string(tgba_digraph *aut,
		      ltl::environment& env
		      = ltl::default_environment::instance())
      : acc_mapper_common(aut, env)
    {
    }

    // Declare an acceptance name.
    bool declare(const std::string& name)
    {
      auto i = map_.find(name);
      if (i != map_.end())
	return true;
      auto f = env_.require(name);
      if (!f)
	return false;
      int v = dict_->register_acceptance_variable(f, aut_);
      f->destroy();
      map_[name] = v;
      neg_ &= bdd_nithvar(v);
      return true;
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


  // The acceptance sets are named using count consecutive integers.
  class acc_mapper_consecutive_int: public acc_mapper_common
  {
  protected:
    std::vector<bdd> vec_;
    std::map<int, bdd> map_;

  public:
    acc_mapper_consecutive_int(tgba_digraph *aut,
			       unsigned count,
			       ltl::environment& env =
			       ltl::default_environment::instance())
      : acc_mapper_common(aut, env), vec_(count)
    {
      std::vector<int> vmap(count);
      for (unsigned n = 0; n < count; ++n)
	{
	  std::ostringstream s;
	  s << n;
	  auto f = env.require(s.str());
	  int v = dict_->register_acceptance_variable(f, aut_);
	  f->destroy();
	  vmap[n] = v;
	  neg_ &= bdd_nithvar(v);
      }
      for (unsigned n = 0; n < count; ++n)
	{
	  int v = vmap[n];
	  vec_[n] = bdd_compose(neg_, bdd_nithvar(v), v);
	}
      commit();
    }

    std::pair<bool, bdd> lookup(unsigned n)
    {
      if (n < vec_.size())
	return std::make_pair(true, vec_[n]);
      else
	return std::make_pair(false, bddfalse);
    }
  };

  // The acceptance sets are named using count integers, but we do not
  // assume the numbers are necessarily consecutive.
  class acc_mapper_int: public acc_mapper_consecutive_int
  {
    unsigned used_;
    std::map<int, bdd> map_;

  public:
    acc_mapper_int(tgba_digraph *aut,
		   unsigned count,
		   ltl::environment& env =
		   ltl::default_environment::instance())
      : acc_mapper_consecutive_int(aut, count, env), used_(0)
    {
    }

    std::pair<bool, bdd> lookup(unsigned n)
    {
       auto p = map_.find(n);
       if (p != map_.end())
	 return std::make_pair(true, p->second);
       if (used_ < vec_.size())
	 {
	   bdd res = vec_[used_++];
	   map_[n] = res;
	   return std::make_pair(true, res);
	 }
       return std::make_pair(false, bddfalse);
    }
  };
}

#endif // SPOT_PRIV_ACCCONV_HH
