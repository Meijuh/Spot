// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2014, 2015 Laboratoire de Recherche et Developpement de
// l'EPITA (LRDE).
// Copyright (C) 2003, 2004, 2005  Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include <spot/twa/twa.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/gtec/gtec.hh>
#include <spot/twaalgos/remfin.hh>
#include <utility>

namespace spot
{
  twa::twa(const bdd_dict_ptr& d)
    : iter_cache_(nullptr),
      dict_(d),
      last_support_conditions_input_(nullptr)
  {
    props = 0U;
    bddaps_ = bddtrue;
  }

  twa::~twa()
  {
    if (last_support_conditions_input_)
      last_support_conditions_input_->destroy();
    delete iter_cache_;
    release_named_properties();
  }

  bdd
  twa::support_conditions(const state* state) const
  {
    if (!last_support_conditions_input_
	|| last_support_conditions_input_->compare(state) != 0)
      {
	last_support_conditions_output_ = compute_support_conditions(state);
	if (last_support_conditions_input_)
	  last_support_conditions_input_->destroy();
	last_support_conditions_input_ = state->clone();
      }
    return last_support_conditions_output_;
  }

  state*
  twa::project_state(const state* s,
		      const const_twa_ptr& t) const
  {
    if (t.get() == this)
      return s->clone();
    return nullptr;
  }

  std::string
  twa::transition_annotation(const twa_succ_iterator*) const
  {
    return "";
  }

  bool
  twa::is_empty() const
  {
    // FIXME: This should be improved based on properties of the
    // automaton.  For instance we do not need couvreur99 is we know
    // the automaton is weak.
    auto a = shared_from_this();
    if (a->acc().uses_fin_acceptance())
      {
	auto aa = std::dynamic_pointer_cast<const twa_graph>(a);
	if (!aa)
	  aa = make_twa_graph(a, prop_set::all());
	a = remove_fin(aa);
      }
    return !couvreur99(a)->check();
  }

  void
  twa::set_named_prop(std::string s,
		      void* val, std::function<void(void*)> destructor)
  {
    auto p = named_prop_.emplace(std::piecewise_construct,
				 std::forward_as_tuple(s),
				 std::forward_as_tuple(val, destructor));
    if (!p.second)
      {
	p.first->second.second(p.first->second.first);
	p.first->second = std::make_pair(val, destructor);
      }
  }

  void*
  twa::get_named_prop_(std::string s) const
  {
    auto i = named_prop_.find(s);
    if (i == named_prop_.end())
      return nullptr;
    return i->second.first;
  }




}
