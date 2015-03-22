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

#include "tgba.hh"
#include "tgbagraph.hh"
#include "tgbaalgos/gtec/gtec.hh"
#include "tgbaalgos/remfin.hh"
#include <utility>

namespace spot
{
  tgba::tgba(const bdd_dict_ptr& d)
    : iter_cache_(nullptr),
      dict_(d),
      last_support_conditions_input_(0)
  {
    props = 0U;
  }

  tgba::~tgba()
  {
    if (last_support_conditions_input_)
      last_support_conditions_input_->destroy();
    delete iter_cache_;
    release_named_properties();
  }

  bdd
  tgba::support_conditions(const state* state) const
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
  tgba::project_state(const state* s,
		      const const_tgba_ptr& t) const
  {
    if (t.get() == this)
      return s->clone();
    return 0;
  }

  std::string
  tgba::transition_annotation(const tgba_succ_iterator*) const
  {
    return "";
  }

  bool
  tgba::is_empty() const
  {
    // FIXME: This should be improved based on properties of the
    // automaton.  For instance we do not need couvreur99 is we know
    // the automaton is weak.
    auto a = shared_from_this();
    if (a->acc().uses_fin_acceptance())
      {
	auto aa = std::dynamic_pointer_cast<const tgba_digraph>(a);
	if (!aa)
	  aa = make_tgba_digraph(a, prop_set::all());
	a = remove_fin(aa);
      }
    return !couvreur99(a)->check();
  }

  void
  tgba::set_named_prop(std::string s,
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
  tgba::get_named_prop_(std::string s) const
  {
    auto i = named_prop_.find(s);
    if (i == named_prop_.end())
      return nullptr;
    return i->second.first;
  }




}
