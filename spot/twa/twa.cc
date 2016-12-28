// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2014-2016 Laboratoire de Recherche et Developpement de
// l'EPITA (LRDE).
// Copyright (C) 2003, 2004, 2005 Laboratoire d'Informatique de Paris 6 (LIP6),
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
#include <spot/twaalgos/couvreurnew.hh>
#include <spot/twaalgos/word.hh>
#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/alternation.hh>
#include <spot/twa/twaproduct.hh>
#include <utility>

namespace spot
{
  twa::twa(const bdd_dict_ptr& d)
    : iter_cache_(nullptr),
      dict_(d)
  {
    props = 0U;
    bddaps_ = bddtrue;
  }

  twa::~twa()
  {
    delete iter_cache_;
    release_named_properties();
    get_dict()->unregister_all_my_variables(this);
  }


  namespace
  {
    // Remove Fin-acceptance and alternation.
    const_twa_ptr remove_fin_maybe(const const_twa_ptr& a)
    {
      auto aa = std::dynamic_pointer_cast<const twa_graph>(a);
      if ((!aa || !aa->is_alternating()) && !a->acc().uses_fin_acceptance())
        return a;
      if (!aa)
        aa = make_twa_graph(a, twa::prop_set::all());
      return remove_fin(remove_alternation(aa));
    }
  }

  state*
  twa::project_state(const state* s,
                      const const_twa_ptr& t) const
  {
    if (t.get() == this)
      return s->clone();
    return nullptr;
  }

  bool
  twa::is_empty() const
  {
    return !couvreur99_new_check(remove_fin_maybe(shared_from_this()));
  }

  twa_run_ptr
  twa::accepting_run() const
  {
    if (acc().uses_fin_acceptance())
      throw std::runtime_error("twa::accepting_run() does not work with "
                               "Fin acceptance (but twa:is_empty() and "
                               "twa::accepting_run() can)");
    auto res = couvreur99_new_check(shared_from_this());
    if (!res)
      return nullptr;
    return res->accepting_run();
  }

  twa_word_ptr
  twa::accepting_word() const
  {
    if (auto run = remove_fin_maybe(shared_from_this())->accepting_run())
      {
        auto w = make_twa_word(run->reduce());
        w->simplify();
        return w;
      }
    else
      {
        return nullptr;
      }
  }

  bool
  twa::intersects(const_twa_ptr other) const
  {
    auto a1 = remove_fin_maybe(shared_from_this());
    auto a2 = remove_fin_maybe(other);
    return !otf_product(a1, a2)->is_empty();
  }

  twa_run_ptr
  twa::intersecting_run(const_twa_ptr other, bool from_other) const
  {
    auto a = shared_from_this();
    if (from_other)
      other = remove_fin_maybe(other);
    else
      a = remove_fin_maybe(a);
    auto run = otf_product(a, other)->accepting_run();
    if (!run)
      return nullptr;
    return run->project(from_other ? other : a);
  }

  twa_word_ptr
  twa::intersecting_word(const_twa_ptr other) const
  {
    auto a1 = remove_fin_maybe(shared_from_this());
    auto a2 = remove_fin_maybe(other);
    return otf_product(a1, a2)->accepting_word();
  }

  void
  twa::set_named_prop(std::string s, std::nullptr_t)
  {
    auto p = named_prop_.find(s);
    if (p == named_prop_.end())
      return;
    p->second.second(p->second.first);
    named_prop_.erase(p);
    return;
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

  void
  twa::unregister_ap(int b)
  {
    auto d = get_dict();
    assert(d->bdd_map[b].type == bdd_dict::var);
    auto pos = std::find(aps_.begin(), aps_.end(), d->bdd_map[b].f);
    assert(pos != aps_.end());
    aps_.erase(pos);
    d->unregister_variable(b, this);
    bddaps_ = bdd_exist(bddaps_, bdd_ithvar(b));
  }



}
