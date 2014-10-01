// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2011, 2012, 2014 Laboratoire de Recherche et
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

#include "tgbasl.hh"
#include "bddprint.hh"

namespace spot
{
  namespace
  {
    class state_tgbasl: public state
    {
    public:
      state_tgbasl(state* s, bdd cond) : s_(s), cond_(cond)
      {
      }

      virtual
      ~state_tgbasl()
      {
        s_->destroy();
      }

      virtual int
      compare(const state* other) const
      {
        const state_tgbasl* o =
          down_cast<const state_tgbasl*>(other);
        assert(o);
        int res = s_->compare(o->real_state());
        if (res != 0)
          return res;
        return cond_.id() - o->cond_.id();
      }

      virtual size_t
      hash() const
      {
        return wang32_hash(s_->hash()) ^ wang32_hash(cond_.id());
      }

      virtual
      state_tgbasl* clone() const
      {
        return new state_tgbasl(*this);
      }

      state*
      real_state() const
      {
        return s_;
      }

      bdd
      cond() const
      {
        return cond_;
      }

    private:
      state* s_;
      bdd cond_;
    };

    class tgbasl_succ_iterator : public tgba_succ_iterator
    {
    public:
      tgbasl_succ_iterator(tgba_succ_iterator* it, const state_tgbasl* state,
			   bdd_dict_ptr d, bdd atomic_propositions)
        : it_(it), state_(state), aps_(atomic_propositions), d_(d)
      {
      }

      virtual
      ~tgbasl_succ_iterator()
      {
        delete it_;
      }

      // iteration

      bool
      first()
      {
        loop_ = false;
        done_ = false;
        need_loop_ = true;
        if (it_->first())
          {
            cond_ = it_->current_condition();
            next_edge();
          }
        return true;
      }

      bool
      next()
      {
        if (cond_ != bddfalse)
          {
            next_edge();
            return true;
          }
        if (!it_->next())
          {
            if (loop_ || !need_loop_)
              done_ = true;
            loop_ = true;
            return !done_;
          }
        else
          {
            cond_ = it_->current_condition();
            next_edge();
            return true;
          }
      }

      bool
      done() const
      {
        return it_->done() && done_;
      }

      // inspection

      state_tgbasl*
      current_state() const
      {
        if (loop_)
          return new state_tgbasl(state_->real_state(), state_->cond());
        return new state_tgbasl(it_->current_state(), one_);
      }

      bdd
      current_condition() const
      {
        if (loop_)
          return state_->cond();
        return one_;
      }

      acc_cond::mark_t
      current_acceptance_conditions() const
      {
        if (loop_)
          return 0U;
        return it_->current_acceptance_conditions();
      }

    private:
      void
      next_edge()
      {
        one_ = bdd_satoneset(cond_, aps_, bddtrue);
        cond_ -= one_;
        if (need_loop_ && (state_->cond() == one_)
            && (state_ == it_->current_state()))
          need_loop_ = false;
      }

      tgba_succ_iterator* it_;
      const state_tgbasl* state_;
      bdd cond_;
      bdd one_;
      bdd aps_;
      bdd_dict_ptr d_;
      bool loop_;
      bool need_loop_;
      bool done_;
    };
  }

  tgbasl::tgbasl(const const_tgba_ptr& a, bdd atomic_propositions)
    : tgba(a->get_dict()), a_(a), aps_(atomic_propositions)
  {
    auto d = get_dict();
    d->register_all_propositions_of(&a_, this);
    assert(acc_.num_sets() == 0);
    acc_.add_sets(a_->acc().num_sets());
  }

  tgbasl::~tgbasl()
  {
    get_dict()->unregister_all_my_variables(this);
  }

  state*
  tgbasl::get_init_state() const
  {
    return new state_tgbasl(a_->get_init_state(), bddfalse);
  }

  tgba_succ_iterator*
  tgbasl::succ_iter(const state* state) const
  {
    const state_tgbasl* s = down_cast<const state_tgbasl*>(state);
    assert(s);
    return new tgbasl_succ_iterator(a_->succ_iter(s->real_state()), s,
				    a_->get_dict(), aps_);
  }

  bdd
  tgbasl::compute_support_conditions(const state*) const
  {
    return bddtrue;
  }

  std::string
  tgbasl::format_state(const state* state) const
  {
    const state_tgbasl* s = down_cast<const state_tgbasl*>(state);
    assert(s);
    return (a_->format_state(s->real_state())
            + ", "
            + bdd_format_formula(a_->get_dict(), s->cond()));
  }
}
