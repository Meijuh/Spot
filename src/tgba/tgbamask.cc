// -*- coding: utf-8 -*-
// Copyright (C) 2013, 2014 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
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

#include "tgbamask.hh"
#include <vector>

namespace spot
{
  namespace
  {
    struct transition
    {
      const state* dest;
      bdd cond;
      acc_cond::mark_t acc;
    };
    typedef std::vector<transition> transitions;

    struct succ_iter_filtered: public twa_succ_iterator
    {
      ~succ_iter_filtered()
      {
	for (auto& t: trans_)
	  t.dest->destroy();
      }

      bool first()
      {
	it_ = trans_.begin();
	return it_ != trans_.end();
      }

      bool next()
      {
	++it_;
	return it_ != trans_.end();
      }

      bool done() const
      {
	return it_ == trans_.end();
      }

      state* current_state() const
      {
	return it_->dest->clone();
      }

      bdd current_condition() const
      {
	return it_->cond;
      }

      acc_cond::mark_t current_acceptance_conditions() const
      {
	return it_->acc;
      }

      transitions trans_;
      transitions::const_iterator it_;
    };

    /// \ingroup tgba_on_the_fly_algorithms
    /// \brief A masked TGBA (abstract).
    ///
    /// Ignores some states from a TGBA.  What state are preserved or
    /// ignored is controlled by the wanted() method.
    ///
    /// This is an abstract class. You should inherit from it and
    /// supply a wanted() method to specify which states to keep.
    class tgba_mask: public twa_proxy
    {
    protected:
      /// \brief Constructor.
      /// \param masked The automaton to mask
      /// \param init Any state to use as initial state. This state will be
      /// destroyed by the destructor.
      tgba_mask(const const_twa_ptr& masked, const state* init = 0):
	twa_proxy(masked),
	init_(init)
      {
	if (!init)
	  init_ = masked->get_init_state();
      }


    public:
      virtual ~tgba_mask()
      {
	init_->destroy();
      }

      virtual state* get_init_state() const
      {
	return init_->clone();
      }

      virtual twa_succ_iterator*
      succ_iter(const state* local_state) const
      {
	succ_iter_filtered* res;
	if (iter_cache_)
	  {
	    res = down_cast<succ_iter_filtered*>(iter_cache_);
	    res->trans_.clear();
	    iter_cache_ = nullptr;
	  }
	else
	  {
	    res = new succ_iter_filtered;
	  }
	for (auto it: original_->succ(local_state))
	  {
	    const spot::state* s = it->current_state();
	    auto acc = it->current_acceptance_conditions();
	    if (!wanted(s, acc))
	      {
		s->destroy();
		continue;
	      }
	    res->trans_.emplace_back
	      (transition {s, it->current_condition(), acc});
	  }
	return res;
      }

      virtual bool wanted(const state* s, acc_cond::mark_t acc) const = 0;

    protected:
      const state* init_;
    };

    class tgba_mask_keep: public tgba_mask
    {
      const state_set& mask_;
    public:
      tgba_mask_keep(const const_twa_ptr& masked,
		     const state_set& mask,
		     const state* init)
	: tgba_mask(masked, init),
	  mask_(mask)
      {
      }

      bool wanted(const state* s, const acc_cond::mark_t) const
      {
	state_set::const_iterator i = mask_.find(s);
	return i != mask_.end();
      }
    };

    class tgba_mask_ignore: public tgba_mask
    {
      const state_set& mask_;
    public:
      tgba_mask_ignore(const const_twa_ptr& masked,
		       const state_set& mask,
		       const state* init)
	: tgba_mask(masked, init),
	  mask_(mask)
      {
      }

      bool wanted(const state* s, const acc_cond::mark_t) const
      {
	state_set::const_iterator i = mask_.find(s);
	return i == mask_.end();
      }
    };

    class tgba_mask_acc_ignore: public tgba_mask
    {
      unsigned mask_;
    public:
      tgba_mask_acc_ignore(const const_twa_ptr& masked,
			   unsigned mask,
			   const state* init)
	: tgba_mask(masked, init),
	  mask_(mask)
      {
      }

      bool wanted(const state*, const acc_cond::mark_t acc) const
      {
	return !acc.has(mask_);
      }
    };

  }

  const_twa_ptr
  build_tgba_mask_keep(const const_twa_ptr& to_mask,
		       const state_set& to_keep,
		       const state* init)
  {
    return std::make_shared<tgba_mask_keep>(to_mask, to_keep, init);
  }

  const_twa_ptr
  build_tgba_mask_ignore(const const_twa_ptr& to_mask,
			 const state_set& to_ignore,
			 const state* init)
  {
    return std::make_shared<tgba_mask_ignore>(to_mask, to_ignore, init);
  }

  const_twa_ptr
  build_tgba_mask_acc_ignore(const const_twa_ptr& to_mask,
			     unsigned to_ignore,
			     const state* init)
  {
    return std::make_shared<tgba_mask_acc_ignore>(to_mask, to_ignore, init);
  }

}
