// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et Developpement de
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

#include <unordered_set>
#include <algorithm>

#include "ltlast/allnodes.hh"
#include "ltlvisit/apcollect.hh"
#include "ltlvisit/clone.hh"
#include "ltlvisit/mutation.hh"
#include "ltlvisit/length.hh"
#include "misc/hash.hh"

#define Implies_(x, y) \
  spot::ltl::binop::instance(spot::ltl::binop::Implies, (x), (y))
#define And_(x, y) \
  spot::ltl::multop::instance(spot::ltl::multop::And, (x), (y))
#define AndRat_(x, y) \
  spot::ltl::multop::instance(spot::ltl::multop::AndRat, (x), (y))
#define AndNLM_(x) \
  spot::ltl::multop::instance(spot::ltl::multop::AndNLM, (x))
#define Concat_(x, y) \
  spot::ltl::multop::instance(spot::ltl::multop::Concat, (x), (y))
#define Not_(x) \
  spot::ltl::unop::instance(spot::ltl::unop::Not, (x))

namespace spot
{
  namespace ltl
  {
    namespace
    {
      class replace_visitor : public clone_visitor
      {
      public:
	void visit(const atomic_prop* ap)
	{
	  if (ap == ap1_)
	    result_ = ap2_->clone();
	  else
	    result_ = ap->clone();
	}

	const formula*
	replace(const formula* f,
		const atomic_prop* ap1,
		const atomic_prop* ap2)
	{
	  ap1_ = ap1;
	  ap2_ = ap2;
	  return recurse(f);
	}

      private:
	const atomic_prop* ap1_;
	const atomic_prop* ap2_;
      };

      typedef std::vector<const formula*> vec;
      class mutation_visitor : public clone_visitor
      {
      public:
        mutation_visitor(const formula* f, unsigned opts) : f_(f), opts_(opts)
        {
        }

        void visit(const atomic_prop* ap)
        {
          result_ = 0;
          if (opts_ & Mut_Ap2Const)
            {
              if (mutation_counter_-- == 0)
                result_ = constant::true_instance();
              if (mutation_counter_-- == 0)
                result_ = constant::false_instance();
            }
          if (!result_)
            result_ = ap->clone();
        }

        void visit(const unop* uo)
        {
          result_ = 0;
          if (opts_ & Mut_Remove_Ops)
            {
              if ((uo->op() == unop::G
                   || uo->op() == unop::F
                   || uo->op() == unop::X
                   || uo->op() == unop::Not)
                  && mutation_counter_-- == 0)
                result_ = uo->child()->clone();
            }
          if (!result_)
            {
              if (mutation_counter_ < 0)
                result_ = uo->clone();
              else
                {
                  result_ = unop::instance(uo->op(), recurse(uo->child()));
                }
            }
        }

        void visit(const binop* bo)
        {
          const formula* first = bo->first();
          const formula* second = bo->second();
          result_ = 0;
	  auto op = bo->op();
	  bool left_is_sere = op == binop::EConcat
	    || op == binop::EConcatMarked
	    || op == binop::UConcat;

          if (opts_ & Mut_Remove_Ops && mutation_counter_-- == 0)
	    {
	      if (!left_is_sere)
		result_ = first->clone();
	      else if (op == binop::UConcat)
		result_ = unop::instance(unop::NegClosure, first->clone());
	      else // EConcat or EConcatMarked
		result_ = unop::instance(unop::Closure, first->clone());
	    }
          if (opts_ & Mut_Remove_Ops && mutation_counter_-- == 0)
            result_ = second->clone();
          if (opts_ & Mut_Rewrite_Ops)
            {
              switch (op)
                {
                case binop::U:
                  if (mutation_counter_-- == 0)
                    result_ = binop::instance(binop::W, first->clone(),
					      second->clone());
                  break;
                case binop::M:
                  if (mutation_counter_-- == 0)
                    result_ = binop::instance(binop::R, first->clone(),
					      second->clone());
                  if (mutation_counter_-- == 0)
                    result_ = binop::instance(binop::U, second->clone(),
					      first->clone());
                  break;
                case binop::R:
                  if (mutation_counter_-- == 0)
                    result_ = binop::instance(binop::W, second->clone(),
					      first->clone());
                  break;
                default:
                  break;
                }
            }
          if (opts_ & Mut_Split_Ops)
            {
              switch (op)
                {
                case binop::Equiv:
                  if (mutation_counter_-- == 0)
                    result_ = Implies_(first->clone(), second->clone());
                  if (mutation_counter_-- == 0)
                    result_ = Implies_(second->clone(), first->clone());
                  if (mutation_counter_-- == 0)
                    result_ = And_(first->clone(), second->clone());
                  if (mutation_counter_-- == 0)
		    {
		      // Negate the two argument sequentially (in this
		      // case right before left, otherwise different
		      // compilers will make different choices.
		      auto right = Not_(second->clone());
		      result_ = And_(Not_(first->clone()), right);
		    }
                  break;
                case binop::Xor:
                  if (mutation_counter_-- == 0)
                    result_ = And_(first->clone(), Not_(second->clone()));
                  if (mutation_counter_-- == 0)
                    result_ = And_(Not_(first->clone()), second->clone());
                  break;
                default:
                  break;
                }
            }
          if (!result_)
            {
              if (mutation_counter_ < 0)
		{
		  result_ = bo->clone();
		}
              else
		{
		  // For historical reasons, we evaluate the right
		  // side before the left one.  The other order would
		  // be OK as well but require changing the test
		  // suite.  Evaluating both sides during the call to
		  // instance() is incorrect, because each compiler
		  // could decide of a different order.
		  auto right = recurse(second);
		  result_ = binop::instance(op, recurse(first), right);
		}
            }
        }

        void visit(const bunop* bu)
        {
          const formula* c = bu->child()->clone();
          result_ = nullptr;
	  auto op = bu->op();

          if (opts_ & Mut_Remove_Ops && mutation_counter_-- == 0)
            result_ = c;
          if (opts_ & Mut_Simplify_Bounds)
            {
	      auto min = bu->min();
	      auto max = bu->max();
	      if (min > 0)
		{
		  if (mutation_counter_-- == 0)
		    result_ = bunop::instance(op, c, min - 1, max);
		  if (mutation_counter_-- == 0)
		    result_ = bunop::instance(op, c, 0, max);
		}
	      if (max != bunop::unbounded)
		{
		  if (max > min && mutation_counter_-- == 0)
		    result_ = bunop::instance(op, c, min, max - 1);
		  if (mutation_counter_-- == 0)
		    result_ = bunop::instance(op, c, min, bunop::unbounded);
		}
            }
          if (!result_)
            {
              c->destroy();
              if (mutation_counter_ < 0)
                result_ = bu->clone();
              else
                result_ = bunop::instance(op, recurse(c), bu->min(), bu->max());
	    }
        }

        void visit(const multop* mo)
        {
          int mos = mo->size();
          int i;
          result_ = 0;

          if (opts_ & Mut_Remove_Multop_Operands)
            {
              for (i = 0; i < mos; ++i)
                if (mutation_counter_-- == 0)
                  result_ = mo->all_but(i);
            }

          if (opts_ & Mut_Split_Ops && mo->op() == multop::AndNLM)
            {
	      if (mutation_counter_ >= 0 && mutation_counter_ < 2 * (mos - 1))
		{
		  vec* v1 = new vec();
		  vec* v2 = new vec();
		  v1->push_back(mo->nth(0)->clone());
		  bool reverse = false;
		  i = 1;
		  while (i < mos)
		    {
		      if (mutation_counter_-- == 0)
			break;
		      if (mutation_counter_-- == 0)
			{
			  reverse = true;
			  break;
			}
		      v1->push_back(mo->nth(i++)->clone());
		    }
		  for (; i < mos; ++i)
		    v2->push_back(mo->nth(i)->clone());
		  const formula* tstar =
		    bunop::instance(bunop::Star, constant::true_instance(),
				    0,
				    bunop::unbounded);
		  const formula* first = AndNLM_(v1);
		  const formula* second = AndNLM_(v2);
		  if (!reverse)
		    result_ = AndRat_(Concat_(first, tstar), second);
		  else
		    result_ = AndRat_(Concat_(second, tstar), first);
		}
	      else
		mutation_counter_ -= 2 * (mos - 1);
            }

          if (!result_)
            {
              if (mutation_counter_ < 0)
                result_ = mo->clone();
              else
                {
		  vec* v = new vec();
                  for (i = 0; i < mos; ++i)
                    v->push_back(recurse(mo->nth(i)));
                  result_ = multop::instance(mo->op(), v);
                }
            }
        }

        const formula*
        recurse(const formula* f)
        {
          f->accept(*this);
          return result_;
        }

        const formula*
        get_mutation(int n)
        {
          mutation_counter_ = n;
          const formula* mut = recurse(f_);
          if (mut == f_)
	    {
	      mut->destroy();
	      return 0;
	    }
	  return mut;
        }

      private:
        const formula* f_;
        int mutation_counter_ = 0;
	unsigned opts_;
      };

      bool
      formula_length_less_than(const formula* left, const formula* right)
      {
	assert(left);
	assert(right);
	if (left == right)
	  return false;
	return length(left) < length(right);
      }

      typedef std::set<const formula*, formula_ptr_less_than> fset_t;

      void
      single_mutation_rec(const formula* f, fset_t& mutations, unsigned opts,
			  unsigned& n, unsigned m)
      {
	if (m == 0)
	  {
	    if (mutations.insert(f).second)
	      {
		f->clone();
		--n;
	      }
	  }
	else
	  {
	    const formula* mut(nullptr);
	    int i = 0;
	    mutation_visitor mv(f, opts);
	    while (n > 0 && (mut = mv.get_mutation(i++)))
	      {
		single_mutation_rec(mut, mutations, opts, n, m - 1);
		mut->destroy();
	      }
	  }
      }

      void
      replace_ap_rec(const formula* f, fset_t& mutations, unsigned opts,
		     unsigned& n, unsigned m)
      {
	if (m == 0)
	  {
	    if (mutations.insert(f).second)
	      {
		f->clone();
		--n;
	      }
	  }
	else
	  {
	    if (!n)
	      return;
	    replace_visitor rv;
	    auto aps =
	      std::unique_ptr<atomic_prop_set>(atomic_prop_collect(f));
	    for (auto ap1: *aps)
	      for (auto ap2: *aps)
		{
		  if (ap1 == ap2)
		    continue;
		  auto mut = rv.replace(f, ap1, ap2);
		  replace_ap_rec(mut, mutations, opts, n, m - 1);
		  mut->destroy();
		  if (!n)
		    return;
		}
	  }
      }
    }

    std::vector<const formula*>
    mutate(const formula* f, unsigned opts, unsigned max_output,
	   unsigned mutation_count, bool sort)
    {
      fset_t mutations;
      single_mutation_rec(f, mutations, opts, max_output, mutation_count);
      if (opts & Mut_Remove_One_Ap)
	replace_ap_rec(f, mutations, opts, max_output, mutation_count);

      vec res(mutations.begin(), mutations.end());
      if (sort)
	std::sort(res.begin(), res.end(), formula_length_less_than);
      return res;
    }
  }
}
