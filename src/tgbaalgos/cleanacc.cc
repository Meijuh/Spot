// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement
// de l'Epita.
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

#include "tgbaalgos/cleanacc.hh"

namespace spot
{
  namespace
  {
    acc_cond::acc_code strip(const acc_cond& acc,
			     const acc_cond::acc_word* pos,
			     acc_cond::mark_t useless)
    {
      auto start = pos - pos->size;
      switch (pos->op)
	{
	case acc_cond::acc_op::And:
	  {
	    --pos;
	    acc_cond::acc_code res;
	    do
	      {
		auto tmp = strip(acc, pos, useless);
		tmp.append_and(std::move(res));
		std::swap(tmp, res);
		pos -= pos->size + 1;
	      }
	    while (pos > start);
	    return res;
	  }
	case acc_cond::acc_op::Or:
	  {
	    --pos;
	    acc_cond::acc_code res = acc.fin(0); // f
	    do
	      {
		auto tmp = strip(acc, pos, useless);
		tmp.append_or(std::move(res));
		std::swap(tmp, res);
		pos -= pos->size + 1;
	      }
	    while (pos > start);
	    return res;
	  }
	case acc_cond::acc_op::Fin:
	  if (pos[-1].mark & useless)
	    return acc.inf(0U);	// t
	  return acc.fin(acc.strip(pos[-1].mark, useless));
	case acc_cond::acc_op::Inf:
	  if (pos[-1].mark & useless)
	    return acc.fin(0U);	// f
	  return acc.inf(acc.strip(pos[-1].mark, useless));
	case acc_cond::acc_op::FinNeg:
	case acc_cond::acc_op::InfNeg:
	  SPOT_UNREACHABLE();
	  return acc_cond::acc_code{};
	}
      SPOT_UNREACHABLE();
      return acc_cond::acc_code{};
    }
  }

  void cleanup_acceptance(tgba_digraph_ptr& aut)
  {
    auto& acc = aut->acc();
    if (acc.num_sets() == 0)
      return;

    auto& c = aut->get_acceptance();
    acc_cond::mark_t used_in_cond = 0U;
    if (!c.is_true())
      {
	auto pos = &c.back();
	auto end = &c.front();
	while (pos > end)
	  {
	    switch (pos->op)
	      {
	      case acc_cond::acc_op::And:
	      case acc_cond::acc_op::Or:
		--pos;
		break;
	      case acc_cond::acc_op::Fin:
	      case acc_cond::acc_op::Inf:
	      case acc_cond::acc_op::FinNeg:
	      case acc_cond::acc_op::InfNeg:
		used_in_cond |= pos[-1].mark;
		pos -= 2;
		break;
	      }
	  }
      }

    acc_cond::mark_t used_in_aut = 0U;
    for (auto& t: aut->transitions())
      used_in_aut |= t.acc;

    auto useful = used_in_aut & used_in_cond;

    auto useless = acc.comp(useful);

    if (!useless)
      return;

    // Remove useless marks from the automaton
    for (auto& t: aut->transitions())
      t.acc = acc.strip(t.acc, useless);

    // Remove useless marks from the acceptance condition
    acc_cond::acc_code newc;
    if (c.is_true() || c.is_false())
      newc = c;
    else
      newc = strip(acc, &c.back(), useless);

    aut->set_acceptance(useful.count(), newc);
  }

}
