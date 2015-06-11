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

#include "totgba.hh"
#include "remfin.hh"
#include "cleanacc.hh"
#include "twa/twagraph.hh"

namespace spot
{
  namespace
  {
    typedef std::vector<acc_cond::mark_t> terms_t;

    terms_t cnf_terms(const acc_cond::acc_code& code)
    {
      assert(!code.empty());
      terms_t res;
      auto pos = &code.back();
      auto end = &code.front();
      if (pos->op == acc_cond::acc_op::And)
	--pos;
      while (pos >= end)
	{
	  auto term_end = pos - 1 - pos->size;
	  if (pos->op == acc_cond::acc_op::Or)
	    --pos;
	  acc_cond::mark_t m = 0U;
	  while (pos > term_end)
	    {
	      assert(pos->op == acc_cond::acc_op::Inf);
	      m |= pos[-1].mark;
	      pos -= 2;
	    }
	  res.push_back(m);
	}
      return res;
    }
  }



  /// \brief Take an automaton with any acceptance condition and return
  /// an equivalent Generalized Büchi automaton.
  twa_graph_ptr
  to_generalized_buchi(const const_twa_graph_ptr& aut)
  {
    auto res = remove_fin(cleanup_acceptance(aut));
    if (res->acc().is_generalized_buchi())
      return res;

    auto cnf = res->get_acceptance().to_cnf();
    // If we are very lucky, building a CNF actually gave us a GBA...
    if (cnf.empty() ||
	(cnf.size() == 2 && cnf.back().op == acc_cond::acc_op::Inf))
      {
	res->set_acceptance(res->num_sets(), cnf);
	cleanup_acceptance_here(res);
	return res;
      }

    // Handle false specifically.  We want the output
    // an automaton with Acceptance: t, that has a single
    // state without successor.
    if (cnf.size() == 2 && cnf.back().op == acc_cond::acc_op::Fin)
      {
	assert(cnf.front().mark == 0U);
	res = make_twa_graph(aut->get_dict());
	res->set_init_state(res->new_state());
	res->prop_state_based_acc();
	res->prop_inherently_weak();
	res->prop_deterministic();
	res->prop_stutter_invariant();
	return res;
      }

    auto terms = cnf_terms(cnf);
    unsigned nterms = terms.size();
    assert(nterms > 0);
    res->set_generalized_buchi(nterms);

    for (auto& t: res->edges())
      {
	acc_cond::mark_t cur_m = t.acc;
	acc_cond::mark_t new_m = 0U;
	for (unsigned n = 0; n < nterms; ++n)
	  if (cur_m & terms[n])
	    new_m.set(n);
	t.acc = new_m;
      }
    return res;
  }
}
