// -*- coding: utf-8 -*-
// Copyright (C) 2015, 2016, 2017 Laboratoire de Recherche et
// Développement de l'Epita.
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

#include <spot/twaalgos/totgba.hh>
#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twa/twagraph.hh>
#include <deque>
#include <tuple>

namespace spot
{
  namespace
  {
    struct st2gba_state
    {
      acc_cond::mark_t pend;
      unsigned s;

      st2gba_state(unsigned st, acc_cond::mark_t bv = -1U):
        pend(bv), s(st)
      {
      }
    };

    struct st2gba_state_hash
    {
      size_t
      operator()(const st2gba_state& s) const
      {
        std::hash<acc_cond::mark_t> h;
        return s.s ^ h(s.pend);
      }
    };

    struct st2gba_state_equal
    {
      bool
      operator()(const st2gba_state& left,
                 const st2gba_state& right) const
      {
        if (left.s != right.s)
          return false;
        return left.pend == right.pend;
      }
    };

    typedef std::vector<acc_cond::mark_t> terms_t;

    terms_t cnf_terms(const acc_cond::acc_code& code)
    {
      assert(!code.empty());
      terms_t res;
      auto pos = &code.back();
      auto end = &code.front();
      if (pos->sub.op == acc_cond::acc_op::And)
        --pos;
      while (pos >= end)
        {
          auto term_end = pos - 1 - pos->sub.size;
          if (pos->sub.op == acc_cond::acc_op::Or)
            --pos;
          acc_cond::mark_t m = 0U;
          while (pos > term_end)
            {
              assert(pos->sub.op == acc_cond::acc_op::Inf);
              m |= pos[-1].mark;
              pos -= 2;
            }
          res.emplace_back(m);
        }
      return res;
    }
  }


  //  Specialized conversion for Streett -> TGBA
  // ============================================
  //
  // Christof Löding's Diploma Thesis: Methods for the
  // Transformation of ω-Automata: Complexity and Connection to
  // Second Order Logic.  Section 3.4.3, gives a transition
  // from Streett with |Q| states to BA with |Q|*(4^n-3^n+2)
  // states, if n is the number of acceptance pairs.
  //
  // Duret-Lutz et al. (ATVA'2009): On-the-fly Emptiness Check of
  // Transition-based Streett Automata.  Section 3.3 contains a
  // conversion from transition-based Streett Automata to TGBA using
  // the generalized Büchi acceptance to limit the explosion.  It goes
  // from Streett with |Q| states to (T)GBA with |Q|*(2^n+1) states.
  // However the definition of the number of acceptance sets in that
  // paper is suboptimal: only n are needed, not 2^n.
  //
  // This implements this second version.
  twa_graph_ptr
  streett_to_generalized_buchi(const const_twa_graph_ptr& in)
  {
    // While "t" is Streett, it is also generalized Büchi, so
    // do not do anything.
    if (in->acc().is_generalized_buchi())
      return std::const_pointer_cast<twa_graph>(in);

    std::vector<acc_cond::rs_pair> pairs;
    bool res = in->acc().is_streett_like(pairs);
    if (!res)
      throw std::runtime_error("streett_to_generalized_buchi() should only be"
                               " called on automata with Streett-like"
                               " acceptance");

    // In Streett acceptance, inf sets are odd, while fin sets are
    // even.
    acc_cond::mark_t inf;
    acc_cond::mark_t fin;
    std::tie(inf, fin) = in->get_acceptance().used_inf_fin_sets();
    unsigned p = inf.count();
    // At some point we will remove anything that is not used as Inf.
    acc_cond::mark_t to_strip = in->acc().all_sets() - inf;
    acc_cond::mark_t inf_alone = 0U;

    if (!p)
      return remove_fin(in);

    unsigned numsets = in->acc().num_sets();
    std::vector<acc_cond::mark_t> fin_to_infpairs(numsets, 0U);
    std::vector<acc_cond::mark_t> inf_to_finpairs(numsets, 0U);
    for (auto pair: pairs)
      {
        if (pair.fin)
          for (unsigned mark: pair.fin.sets())
            fin_to_infpairs[mark] |= pair.inf;
        else
          inf_alone |= pair.inf;

        for (unsigned mark: pair.inf.sets())
          inf_to_finpairs[mark] |= pair.fin;
      }

    scc_info si(in);

    // Compute the acceptance sets present in each SCC
    unsigned nscc = si.scc_count();
    std::vector<std::tuple<acc_cond::mark_t, acc_cond::mark_t,
                           bool, bool>> sccfi;
    sccfi.reserve(nscc);
    for (unsigned s = 0; s < nscc; ++s)
      {
        auto acc = si.acc_sets_of(s); // {0,1,2,3,4,6,7,9}
        auto acc_fin = acc & fin;     // {0,  2,  4,6}
        auto acc_inf = acc & inf;     // {  1,  3,    7,9}
        acc_cond::mark_t fin_wo_inf = 0U;
        for (unsigned mark: acc_fin.sets())
          if (!fin_to_infpairs[mark] || (fin_to_infpairs[mark] - acc_inf))
            fin_wo_inf.set(mark);

        acc_cond::mark_t inf_wo_fin = 0U;
        for (unsigned mark: acc_inf.sets())
          if (!inf_to_finpairs[mark] || (inf_to_finpairs[mark] - acc_fin))
            inf_wo_fin.set(mark);

        sccfi.emplace_back(fin_wo_inf, inf_wo_fin,
                           acc_fin == 0U, acc_inf == 0U);
      }

    auto out = make_twa_graph(in->get_dict());
    out->copy_ap_of(in);
    out->prop_copy(in, {false, false, false, false, false, true});
    out->set_generalized_buchi(p);

    // Map st2gba pairs to the state numbers used in out.
    typedef std::unordered_map<st2gba_state, unsigned,
                               st2gba_state_hash,
                               st2gba_state_equal> bs2num_map;
    bs2num_map bs2num;

    // Queue of states to be processed.
    typedef std::deque<st2gba_state> queue_t;
    queue_t todo;

    st2gba_state s(in->get_init_state_number());
    bs2num[s] = out->new_state();
    todo.emplace_back(s);

    bool sbacc = in->prop_state_acc().is_true();

    // States of the original automaton are marked with s.pend == -1U.
    const acc_cond::mark_t orig_copy(-1U);

    while (!todo.empty())
      {
        s = todo.front();
        todo.pop_front();
        unsigned src = bs2num[s];

        unsigned scc_src = si.scc_of(s.s);
        bool maybe_acc_scc = !si.is_rejecting_scc(scc_src);

        acc_cond::mark_t scc_fin_wo_inf;
        acc_cond::mark_t scc_inf_wo_fin;
        bool no_fin;
        bool no_inf;
        std::tie(scc_fin_wo_inf, scc_inf_wo_fin, no_fin, no_inf)
          = sccfi[scc_src];

        for (auto& t: in->out(s.s))
          {
            acc_cond::mark_t pend = s.pend;
            acc_cond::mark_t acc = 0U;

            bool maybe_acc = maybe_acc_scc && (scc_src == si.scc_of(t.dst));
            if (pend != orig_copy)
              {
                if (!maybe_acc)
                  continue;
                // No point going to some place we will never leave
                if (t.acc & scc_fin_wo_inf)
                  continue;
                // For any Fin set we see, we want to see the
                // corresponding Inf set.
                for (unsigned mark: (t.acc & fin).sets())
                  pend |= fin_to_infpairs[mark];

                // If we see some Inf set immediately, they are not
                // pending anymore.
                pend -= t.acc & inf;

                // Label this transition with all non-pending
                // inf sets.  The strip will shift everything
                // to the correct numbers in the targets.
                acc = (inf - pend).strip(to_strip);
                // Adjust the pending sets to what will be necessary
                // required on the destination state.
                if (sbacc)
                  {
                    auto a = in->state_acc_sets(t.dst);
                    if (a & scc_fin_wo_inf)
                      continue;
                    for (unsigned m: (a & fin).sets())
                      pend |= fin_to_infpairs[m];

                    pend -= a & inf;
                  }
                pend |= inf_alone;
              }
            else if (no_fin && maybe_acc)
              {
                // If the acceptance is (Fin(0) | Inf(1)) & Inf(2)
                // but we do not see any Fin set in this SCC, a
                // mark {2} should become {1,2} before striping.
                acc = (t.acc | (inf - scc_inf_wo_fin)).strip(to_strip);
              }
            assert((acc & out->acc().all_sets()) == acc);

            st2gba_state d(t.dst, pend);
            // Have we already seen this destination?
            unsigned dest;
            auto dres = bs2num.emplace(d, 0);
            if (!dres.second)
              {
                dest = dres.first->second;
              }
            else                // No, this is a new state
              {
                dest = dres.first->second = out->new_state();
                todo.emplace_back(d);
              }
            out->new_edge(src, dest, t.cond, acc);

            // Nondeterministically jump to level ∅.  We need to do
            // that only once per cycle.  As an approximation, we
            // only to that for transition where t.src >= t.dst as
            // this has to occur at least once per cycle.
            if (pend == orig_copy && (t.src >= t.dst) && maybe_acc && !no_fin)
              {
                acc_cond::mark_t stpend = 0U;
                if (sbacc)
                  {
                    auto a = in->state_acc_sets(t.dst);
                    if (a & scc_fin_wo_inf)
                      continue;
                    for (unsigned m: (a & fin).sets())
                      stpend |= fin_to_infpairs[m];

                    stpend -= a & inf;
                  }
                st2gba_state d(t.dst, stpend | inf_alone);
                // Have we already seen this destination?
                unsigned dest;
                auto dres = bs2num.emplace(d, 0);
                if (!dres.second)
                  {
                    dest = dres.first->second;
                  }
                else                // No, this is a new state
                  {
                    dest = dres.first->second = out->new_state();
                    todo.emplace_back(d);
                  }
                out->new_edge(src, dest, t.cond);
              }
          }
      }
    return out;
  }

  twa_graph_ptr
  streett_to_generalized_buchi_maybe(const const_twa_graph_ptr& in)
  {
    static unsigned min = [&]() {
      const char* c = getenv("SPOT_STREETT_CONV_MIN");
      if (!c)
        return 3;
      errno = 0;
      int val = strtol(c, nullptr, 10);
      if (val < 0 || errno != 0)
        throw std::runtime_error("unexpected value for SPOT_STREETT_CONV_MIN");
      return val;
    }();

    std::vector<acc_cond::rs_pair> pairs;
    bool res = in->acc().is_streett_like(pairs);
    if (!res || min == 0 || min > pairs.size())
      return nullptr;
    else
      return streett_to_generalized_buchi(in);
  }


  /// \brief Take an automaton with any acceptance condition and return
  /// an equivalent Generalized Büchi automaton.
  twa_graph_ptr
  to_generalized_buchi(const const_twa_graph_ptr& aut)
  {
    auto maybe = streett_to_generalized_buchi_maybe(aut);
    if (maybe)
      return maybe;

    auto res = remove_fin(cleanup_acceptance(aut));
    if (res->acc().is_generalized_buchi())
      return res;

    auto cnf = res->get_acceptance().to_cnf();
    // If we are very lucky, building a CNF actually gave us a GBA...
    if (cnf.empty() ||
        (cnf.size() == 2 && cnf.back().sub.op == acc_cond::acc_op::Inf))
      {
        res->set_acceptance(res->num_sets(), cnf);
        cleanup_acceptance_here(res);
        return res;
      }

    // Handle false specifically.  We want the output
    // an automaton with Acceptance: t, that has a single
    // state without successor.
    if (cnf.is_f())
      {
        assert(cnf.front().mark == 0U);
        res = make_twa_graph(aut->get_dict());
        res->set_init_state(res->new_state());
        res->prop_state_acc(true);
        res->prop_weak(true);
        res->prop_universal(true);
        res->prop_stutter_invariant(true);
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

  namespace
  {
    // If the DNF is
    //  Fin(1)&Inf(2)&Inf(4) | Fin(2)&Fin(3)&Inf(1) |
    //  Inf(1)&Inf(3) | Inf(1)&Inf(2) | Fin(4)
    // this returns the following vector of pairs:
    //  [({1}, {2,4})
    //   ({2,3}, {1}),
    //   ({}, {1,3}),
    //   ({}, {2}),
    //   ({4}, t)]
    static std::vector<std::pair<acc_cond::mark_t, acc_cond::mark_t>>
    split_dnf_acc(const acc_cond::acc_code& acc)
    {
      std::vector<std::pair<acc_cond::mark_t, acc_cond::mark_t>> res;
      if (acc.empty())
        {
          res.emplace_back(0U, 0U);
          return res;
        }
      auto pos = &acc.back();
      if (pos->sub.op == acc_cond::acc_op::Or)
        --pos;
      auto start = &acc.front();
      while (pos > start)
        {
          if (pos->sub.op == acc_cond::acc_op::Fin)
            {
              // We have only a Fin term, without Inf.  In this case
              // only, the Fin() may encode a disjunction of sets.
              for (auto s: pos[-1].mark.sets())
                res.emplace_back(acc_cond::mark_t({s}), 0U);
              pos -= pos->sub.size + 1;
            }
          else
            {
              // We have a conjunction of Fin and Inf sets.
              auto end = pos - pos->sub.size - 1;
              acc_cond::mark_t fin = 0U;
              acc_cond::mark_t inf = 0U;
              while (pos > end)
                {
                  switch (pos->sub.op)
                    {
                    case acc_cond::acc_op::And:
                      --pos;
                      break;
                    case acc_cond::acc_op::Fin:
                      fin |= pos[-1].mark;
                      assert(pos[-1].mark.count() == 1);
                      pos -= 2;
                      break;
                    case acc_cond::acc_op::Inf:
                      inf |= pos[-1].mark;
                      pos -= 2;
                      break;
                    case acc_cond::acc_op::FinNeg:
                    case acc_cond::acc_op::InfNeg:
                    case acc_cond::acc_op::Or:
                      SPOT_UNREACHABLE();
                      break;
                    }
                }
              assert(pos == end);
              res.emplace_back(fin, inf);
            }
        }
      return res;
    }


    static twa_graph_ptr
    to_generalized_rabin_aux(const const_twa_graph_ptr& aut,
                             bool share_inf, bool complement)
    {
      auto res = cleanup_acceptance(aut);
      auto oldacc = res->get_acceptance();
      if (complement)
        res->set_acceptance(res->acc().num_sets(), oldacc.complement());

      {
        std::vector<unsigned> pairs;
        if (res->acc().is_generalized_rabin(pairs))
          {
            if (complement)
              res->set_acceptance(res->acc().num_sets(), oldacc);
            return res;
          }
      }
      auto dnf = res->get_acceptance().to_dnf();
      if (dnf.is_f())
        {
          if (complement)
            res->set_acceptance(0, acc_cond::acc_code::t());
          return res;
        }

      auto v = split_dnf_acc(dnf);

      // Decide how we will rename each input set.
      //
      // inf_rename is only used if hoa_style=false, to
      // reuse previously used Inf sets.

      unsigned ns = res->num_sets();
      std::vector<acc_cond::mark_t> rename(ns);
      std::vector<unsigned> inf_rename(ns);

      unsigned next_set = 0;
      // The output acceptance conditions.
      acc_cond::acc_code code =
        complement ? acc_cond::acc_code::t() : acc_cond::acc_code::f();
      for (auto& i: v)
        {
          unsigned fin_set = 0U;

          if (!complement)
            {
              for (auto s: i.first.sets())
                rename[s].set(next_set);
              fin_set = next_set++;
            }

          acc_cond::mark_t infsets = 0U;

          if (share_inf)
            for (auto s: i.second.sets())
              {
                unsigned n = inf_rename[s];
                if (n == 0)
                  n = inf_rename[s] = next_set++;
                rename[s].set(n);
                infsets.set(n);
              }
          else                    // HOA style
            {
              for (auto s: i.second.sets())
                {
                  unsigned n = next_set++;
                  rename[s].set(n);
                  infsets.set(n);
                }
            }

          // The definition of Streett wants the Fin first in clauses,
          // so we do the same for generalized Streett since HOA does
          // not specify anything.  See
          // https://github.com/adl/hoaf/issues/62
          if (complement)
            {
              for (auto s: i.first.sets())
                rename[s].set(next_set);
              fin_set = next_set++;

              auto pair = acc_cond::inf({fin_set});
              pair |= acc_cond::acc_code::fin(infsets);
              pair &= std::move(code);
              code = std::move(pair);
            }
          else
            {
              auto pair = acc_cond::acc_code::inf(infsets);
              pair &= acc_cond::fin({fin_set});
              pair |= std::move(code);
              code = std::move(pair);
            }
        }

      // Fix the automaton
      res->set_acceptance(next_set, code);
      for (auto& e: res->edges())
        {
          acc_cond::mark_t m = 0U;
          for (auto s: e.acc.sets())
            m |= rename[s];
          e.acc = m;
        }
      return res;
    }


  }



  twa_graph_ptr
  to_generalized_rabin(const const_twa_graph_ptr& aut,
                       bool share_inf)
  {
    return to_generalized_rabin_aux(aut, share_inf, false);
  }

  twa_graph_ptr
  to_generalized_streett(const const_twa_graph_ptr& aut,
                         bool share_fin)
  {
    return to_generalized_rabin_aux(aut, share_fin, true);
  }
}
