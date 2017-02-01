// -*- coding: utf-8 -*-
// Copyright (C) 2014-2017 Laboratoire de Recherche et Développement de
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

#include <spot/twaalgos/stutter.hh>
#include <spot/twa/twa.hh>
#include <spot/misc/hash.hh>
#include <spot/misc/hashfunc.hh>
#include <spot/tl/apcollect.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/tl/remove_x.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/remfin.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/twa/twaproduct.hh>
#include <spot/twa/bddprint.hh>
#include <deque>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace spot
{
  namespace
  {
    class state_tgbasl final: public state
    {
    public:
      state_tgbasl(const state* s, bdd cond) : s_(s), cond_(cond)
      {
      }

      virtual
      ~state_tgbasl()
      {
        s_->destroy();
      }

      virtual int
      compare(const state* other) const override
      {
        const state_tgbasl* o =
          down_cast<const state_tgbasl*>(other);
        int res = s_->compare(o->real_state());
        if (res != 0)
          return res;
        return cond_.id() - o->cond_.id();
      }

      virtual size_t
      hash() const override
      {
        return wang32_hash(s_->hash()) ^ wang32_hash(cond_.id());
      }

      virtual
      state_tgbasl* clone() const override
      {
        return new state_tgbasl(*this);
      }

      const state*
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
      const state* s_;
      bdd cond_;
    };

    class twasl_succ_iterator final : public twa_succ_iterator
    {
    public:
      twasl_succ_iterator(twa_succ_iterator* it, const state_tgbasl* state,
                           bdd_dict_ptr d, bdd atomic_propositions)
        : it_(it), state_(state), aps_(atomic_propositions), d_(d)
      {
      }

      virtual
      ~twasl_succ_iterator()
      {
        delete it_;
      }

      // iteration

      virtual bool
      first() override
      {
        loop_ = false;
        done_ = false;
        need_loop_ = true;
        if (it_->first())
          {
            cond_ = it_->cond();
            next_edge();
          }
        return true;
      }

      virtual bool
      next() override
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
            cond_ = it_->cond();
            next_edge();
            return true;
          }
      }

      virtual bool
      done() const override
      {
        return it_->done() && done_;
      }

      // inspection

      virtual state_tgbasl*
      dst() const override
      {
        if (loop_)
          return new state_tgbasl(state_->real_state(), state_->cond());
        return new state_tgbasl(it_->dst(), one_);
      }

      virtual bdd
      cond() const override
      {
        if (loop_)
          return state_->cond();
        return one_;
      }

      virtual acc_cond::mark_t
      acc() const override
      {
        if (loop_)
          return 0U;
        return it_->acc();
      }

    private:
      void
      next_edge()
      {
        one_ = bdd_satoneset(cond_, aps_, bddtrue);
        cond_ -= one_;
        if (need_loop_ && (state_->cond() == one_)
            && (state_ == it_->dst()))
          need_loop_ = false;
      }

      twa_succ_iterator* it_;
      const state_tgbasl* state_;
      bdd cond_;
      bdd one_;
      bdd aps_;
      bdd_dict_ptr d_;
      bool loop_;
      bool need_loop_;
      bool done_;
    };


    class tgbasl final : public twa
    {
    public:
      tgbasl(const const_twa_ptr& a, bdd atomic_propositions)
        : twa(a->get_dict()), a_(a), aps_(atomic_propositions)
      {
        get_dict()->register_all_propositions_of(&a_, this);
        assert(num_sets() == 0);
        set_generalized_buchi(a_->num_sets());
      }

      virtual const state* get_init_state() const override
      {
        return new state_tgbasl(a_->get_init_state(), bddfalse);
      }

      virtual twa_succ_iterator* succ_iter(const state* state) const override
      {
        const state_tgbasl* s = down_cast<const state_tgbasl*>(state);
        return new twasl_succ_iterator(a_->succ_iter(s->real_state()), s,
                                        a_->get_dict(), aps_);
      }

      virtual std::string format_state(const state* state) const override
      {
        const state_tgbasl* s = down_cast<const state_tgbasl*>(state);
        return (a_->format_state(s->real_state())
                + ", "
                + bdd_format_formula(a_->get_dict(), s->cond()));
      }

    private:
      const_twa_ptr a_;
      bdd aps_;
    };

    typedef std::shared_ptr<tgbasl> tgbasl_ptr;

    inline tgbasl_ptr make_tgbasl(const const_twa_ptr& aut, bdd ap)
    {
      return std::make_shared<tgbasl>(aut, ap);
    }



    typedef std::pair<unsigned, bdd> stutter_state;

    struct stutter_state_hash
    {
      size_t
      operator()(const stutter_state& s) const
      {
        return wang32_hash(s.first) ^ wang32_hash(s.second.id());
      }
    };

    // Associate the stutter state to its number.
    typedef std::unordered_map<stutter_state, unsigned,
                               stutter_state_hash> ss2num_map;

    // Queue of state to be processed.
    typedef std::deque<stutter_state> queue_t;
  }

  twa_graph_ptr
  sl(const twa_graph_ptr& a)
  {
    return sl(a, a->ap_vars());
  }

  twa_graph_ptr
  sl2(const twa_graph_ptr& a)
  {
    return sl2(a, a->ap_vars());
  }

  twa_graph_ptr
  sl(const const_twa_graph_ptr& a, bdd atomic_propositions)
  {
    // The result automaton uses numbered states.
    twa_graph_ptr res = make_twa_graph(a->get_dict());
    // We use the same BDD variables as the input.
    res->copy_ap_of(a);
    res->copy_acceptance_of(a);
    // These maps make it possible to convert stutter_state to number
    // and vice-versa.
    ss2num_map ss2num;

    queue_t todo;

    unsigned s0 = a->get_init_state_number();
    stutter_state s(s0, bddfalse);
    ss2num[s] = 0;
    res->new_state();
    todo.emplace_back(s);

    while (!todo.empty())
      {
        s = todo.front();
        todo.pop_front();
        unsigned src = ss2num[s];

        bool self_loop_needed = true;

        for (auto& t : a->out(s.first))
          {
            bdd all = t.cond;
            while (all != bddfalse)
              {
                bdd one = bdd_satoneset(all, atomic_propositions, bddtrue);
                all -= one;

                stutter_state d(t.dst, one);

                auto r = ss2num.emplace(d, ss2num.size());
                unsigned dest = r.first->second;

                if (r.second)
                  {
                    todo.emplace_back(d);
                    unsigned u = res->new_state();
                    assert(u == dest);
                    (void)u;
                  }

                // Create the edge.
                res->new_edge(src, dest, one, t.acc);

                if (src == dest)
                  self_loop_needed = false;
              }
          }

        if (self_loop_needed && s.second != bddfalse)
          res->new_edge(src, src, s.second, 0U);
      }
    res->merge_edges();
    return res;
  }

  twa_graph_ptr
  sl2(twa_graph_ptr&& a, bdd atomic_propositions)
  {
    if (atomic_propositions == bddfalse)
      atomic_propositions = a->ap_vars();
    unsigned num_states = a->num_states();
    unsigned num_edges = a->num_edges();
    std::vector<bdd> selfloops(num_states, bddfalse);
    std::map<std::pair<unsigned, int>, unsigned> newstates;
    // Record all the conditions for which we can selfloop on each
    // state.
    for (auto& t: a->edges())
      if (t.src == t.dst)
        selfloops[t.src] |= t.cond;
    for (unsigned t = 1; t <= num_edges; ++t)
      {
        auto& td = a->edge_storage(t);
        if (a->is_dead_edge(td))
          continue;

        unsigned src = td.src;
        unsigned dst = td.dst;
        if (src != dst)
          {
            bdd all = td.cond;
            // If there is a self-loop with the whole condition on
            // either end of the edge, do not bother with it.
            if (bdd_implies(all, selfloops[src])
                || bdd_implies(all, selfloops[dst]))
              continue;
            // Do not use td in the loop because the new_edge()
            // might invalidate it.
            auto acc = td.acc;
            while (all != bddfalse)
              {
                bdd one = bdd_satoneset(all, atomic_propositions, bddtrue);
                all -= one;
                // Skip if there is a loop for this particular letter.
                if (bdd_implies(one, selfloops[src])
                    || bdd_implies(one, selfloops[dst]))
                  continue;
                auto p = newstates.emplace(std::make_pair(dst, one.id()), 0);
                if (p.second)
                  p.first->second = a->new_state();
                unsigned tmp = p.first->second; // intermediate state
                unsigned i = a->new_edge(src, tmp, one, acc);
                assert(i > num_edges);
                i = a->new_edge(tmp, tmp, one, 0U);
                assert(i > num_edges);
                // No acceptance here to preserve the state-based property.
                i = a->new_edge(tmp, dst, one, 0U);
                assert(i > num_edges);
                (void)i;
              }
          }
      }
    if (num_states != a->num_states())
      a->prop_keep({true,        // state_based
                    false,        // inherently_weak
                    false, false, // deterministic
                    false,      // stutter inv.
                   });
    a->merge_edges();
    return a;
  }

  twa_graph_ptr
  sl2(const const_twa_graph_ptr& a, bdd atomic_propositions)
  {
    return sl2(make_twa_graph(a, twa::prop_set::all()),
               atomic_propositions);
  }


  twa_graph_ptr
  closure(twa_graph_ptr&& a)
  {
    a->prop_keep({false,        // state_based
                  false,        // inherently_weak
                  false, false, // deterministic
                  false,        // stutter inv.
                 });

    unsigned n = a->num_states();
    std::vector<unsigned> todo;
    std::vector<std::vector<unsigned> > dst2trans(n);

    for (unsigned state = 0; state < n; ++state)
      {
        auto trans = a->out(state);

        for (auto it = trans.begin(); it != trans.end(); ++it)
          {
            todo.emplace_back(it.trans());
            dst2trans[it->dst].emplace_back(it.trans());
          }

        while (!todo.empty())
          {
            auto t1 = a->edge_storage(todo.back());
            todo.pop_back();

            for (auto& t2 : a->out(t1.dst))
              {
                bdd cond = t1.cond & t2.cond;
                if (cond != bddfalse)
                  {
                    bool need_new_trans = true;
                    acc_cond::mark_t acc = t1.acc | t2.acc;
                    for (auto& t: dst2trans[t2.dst])
                      {
                        auto& ts = a->edge_storage(t);
                        if (acc == ts.acc)
                          {
                            if (!bdd_implies(cond, ts.cond))
                              {
                                ts.cond |= cond;
                                if (std::find(todo.begin(), todo.end(), t)
                                    == todo.end())
                                  todo.emplace_back(t);
                              }
                            need_new_trans = false;
                            break;
                          }
                        else if (cond == ts.cond)
                          {
                            acc |= ts.acc;
                            if (ts.acc != acc)
                              {
                                ts.acc = acc;
                                if (std::find(todo.begin(), todo.end(), t)
                                    == todo.end())
                                  todo.emplace_back(t);
                              }
                            need_new_trans = false;
                            break;
                          }
                      }
                    if (need_new_trans)
                      {
                        // Load t2.dst first, because t2 can be
                        // invalidated by new_edge().
                        auto dst = t2.dst;
                        auto i = a->new_edge(state, dst, cond, acc);
                        dst2trans[dst].emplace_back(i);
                        todo.emplace_back(i);
                      }
                  }
              }
          }
        for (auto& it: dst2trans)
          it.clear();
      }
    return a;
  }

  twa_graph_ptr
  closure(const const_twa_graph_ptr& a)
  {
    return closure(make_twa_graph(a, twa::prop_set::all()));
  }

  // The stutter check algorithm to use can be overridden via an
  // environment variable.
  static int default_stutter_check_algorithm()
  {
    static const char* stutter_check = getenv("SPOT_STUTTER_CHECK");
    if (stutter_check)
      {
        char* endptr;
        long res = strtol(stutter_check, &endptr, 10);
        if (*endptr || res < 0 || res > 9)
          throw
            std::runtime_error("invalid value for SPOT_STUTTER_CHECK.");
        return res;
      }
    else
      {
        return 8;     // The best variant, according to our benchmarks.
      }
  }

  bool
  is_stutter_invariant(formula f)
  {
    if (f.is_ltl_formula() && f.is_syntactic_stutter_invariant())
      return true;

    int algo = default_stutter_check_algorithm();

    if (algo == 0 || algo == 9)
      // Etessami's check via syntactic transformation.
      {
        if (!f.is_ltl_formula())
          throw std::runtime_error("Cannot use the syntactic "
                                   "stutter-invariance check "
                                   "for non-LTL formulas");
        formula g = remove_x(f);
        bool res;
        if (algo == 0)                // Equivalence check
          {
            tl_simplifier ls;
            res = ls.are_equivalent(f, g);
          }
        else
          {
            formula h = formula::Xor(f, g);
            res = ltl_to_tgba_fm(h, make_bdd_dict())->is_empty();
          }
        return res;
      }

    // Prepare for an automata-based check.
    translator trans;
    auto aut_f = trans.run(f);
    auto aut_nf = trans.run(formula::Not(f));
    bdd aps = atomic_prop_collect_as_bdd(f, aut_f);
    return is_stutter_invariant(std::move(aut_f), std::move(aut_nf), aps, algo);
  }

  bool
  is_stutter_invariant(twa_graph_ptr&& aut_f,
                       twa_graph_ptr&& aut_nf, bdd aps, int algo)
  {
    if (algo == 0)
      algo = default_stutter_check_algorithm();

    switch (algo)
      {
      case 1: // sl(aut_f) x sl(aut_nf)
        return product(sl(std::move(aut_f), aps),
                       sl(std::move(aut_nf), aps))->is_empty();
      case 2: // sl(cl(aut_f)) x aut_nf
        return product(sl(closure(std::move(aut_f)), aps),
                       std::move(aut_nf))->is_empty();
      case 3: // (cl(sl(aut_f)) x aut_nf
        return product(closure(sl(std::move(aut_f), aps)),
                       std::move(aut_nf))->is_empty();
      case 4: // sl2(aut_f) x sl2(aut_nf)
        return product(sl2(std::move(aut_f), aps),
                       sl2(std::move(aut_nf), aps))->is_empty();
      case 5: // sl2(cl(aut_f)) x aut_nf
        return product(sl2(closure(std::move(aut_f)), aps),
                       std::move(aut_nf))->is_empty();
      case 6: // (cl(sl2(aut_f)) x aut_nf
        return product(closure(sl2(std::move(aut_f), aps)),
                       std::move(aut_nf))->is_empty();
      case 7: // on-the-fly sl(aut_f) x sl(aut_nf)
        return otf_product(make_tgbasl(aut_f, aps),
                           make_tgbasl(aut_nf, aps))->is_empty();
      case 8: // cl(aut_f) x cl(aut_nf)
        return product(closure(std::move(aut_f)),
                       closure(std::move(aut_nf)))->is_empty();
      default:
        throw std::runtime_error("invalid algorithm number for "
                                 "is_stutter_invariant()");
        SPOT_UNREACHABLE();
      }
  }

  trival
  check_stutter_invariance(const twa_graph_ptr& aut, formula f,
                           bool do_not_determinize)
  {
    trival is_stut = aut->prop_stutter_invariant();
    if (is_stut.is_known())
      return is_stut.is_true();

    twa_graph_ptr neg = nullptr;
    if (f)
      {
        neg = translator(aut->get_dict()).run(formula::Not(f));
      }
    else
      {
        twa_graph_ptr tmp = aut;
        if (!is_deterministic(aut))
          {
            if (do_not_determinize)
              return trival::maybe();
            spot::postprocessor p;
            p.set_type(spot::postprocessor::Generic);
            p.set_pref(spot::postprocessor::Deterministic);
            p.set_level(spot::postprocessor::Low);
            tmp = p.run(aut);
          }
        neg = dtwa_complement(tmp);
      }

    is_stut = is_stutter_invariant(make_twa_graph(aut, twa::prop_set::all()),
                                   std::move(neg), aut->ap_vars());
    aut->prop_stutter_invariant(is_stut);
    return is_stut;
  }
}
