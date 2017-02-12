// -*- coding: utf-8 -*-
// Copyright (C) 2016, 2017 Laboratoire de Recherche et Développement
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

#include <algorithm>
#include <sstream>
#include <spot/twaalgos/alternation.hh>
#include <spot/misc/minato.hh>
#include <spot/twaalgos/strength.hh>

namespace spot
{
  outedge_combiner::outedge_combiner(const twa_graph_ptr& aut)
    : aut_(aut), vars_(bddtrue)
  {
  }

  outedge_combiner::~outedge_combiner()
  {
    aut_->get_dict()->unregister_all_my_variables(this);
  }

  bdd outedge_combiner::operator()(unsigned st)
  {
    const auto& dict = aut_->get_dict();
    bdd res = bddtrue;
    for (unsigned d1: aut_->univ_dests(st))
      {
        bdd res2 = bddfalse;
        for (auto& e: aut_->out(d1))
          {
            bdd out = bddtrue;
            for (unsigned d: aut_->univ_dests(e.dst))
              {
                auto p = state_to_var.emplace(d, 0);
                if (p.second)
                  {
                    int v = dict->register_anonymous_variables(1, this);
                    p.first->second = v;
                    var_to_state.emplace(v, d);
                    vars_ &= bdd_ithvar(v);
                  }
                out &= bdd_ithvar(p.first->second);
              }
            res2 |= e.cond & out;
          }
        res &= res2;
      }
    return res;
  }



  void outedge_combiner::new_dests(unsigned st, bdd out) const
  {
    minato_isop isop(out);
    bdd cube;
    std::vector<unsigned> univ_dest;
    while ((cube = isop.next()) != bddfalse)
      {
        bdd cond = bdd_exist(cube, vars_);
        bdd dest = bdd_existcomp(cube, vars_);
        while (dest != bddtrue)
          {
            assert(bdd_low(dest) == bddfalse);
            auto it = var_to_state.find(bdd_var(dest));
            assert(it != var_to_state.end());
            univ_dest.push_back(it->second);
            dest = bdd_high(dest);
          }
        std::sort(univ_dest.begin(), univ_dest.end());
        aut_->new_univ_edge(st, univ_dest.begin(), univ_dest.end(), cond);
        univ_dest.clear();
      }
  }



  namespace
  {
    class alternation_remover final
    {
    protected:
      const_twa_graph_ptr aut_;
      scc_info si_;
      enum scc_class : char { accept, reject_1, reject_more };
      std::vector<scc_class> class_of_;
      bool has_reject_more_ = false;
      unsigned reject_1_count_ = 0;
      std::set<unsigned> true_states_;

      bool ensure_weak_scc(unsigned scc)
      {
        bool first = true;
        bool reject_cycle = false;
        acc_cond::mark_t m = 0U;
        for (unsigned src: si_.states_of(scc))
          for (auto& t: aut_->out(src))
            for (unsigned d: aut_->univ_dests(t.dst))
              if (si_.scc_of(d) == scc)
                {
                  if (first)
                    {
                      first = false;
                      m = t.acc;
                      reject_cycle = !aut_->acc().accepting(m);
                    }
                  else if (m != t.acc)
                    {
                      throw std::runtime_error
                        ("alternation_removal() only work with weak "
                         "alternating automata");
                    }
                  // In case of a universal edge we only
                  // need to check the first destination
                  // inside the SCC, because the other
                  // have the same t.acc.
                  break;
                }
        return reject_cycle;
      }

      void classify_each_scc()
      {
        auto& g = aut_->get_graph();
        unsigned sc = si_.scc_count();
        for (unsigned n = 0; n < sc; ++n)
          {
            if (si_.is_trivial(n))
              continue;
            if (si_.states_of(n).size() == 1)
              {
                if (si_.is_rejecting_scc(n))
                  {
                    class_of_[n] = scc_class::reject_1;
                    ++reject_1_count_;
                  }
                else
                  {
                    // For size one, scc_info should always be able to
                    // decide rejecting/accepting.
                    assert(si_.is_accepting_scc(n));

                    // Catch unsupported types of automata
                    bool rej = ensure_weak_scc(n);
                    assert(rej == false);
                    // Detect if it is a "true state"
                    unsigned s = si_.states_of(n).front();
                    auto& ss = g.state_storage(s);
                    if (ss.succ == ss.succ_tail)
                      {
                        auto& es = g.edge_storage(ss.succ);
                        if (es.cond == bddtrue && !aut_->is_univ_dest(es.dst))
                          true_states_.emplace(s);
                      }
                  }
              }
            else if (ensure_weak_scc(n))
              {
                class_of_[n] = reject_more;
                has_reject_more_ = true;
              }
          }
      }

      std::vector<int> state_to_var_;
      std::map<int, unsigned> var_to_state_;
      std::vector<int> scc_to_var_;
      std::map<int, acc_cond::mark_t> var_to_mark_;
      bdd all_vars_;
      bdd all_marks_;
      bdd all_states_;

      void allocate_state_vars()
      {
        auto d = aut_->get_dict();
        // We need one BDD variable per possible output state.  If
        // that state is in a reject_more SCC we actually use two
        // variables for the breakpoint.
        unsigned ns = aut_->num_states();
        state_to_var_.reserve(ns);
        bdd all_states = bddtrue;
        for (unsigned s = 0; s < ns; ++s)
          {
            if (!si_.reachable_state(s))
              {
                state_to_var_.push_back(0);
                continue;
              }
            scc_class c = class_of_[si_.scc_of(s)];
            bool r = c == scc_class::reject_more;
            int v = d->register_anonymous_variables(1 + r, this);
            state_to_var_.push_back(v);
            var_to_state_[v] = s;
            all_states &= bdd_ithvar(v);
            if (r)
              {
                var_to_state_[v + 1] = ~s;
                all_states &= bdd_ithvar(v + 1);
              }
          }
        // We also use one BDD variable per reject_1 SCC.  Each of
        // these variables will represent a bit in mark_t.  We reserve
        // the first bit for the break_point construction if we have
        // some reject_more SCC.
        unsigned nc = si_.scc_count();
        scc_to_var_.reserve(nc);
        unsigned mark_pos = has_reject_more_;
        bdd all_marks = bddtrue;
        for (unsigned s = 0; s < nc; ++s)
          {
            scc_class c = class_of_[s];
            if (c == scc_class::reject_1)
              {
                int v = d->register_anonymous_variables(1, this);
                scc_to_var_.emplace_back(v);
                var_to_mark_.emplace(v, acc_cond::mark_t({mark_pos++}));
                bdd bv = bdd_ithvar(v);
                all_marks &= bv;
              }
            else
              {
                scc_to_var_.emplace_back(0);
              }
          }
        all_marks_ = all_marks;
        all_states_ = all_states;
        all_vars_ = all_states & all_marks;
      }

      std::map<unsigned, bdd> state_as_bdd_cache_;

      bdd state_as_bdd(unsigned s)
      {
        auto p = state_as_bdd_cache_.emplace(s, bddfalse);
        if (!p.second)
          return p.first->second;

        bool marked = (int)s < 0;
        if (marked)
          s = ~s;

        unsigned scc_s = si_.scc_of(s);
        bdd res = bddfalse;
        for (auto& e: aut_->out(s))
          {
            bdd dest = bddtrue;
            for (unsigned d: aut_->univ_dests(e.dst))
              {
                unsigned scc_d = si_.scc_of(d);
                scc_class c = class_of_[scc_d];
                bool mark =
                  marked && (scc_s == scc_d) && (c == scc_class::reject_more);
                dest &= bdd_ithvar(state_to_var_[d] + mark);
                if (c == scc_class::reject_1 && scc_s == scc_d)
                  dest &= bdd_ithvar(scc_to_var_[scc_s]);
              }
            res |= e.cond & dest;
          }

        p.first->second = res;
        return res;
      }

      acc_cond::mark_t bdd_to_state(bdd b, std::vector<unsigned>& s)
      {
        acc_cond::mark_t m = 0U;
        while (b != bddtrue)
          {
            assert(bdd_low(b) == bddfalse);
            int v = bdd_var(b);
            auto it = var_to_state_.find(v);
            if (it != var_to_state_.end())
              {
                s.push_back(it->second);
              }
            else
              {
                auto it2 = var_to_mark_.find(v);
                assert(it2 != var_to_mark_.end());
                m |= it2->second;
              }
            b = bdd_high(b);
          }
        return m;
      }

      void simplify_state_set(std::vector<unsigned>& ss)
      {
        auto to_remove = true_states_;
        for (unsigned i: ss)
          if ((int)i < 0)
            to_remove.emplace(~i);

        auto i =
          std::remove_if(ss.begin(), ss.end(),
                         [&] (unsigned s) {
                           return to_remove.find(s) != to_remove.end();
                         });
        ss.erase(i, ss.end());
        std::sort(ss.begin(), ss.end());
      }

      bool has_mark(const std::vector<unsigned>& ss)
      {
        for (unsigned i: ss)
          if ((int)i < 0)
            return true;
        return false;
      }

      void set_mark(std::vector<unsigned>& ss)
      {
        for (unsigned& s: ss)
          if (class_of_[si_.scc_of(s)] == scc_class::reject_more)
            s = ~s;
      }

    public:
      alternation_remover(const const_twa_graph_ptr& aut)
        : aut_(aut), si_(aut), class_of_(si_.scc_count(), scc_class::accept)
      {
      }

      ~alternation_remover()
      {
        aut_->get_dict()->unregister_all_my_variables(this);
      }


      twa_graph_ptr run(bool named_states)
      {
        // First, we classify each SCC into three possible classes:
        //
        // 1) trivial or accepting
        // 2) rejecting of size 1
        // 3) rejecting of size >1
        classify_each_scc();

        // Rejecting SCCs of size 1 can be handled using genralized
        // Büchi acceptance, using one set per SCC, as in Gastin &
        // Oddoux CAV'01.  See also Boker & et al. ICALP'10.  Larger
        // rejecting SCCs require a more expensive procedure known as
        // the break point construction.  See Miyano & Hayashi (TCS
        // 1984).  We are currently combining the two constructions.
        auto res = make_twa_graph(aut_->get_dict());
        res->copy_ap_of(aut_);
        // We preserve deterministic-like properties, and
        // stutter-invariance.
        res->prop_copy(aut_, {false, false, false, true, true});
        res->set_generalized_buchi(has_reject_more_ + reject_1_count_);

        // We for easier computation of outgoing sets, we will
        // represent states using BDD variables.
        allocate_state_vars();

        // Conversion between state-sets and states.
        typedef std::vector<unsigned> state_set;
        std::vector<state_set> s_to_ss;
        std::map<state_set, unsigned> ss_to_s;
        std::stack<unsigned> todo;

        std::vector<std::string>* state_name = nullptr;
        if (named_states)
          {
            state_name = new std::vector<std::string>();
            res->set_named_prop("state-names", state_name);
          }

        auto new_state = [&](state_set& ss, bool& need_mark)
        {
          simplify_state_set(ss);

          if (has_reject_more_)
            {
              need_mark = has_mark(ss);
              if (!need_mark)
                set_mark(ss);
            }

          auto p = ss_to_s.emplace(ss, 0);
          if (!p.second)
            return p.first->second;
          unsigned s = res->new_state();
          assert(s == s_to_ss.size());
          p.first->second = s;
          s_to_ss.emplace_back(ss);
          todo.emplace(s);

          if (named_states)
            {
              std::ostringstream os;
              bool notfirst = false;
              for (unsigned s: ss)
                {
                  if (notfirst)
                    os << ',';
                  else
                    notfirst = true;
                  if ((int)s < 0)
                    {
                      os << '~';
                      s = ~s;
                    }
                  os << s;
                }
              if (!notfirst)
                os << "{}";
              state_name->emplace_back(os.str());
            }
          return s;
        };

        const auto& i = aut_->univ_dests(aut_->get_init_state_number());
        state_set is(i.begin(), i.end());
        bool has_mark = false;
        res->set_init_state(new_state(is, has_mark));

        acc_cond::mark_t all_marks = res->acc().all_sets();

        state_set v;
        while (!todo.empty())
          {
            unsigned s = todo.top();
            todo.pop();

            bdd bs = bddtrue;
            for (unsigned se: s_to_ss[s])
              bs &= state_as_bdd(se);


            bdd ap = bdd_exist(bdd_support(bs), all_vars_);
            bdd all_letters = bdd_exist(bs, all_vars_);

            // First loop over all possible valuations atomic properties.
            while (all_letters != bddfalse)
              {
                bdd oneletter = bdd_satoneset(all_letters, ap, bddtrue);
                all_letters -= oneletter;

                minato_isop isop(bs & oneletter);
                bdd cube;
                while ((cube = isop.next()) != bddfalse)
                  {
                    bdd cond = bdd_exist(cube, all_vars_);
                    bdd dest = bdd_existcomp(cube, all_vars_);
                    v.clear();
                    acc_cond::mark_t m = bdd_to_state(dest, v);
                    unsigned d = new_state(v, has_mark);
                    if (has_mark)
                      m.set(0);
                    res->new_edge(s, d, cond, all_marks - m);
                  }
              }
          }
        res->merge_edges();
        return res;
      }
    };

  }


  twa_graph_ptr remove_alternation(const const_twa_graph_ptr& aut,
                                   bool named_states)
  {
    if (!aut->is_alternating())
      // Nothing to do, why was this function called at all?
      return std::const_pointer_cast<twa_graph>(aut);

    alternation_remover ar(aut);
    return ar.run(named_states);
  }

}
