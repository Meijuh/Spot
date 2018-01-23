// -*- coding: utf-8 -*-
// Copyright (C) 2017-2018 Laboratoire de Recherche et Développement de l'Epita.
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

#include <deque>

#include <spot/twaalgos/rabin2parity.hh>

#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  namespace
  {

    using perm_t = std::vector<unsigned>;
    struct iar_state
    {
      unsigned state;
      perm_t perm;

      bool
      operator<(const iar_state& other) const
      {
        return state == other.state ? perm < other.perm : state < other.state;
      }
    };

    template<bool is_rabin>
    class iar_generator
    {
      // helper functions: access fin and inf parts of the pairs
      // these functions negate the Streett condition to see it as a Rabin one
      const acc_cond::mark_t&
      fin(unsigned k) const
      {
        if (is_rabin)
          return pairs_[k].fin;
        else
          return pairs_[k].inf;
      }
      acc_cond::mark_t
      inf(unsigned k) const
      {
        if (is_rabin)
          return pairs_[k].inf;
        else
          return pairs_[k].fin;
      }
    public:
      explicit iar_generator(const const_twa_graph_ptr& a,
                             const std::vector<acc_cond::rs_pair>& p)
      : aut_(a)
      , pairs_(p)
      , scc_(scc_info(a))
      {}

      twa_graph_ptr
      run()
      {
        res_ = make_twa_graph(aut_->get_dict());
        res_->copy_ap_of(aut_);

        build_iar_scc(scc_.initial());

        // resulting automaton has acceptance condition: parity max odd
        // with priorities ranging from 0 to 2*(nb pairs)
        // /!\ priorities are shifted by -1 compared to the original paper
        if (is_rabin)
          res_->set_acceptance(2*pairs_.size() + 1,
              acc_cond::acc_code::parity(true, true, 2*pairs_.size() + 1));
        else
          res_->set_acceptance(2*pairs_.size() + 1,
              acc_cond::acc_code::parity(true, false, 2*pairs_.size() + 1));

        // set initial state
        res_->set_init_state(
            iar2num.at(state2iar.at(aut_->get_init_state_number())));

        // there could be quite a number of unreachable states, prune them
        res_->purge_unreachable_states();

        return res_;
      }

      void
      build_iar_scc(unsigned scc_num)
      {
        // we are working on an SCC: the state we start from does not matter
        unsigned init = scc_.one_state_of(scc_num);

        std::deque<iar_state> todo;
        auto get_state = [&](const iar_state& s)
          {
            auto it = iar2num.find(s);
            if (it == iar2num.end())
              {
                unsigned nb = res_->new_state();
                iar2num[s] = nb;
                num2iar[nb] = s;
                todo.push_back(s);
                return nb;
              }
            return it->second;
          };

        auto get_other_scc = [this](unsigned state)
          {
            auto it = state2iar.find(state);
            // recursively build the destination SCC if we detect that it has
            // not been already built.
            if (it == state2iar.end())
              build_iar_scc(scc_.scc_of(state));
            return iar2num.at(state2iar.at(state));
          };

        if (scc_.is_trivial(scc_num))
          {
            iar_state iar_s{init, perm_t()};
            state2iar[init] = iar_s;
            unsigned src_num = get_state(iar_s);
            // Do not forget to connect to subsequent SCCs
            for (const auto& e : aut_->out(init))
              res_->new_edge(src_num, get_other_scc(e.dst), e.cond);
            return;
          }

        // determine the pairs that appear in the SCC
        auto colors = scc_.acc_sets_of(scc_num);
        std::set<unsigned> scc_pairs;
        for (unsigned k = 0; k != pairs_.size(); ++k)
          if (inf(k) == 0U || (colors & (pairs_[k].fin | pairs_[k].inf)))
            scc_pairs.insert(k);

        perm_t p0;
        for (unsigned k : scc_pairs)
          p0.push_back(k);

        iar_state s0{init, p0};
        get_state(s0); // put s0 in todo

        // the main loop
        while (!todo.empty())
          {
            iar_state current = todo.front();
            todo.pop_front();

            unsigned src_num = get_state(current);

            for (const auto& e : aut_->out(current.state))
              {
                // connect to the appropriate state
                if (scc_.scc_of(e.dst) != scc_num)
                  res_->new_edge(src_num, get_other_scc(e.dst), e.cond);
                else
                  {
                    // find the new permutation
                    perm_t new_perm = current.perm;
                    // Count pairs whose fin-part is seen on this transition
                    unsigned seen_nb = 0;
                    // consider the pairs for this SCC only
                    for (unsigned k : scc_pairs)
                      if (e.acc & fin(k))
                        {
                          ++seen_nb;
                          auto it = std::find(new_perm.begin(),
                                              new_perm.end(),
                                              k);
                          // move the pair in front of the permutation
                          std::rotate(new_perm.begin(), it, it+1);
                        }

                    iar_state dst;
                    unsigned dst_num = -1U;

                    // Optimization: when several indices are seen in the
                    // transition, they move at the front of new_perm in any
                    // order. Check whether there already exists an iar_state
                    // that matches this condition.
                    for (unsigned i = 0; i != num2iar.size(); ++i)
                      if (num2iar[i].state == e.dst)
                        if (std::equal(new_perm.begin() + seen_nb,
                                       new_perm.end(),
                                       num2iar[i].perm.begin() + seen_nb))
                          {
                            dst = num2iar[i];
                            dst_num = i;
                            break;
                          }
                    // if such a state was not found, build it
                    if (dst_num == -1U)
                      {
                        dst = iar_state{e.dst, new_perm};
                        dst_num = get_state(dst);
                      }

                    // find the maximal index encountered by this transition
                    unsigned maxint = -1U;
                    for (unsigned k = 0; k != current.perm.size(); ++k)
                      {
                        unsigned pk = current.perm[k];
                        if (inf(pk) == 0U ||
                            (e.acc & (pairs_[pk].fin | pairs_[pk].inf)))
                          // k increases in the loop, so k > maxint necessarily
                          maxint = k;
                      }

                    acc_cond::mark_t acc = 0U;
                    if (maxint == -1U)
                      acc = {0};
                    else if (e.acc & fin(current.perm[maxint]))
                      acc = {2*maxint+2};
                    else
                      acc = {2*maxint+1};

                    res_->new_edge(src_num, dst_num, e.cond, acc);
                  }
              }
          }

        // Optimization: find the bottom SCC of the sub-automaton we have just
        // built. To that end, we have to ignore edges going out of scc_num.
        auto leaving_edge = [&](unsigned d)
          {
            return scc_.scc_of(num2iar.at(d).state) != scc_num;
          };
        auto filter_edge = [](const twa_graph::edge_storage_t&,
                              unsigned dst,
                              void* filter_data)
          {
            decltype(leaving_edge)* data =
              static_cast<decltype(leaving_edge)*>(filter_data);

            if ((*data)(dst))
              return scc_info::edge_filter_choice::ignore;
            return scc_info::edge_filter_choice::keep;
          };
        scc_info sub_scc(res_, get_state(s0), filter_edge, &leaving_edge);
        // SCCs are numbered in reverse topological order, so the bottom SCC has
        // index 0.
        const unsigned bscc = 0;
        assert(sub_scc.succ(0).empty());
        assert(
            [&]()
            {
              for (unsigned s = 1; s != sub_scc.scc_count(); ++s)
                if (sub_scc.succ(s).empty())
                  return false;
              return true;
            } ());

        assert(sub_scc.states_of(bscc).size()
            >= scc_.states_of(scc_num).size());

        // update state2iar
        for (const auto& scc_state : sub_scc.states_of(bscc))
          {
            iar_state iar = num2iar.at(scc_state);
            if (state2iar.find(iar.state) == state2iar.end())
              state2iar[iar.state] = iar;
          }
      }

    private:
      const const_twa_graph_ptr& aut_;
      const std::vector<acc_cond::rs_pair>& pairs_;
      const scc_info scc_;
      twa_graph_ptr res_;

      // to be used when entering a new SCC
      // maps a state of aut_ onto an iar_state with the appropriate perm
      std::map<unsigned, iar_state> state2iar;

      std::map<iar_state, unsigned> iar2num;
      std::map<unsigned, iar_state> num2iar;
    };
  }

  twa_graph_ptr
  iar_maybe(const const_twa_graph_ptr& aut)
  {
    std::vector<acc_cond::rs_pair> pairs;
    if (!aut->acc().is_rabin_like(pairs))
      if (!aut->acc().is_streett_like(pairs))
        return nullptr;
      else
        {
          iar_generator<false> gen(aut, pairs);
          return gen.run();
        }
    else
      {
        iar_generator<true> gen(aut, pairs);
        return gen.run();
      }
  }

  twa_graph_ptr
  iar(const const_twa_graph_ptr& aut)
  {
    if (auto res = iar_maybe(aut))
      return res;
    throw std::runtime_error("iar() expects Rabin-like or Streett-like input");
  }
}
