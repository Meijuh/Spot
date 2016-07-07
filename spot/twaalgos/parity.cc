// -*- coding: utf-8 -*-
// Copyright (C) 2016 Laboratoire de Recherche et Développement
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

#include <spot/twaalgos/parity.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/product.hh>
#include <vector>
#include <utility>
#include <functional>
#include <queue>

namespace spot
{
  namespace
  {
    unsigned change_set(unsigned x, unsigned num_sets,
                        bool change_kind, bool change_style)
    {
      // If the parity acceptance kind is changed,
      // then the index of the sets are reversed
      if (change_kind)
        x = num_sets - x - 1;
      // If the parity style is changed, then all the existing acceptance
      // sets are shifted
      x += change_style;
      return x;
    }

    void
    change_acc(twa_graph_ptr& aut, unsigned num_sets, bool change_kind,
               bool change_style, bool output_max, bool input_max)
    {
      for (auto& e: aut->edge_vector())
        if (e.acc)
          {
            unsigned msb = (input_max ? e.acc.max_set() : e.acc.min_set()) - 1;
            e.acc = acc_cond::mark_t{change_set(msb, num_sets, change_kind,
                                                change_style)};
          }
        else if (output_max && change_style)
          {
            // If the parity is changed, a new set is introduced.
            // This new set is used to mark all the transitions of the input
            // that don't belong to any acceptance sets.
            e.acc.set(0);
          }
    }
  }

  twa_graph_ptr
  change_parity(const const_twa_graph_ptr& aut,
                parity_kind kind, parity_style style)
  {
    return change_parity_here(make_twa_graph(aut, twa::prop_set::all()),
                              kind, style);
  }

  twa_graph_ptr
  change_parity_here(twa_graph_ptr aut, parity_kind kind, parity_style style)
  {
    bool current_max;
    bool current_odd;
    if (!aut->acc().is_parity(current_max, current_odd, true))
      throw new std::invalid_argument("change_parity: input must have a parity "
                                      "acceptance.");
    auto old_num_sets = aut->num_sets();

    bool output_max = true;
    switch (kind)
      {
        case parity_kind_max:
          output_max = true;
          break;
        case parity_kind_min:
          output_max = false;
          break;
        case parity_kind_same:
          output_max = current_max;
          break;
        case parity_kind_any:
          // If we need to change the style we may change the kind not to
          // introduce new accset.
          output_max = (((style == parity_style_odd && !current_odd)
                         || (style == parity_style_even && current_odd))
                        && old_num_sets % 2 == 0) != current_max;
          break;
      }

    bool change_kind = current_max != output_max;
    bool toggle_style = change_kind && (old_num_sets % 2 == 0);

    bool output_odd = true;
    switch (style)
      {
        case parity_style_odd:
          output_odd = true;
          break;
        case parity_style_even:
          output_odd = false;
          break;
        case parity_style_same:
          output_odd = current_odd;
          break;
        case parity_style_any:
          output_odd = current_odd != toggle_style;
          // If we need to change the kind we may change the style not to
          // introduce new accset.
          break;
      }

    current_odd = current_odd != toggle_style;
    bool change_style = false;
    auto num_sets = old_num_sets;
    // If the parity neeeds to be changed, then a new acceptance set is created.
    // The old acceptance sets are shifted
    if (output_odd != current_odd)
      {
        change_style = true;
        ++num_sets;
      }

    if (change_kind || change_style)
      {
        auto new_acc = acc_cond::acc_code::parity(output_max,
                                                  output_odd, num_sets);
        aut->set_acceptance(num_sets, new_acc);
      }
    change_acc(aut, old_num_sets, change_kind,
               change_style, output_max, current_max);
    return aut;
  }

  twa_graph_ptr
  cleanup_parity(const const_twa_graph_ptr& aut, bool keep_style)
  {
    auto result = make_twa_graph(aut, twa::prop_set::all());
    return cleanup_parity_here(result, keep_style);
  }

  twa_graph_ptr
  cleanup_parity_here(twa_graph_ptr aut, bool keep_style)
  {
    bool current_max;
    bool current_odd;
    if (!aut->acc().is_parity(current_max, current_odd, true))
      throw new std::invalid_argument("cleanup_parity: input "
                                      "must have a parity acceptance.");
    auto num_sets = aut->num_sets();
    if (num_sets == 0)
      return aut;

    // Compute all the used sets
    auto used_in_aut = acc_cond::mark_t();
    for (auto& t: aut->edges())
      {
        if (current_max)
          {
            auto maxset = t.acc.max_set();
            if (maxset)
              t.acc = acc_cond::mark_t{maxset - 1};
          }
        else
          {
            t.acc = t.acc.lowest();
          }
        used_in_aut |= t.acc;
      }
    if (used_in_aut)
    {
      // Never remove the least significant acceptance set, and mark the
      // acceptance set 0 to keep the style if needed.
      if (current_max || keep_style)
        used_in_aut.set(0);
      if (!current_max)
        used_in_aut.set(num_sets - 1);

      // Fill the vector shift with the new acceptance sets
      std::vector<unsigned> shift(num_sets);
      int prev_used = -1;
      bool change_style = false;
      unsigned new_index = 0;
      for (auto i = 0U; i < num_sets; ++i)
        if (used_in_aut.has(i))
          {
            if (prev_used == -1)
              change_style = i % 2 != 0;
            else if ((i + prev_used) % 2 != 0)
              ++new_index;
            shift[i] = new_index;
            prev_used = i;
          }

      // Update all the transitions with the vector shift
      for (auto& t: aut->edges())
        {
          auto maxset = t.acc.max_set();
          if (maxset)
            t.acc = acc_cond::mark_t{shift[maxset - 1]};
        }
      auto new_num_sets = new_index + 1;
      if (new_num_sets < num_sets)
        {
          auto new_acc = acc_cond::acc_code::parity(current_max,
                                                    current_odd != change_style,
                                                    new_num_sets);
          aut->set_acceptance(new_num_sets, new_acc);
        }
    }
    else
      {
        if ((current_max && current_odd)
           || (!current_max && current_odd != (num_sets % 2 == 0)))
          aut->set_acceptance(0, acc_cond::acc_code::t());
        else
          aut->set_acceptance(0, acc_cond::acc_code::f());
      }
    return aut;
  }

  twa_graph_ptr
  colorize_parity(const const_twa_graph_ptr& aut, bool keep_style)
  {
    return colorize_parity_here(make_twa_graph(aut, twa::prop_set::all()),
                                keep_style);
  }

  twa_graph_ptr
  colorize_parity_here(twa_graph_ptr aut, bool keep_style)
  {
    bool current_max;
    bool current_odd;
    if (!aut->acc().is_parity(current_max, current_odd, true))
      throw new std::invalid_argument("colorize_parity: input "
                                      "must have a parity acceptance.");

    bool has_empty = false;
    for (const auto& e: aut->edges())
      if (!e.acc)
        {
          has_empty = true;
          break;
        }
    auto num_sets = aut->num_sets();
    int incr = 0;
    if (has_empty)
      {
        // If the automaton has a transition that belong to any set, we need to
        // introduce a new acceptance set.
        // We may want to add a second acceptance set to keep the style of
        // the parity acceptance
        incr = 1 + (keep_style && current_max);
        num_sets += incr;
        bool new_style = current_odd == (keep_style || !current_max);
        auto new_acc = acc_cond::acc_code::parity(current_max,
                                                  new_style, num_sets);
        aut->set_acceptance(num_sets, new_acc);
      }
    if (current_max)
      {
        --incr;
        for (auto& e: aut->edges())
          {
            auto maxset = e.acc.max_set();
            e.acc = acc_cond::mark_t{maxset ? maxset + incr : incr};
          }
      }
    else
      {
        auto unused_mark = num_sets - incr;
        for (auto& e: aut->edges())
          e.acc = e.acc ? e.acc.lowest() : acc_cond::mark_t{unused_mark};
      }
    return aut;
  }

  namespace
  {
    using state_history_value_t = unsigned;

    class state_history : public std::vector<state_history_value_t>
    {
    public:

      using value_t = state_history_value_t;

      state_history(unsigned left_num_sets, unsigned right_num_sets) :
        left_num_sets_(left_num_sets),
        right_num_sets_(right_num_sets)
      {
        resize(left_num_sets + right_num_sets, 0);
      }

      value_t get_left(value_t right) const
      {
        return get(right, true);
      }

      value_t get_right(value_t left) const
      {
        return get(left, false);
      }

      void set_left(value_t right, value_t val)
      {
        set(right, true, val);
      }

      void set_right(value_t left, value_t val)
      {
        set(left, false, val);
      }

      unsigned get_left_num_sets() const
      {
        return left_num_sets_;
      }

      unsigned get_right_num_sets() const
      {
        return right_num_sets_;
      }

      value_t get_max_acc_set() const
      {
        // i is the index of the resulting automaton acceptance set
        // If i is even, it means that the according set is a set with
        // transitions that need to be infinitly often as the
        // acceptance is a parity even. Then k, the index of the
        // first automaton must be even too.
        unsigned l = right_num_sets_;
        while (l-- > 0)
          {
            auto k = get_left(l);
            bool can_jump = (k & l & 1) != 1;
            if (!can_jump)
              --k;
            auto new_l = get_right(k);
            if (new_l >= l)
              return k + l;
            else if (can_jump)
              l = new_l + 1;
          }
        return 0;
      }

      state_history make_succ(value_t left_acc_set, value_t right_acc_set) const
      {
        auto mat = state_history(*this);
        mat.clean_here();
        for (unsigned i = 0; i < right_num_sets_; ++i)
          {
            auto old = mat.get_left(i);
            mat.set_left(i, std::max(left_acc_set, old));
          }
        for (unsigned i = 0; i < left_num_sets_; ++i)
          {
            auto old = mat.get_right(i);
            mat.set_right(i, std::max(right_acc_set, old));
          }
        return mat;
      }

      void clean_here()
      {
        auto mat = state_history(*this);
        for (unsigned l = 0; l < right_num_sets_; ++l)
          {
            set_left(l, 0);
            for (unsigned k = 0; k < left_num_sets_; ++k)
              {
                if (mat.get_right(k) < l)
                  set_left(l, std::min(mat.get_left(l), k));
                else
                  break;
              }
          }
        for (unsigned k = 0; k < left_num_sets_; ++k)
          {
            set_right(k, 0);
            for (unsigned l = 0; l < right_num_sets_; ++l)
              {
                if (mat.get_left(l) < k)
                  set_right(k, std::min(mat.get_right(k), l));
                else
                  break;
              }
          }
      }

    private:
      const unsigned left_num_sets_;
      const unsigned right_num_sets_;

      value_t get(value_t index, bool first) const
      {
        return at(index + (first ? 0 : right_num_sets_));
      }

      void set(value_t index, bool first, value_t val)
      {
        at(index + (first ? 0 : right_num_sets_)) = val;
      }
    };

    struct state_history_hash
    {
      size_t
      operator()(const state_history& mat) const
      {
        unsigned result = 0;
        for (unsigned i = 0; i < mat.get_left_num_sets(); ++i)
          result = wang32_hash(result ^ wang32_hash(mat.get_right(i)));
        for (unsigned i = 0; i < mat.get_right_num_sets(); ++i)
          result = wang32_hash(result ^ wang32_hash(mat.get_left(i)));
        return result;
      }
    };

    using sh_label_t = unsigned;

    class state_history_set
    {
    private:
      using value_t = state_history::value_t;

    public:
      sh_label_t
      push_state_history(state_history sh)
      {
        auto p = sh2l_.emplace(sh, 0);
        if (p.second)
          {
            l2sh_.push_back(p.first);
            p.first->second = l2sh_.size() - 1;
          }
        return p.first->second;
      }

      std::pair<sh_label_t, value_t>
      push_state_history(sh_label_t label,
                         value_t left_acc_set, value_t right_acc_set)
      {
        state_history new_sh = l2sh_[label]->first;
        auto succ = new_sh.make_succ(left_acc_set, right_acc_set);
        auto max_acc_set = succ.get_max_acc_set();
        return std::make_pair(push_state_history(succ), max_acc_set);
      }

      std::pair<sh_label_t, value_t>
      get_succ(sh_label_t current_sh,
               value_t left_acc_set, value_t right_acc_set)
      {
        auto f_args = std::make_tuple(current_sh, left_acc_set, right_acc_set);
        auto p = succ_.emplace(f_args, std::make_pair(0, 0));
        if (p.second)
          {
            p.first->second =
              push_state_history(current_sh, left_acc_set, right_acc_set);
          }
        return p.first->second;
      }

    private:
      using sh_dict_t = std::unordered_map<const state_history,
                                           value_t,
                                           state_history_hash>;
      sh_dict_t sh2l_;

      struct sh_succ_hash
      {
        size_t
        operator()(std::tuple<sh_label_t, value_t, value_t> x) const
        {
          return wang32_hash(std::get<0>(x) ^ wang32_hash(std::get<1>(x)
                             ^ wang32_hash(std::get<2>(x))));
        }
      };
      std::unordered_map<std::tuple<sh_label_t, value_t, value_t>,
                                    std::pair<sh_label_t, value_t>,
                                    sh_succ_hash> succ_;
      std::vector<sh_dict_t::const_iterator> l2sh_;
    };

    using product_state_t = std::tuple<unsigned, unsigned, sh_label_t>;

    struct product_state_hash
    {
      size_t
      operator()(product_state_t s) const
      {
        return wang32_hash(std::get<0>(s) ^ wang32_hash(std::get<1>(s)
                           ^ wang32_hash(std::get<2>(s))));
      }
    };


    twa_graph_ptr
    parity_product_aux(twa_graph_ptr& left, twa_graph_ptr& right)
    {
      std::unordered_map<product_state_t, unsigned, product_state_hash> s2n;
      state_history_set sh_set;
      std::queue<std::pair<product_state_t, unsigned>> todo;
      auto res = make_twa_graph(left->get_dict());
      res->copy_ap_of(left);
      res->copy_ap_of(right);
      unsigned left_num_sets = left->num_sets();
      unsigned right_num_sets = right->num_sets();
      unsigned z_size = left_num_sets + right_num_sets - 1;
      auto z = acc_cond::acc_code::parity(true, false, z_size);
      res->set_acceptance(z_size, z);

      auto v = new product_states;
      res->set_named_prop("product-states", v);

      auto new_state =
        [&](const sh_label_t sh_label,
            unsigned left_state, unsigned right_state,
            unsigned left_acc_set, unsigned right_acc_set)
        -> std::pair<unsigned, unsigned>
        {
          auto succ = sh_set.get_succ(sh_label, left_acc_set, right_acc_set);
          product_state_t x(left_state, right_state, succ.first);
          auto p = s2n.emplace(x, 0);
          if (p.second)                 // This is a new state
          {
            auto new_state = res->new_state();
            p.first->second = new_state;
            v->push_back(std::make_pair(left_state, right_state));
            todo.emplace(x, new_state);
          }
          return std::make_pair(p.first->second, succ.second);
        };

      state_history init_state_history(left_num_sets, right_num_sets);
      auto init_sh_label = sh_set.push_state_history(init_state_history);
      product_state_t init_state(left->get_init_state_number(),
                               right->get_init_state_number(), init_sh_label);
      auto init_state_index = res->new_state();
      s2n.emplace(init_state, init_state_index);
      todo.emplace(init_state, init_state_index);
      res->set_init_state(init_state_index);

      while (!todo.empty())
      {
        auto& top = todo.front();
        for (auto& l: left->out(std::get<0>(top.first)))
          for (auto& r: right->out(std::get<1>(top.first)))
          {
            auto cond = l.cond & r.cond;
            if (cond == bddfalse)
              continue;
            auto left_acc = l.acc.max_set() - 1;
            auto right_acc = r.acc.max_set() - 1;
            auto dst = new_state(std::get<2>(top.first), l.dst, r.dst,
                                 left_acc, right_acc);
            auto acc = acc_cond::mark_t{dst.second};
            res->new_edge(top.second, dst.first, cond, acc);
          }
        todo.pop();
      }

      // The product of two non-deterministic automata could be
      // deterministic.  likewise for non-complete automata.
      if (left->prop_universal() && right->prop_universal())
        res->prop_universal(true);
      if (left->prop_complete() && right->prop_complete())
        res->prop_complete(true);
      if (left->prop_stutter_invariant() && right->prop_stutter_invariant())
        res->prop_stutter_invariant(true);
      if (left->prop_inherently_weak() && right->prop_inherently_weak())
        res->prop_inherently_weak(true);
      if (left->prop_weak() && right->prop_weak())
        res->prop_weak(true);
      if (left->prop_terminal() && right->prop_terminal())
        res->prop_terminal(true);
      res->prop_state_acc(left->prop_state_acc() && right->prop_state_acc());
      return res;
    }
  }

  twa_graph_ptr
  parity_product(const const_twa_graph_ptr& left,
                 const const_twa_graph_ptr& right)
  {
    if (left->get_dict() != right->get_dict())
      throw std::runtime_error("parity_product: left and right automata "
                               "should share their bdd_dict");
    if (!(left->is_existential() && right->is_existential()))
      throw std::runtime_error("parity_product() does not support alternating "
                               "automata");
    auto first = change_parity(left, parity_kind_max, parity_style_even);
    auto second = change_parity(right, parity_kind_max, parity_style_even);
    cleanup_parity_here(first, true);
    cleanup_parity_here(second, true);
    colorize_parity_here(first, true);
    colorize_parity_here(second, true);
    return parity_product_aux(first, second);
  }
}
