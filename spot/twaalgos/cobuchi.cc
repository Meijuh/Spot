// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Développement
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

#include <spot/twaalgos/cobuchi.hh>

#include <spot/misc/bitvect.hh>
#include <spot/twaalgos/powerset.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/totgba.hh>

#include <stack>
#include <unordered_map>

#define DEBUG 0
#if DEBUG
#define debug std::cerr
#else
#define debug while (0) std::cout
#endif

namespace spot
{
  namespace
  {
    typedef std::pair<unsigned, unsigned> pair_state_nca;

    // Helper function that returns the called 'augmented subset construction'
    // of the given automaton, i.e. the product of the automaton  with its
    // powerset construction.
    //
    // 'aut_power' is the automaton that will be used for the powerset
    // construction and 'aut_prod' is the one that will be used for the
    // product. They may be confusing in the sense that why the same automaton
    // is not used for the product and the powerset construction. Actually,
    // when dealing with an automaton A with Rabin acceptance, it is firstly
    // converted into an automaton B with Streett-like acceptance. The powerset
    // construction of B happens to be isomorphic with the powerset construction
    // of A. Therefore, you would like to use A (which is smaller than B) for
    // the powerset construction and B for the product.
    static
    twa_graph_ptr
    aug_subset_cons(const const_twa_graph_ptr& aut_prod,
                    const const_twa_graph_ptr& aut_power,
                    bool named_states,
                    struct power_map& pmap)
    {
      twa_graph_ptr res = product(aut_prod, tgba_powerset(aut_power, pmap));

      if (named_states)
        {
          const product_states* res_map = res->get_named_prop
            <product_states>("product-states");

          auto v = new std::vector<std::string>;
          res->set_named_prop("state-names", v);

          auto get_st_name =
            [&](const pair_state_nca& x)
            {
              std::stringstream os;
              os << x.first << ",{";
              bool not_first = false;
              for (auto& a : pmap.states_of(x.second))
                {
                  if (not_first)
                    os << ',';
                  else
                    not_first = true;
                  os << a;
                }
              os << '}';
              return os.str();
            };

          unsigned num_states = res->num_states();
          for (unsigned i = 0; i < num_states; ++i)
            v->emplace_back(get_st_name((*res_map)[i]));
        }
      return res;
    }

    class nsa_to_nca_converter final
    {
      protected:
        struct power_map pmap_;                 // Sets of sts (powerset cons.).

        const_twa_graph_ptr aut_;               // The given automaton.
        bool state_based_;                      // Is it state based?
        std::vector<acc_cond::rs_pair> pairs_;  // All pairs of the acc. cond.
        unsigned nb_pairs_;                     // Nb pair in the acc. cond.
        bool named_states_;                     // Name states for display?
        twa_graph_ptr res_;                     // The augmented subset const.
        product_states* res_map_;               // States of the aug. sub. cons.
        scc_info si_;                           // SCC information.
        unsigned nb_states_;                    // Number of states.
        unsigned was_rabin_;                    // Was it Rabin before Streett?
        std::vector<unsigned>* orig_states_;    // Match old Rabin st. from new.
        unsigned orig_num_st_;                  // Rabin original nb states.

        // Keep information of states that are wanted to be seen infinitely
        // often (cf Header).
        void save_inf_nca_st(unsigned s, acc_cond::mark_t m,
                             vect_nca_info* nca_info)
        {
          if (was_rabin_ && m)
            {
              for (unsigned p = 0; p < nb_pairs_; ++p)
                if (pairs_[p].fin || m & pairs_[p].inf)
                  {
                    const pair_state_nca& st = (*res_map_)[s];
                    auto bv = make_bitvect(orig_num_st_);
                    for (unsigned state : pmap_.states_of(st.second))
                      bv->set(state);
                    assert(!was_rabin_
                            || ((int)(*orig_states_)[st.first] >= 0));
                    unsigned state = was_rabin_ ? (*orig_states_)[st.first]
                                              : st.first;
                    unsigned clause_nb = was_rabin_ ? p / 2 : p;
                    nca_info->push_back(new nca_st_info(clause_nb, state, bv));
                  }
            }
          else if (!was_rabin_)
            {
              const pair_state_nca& st = (*res_map_)[s];
              auto bv = make_bitvect(aut_->num_states());
              for (unsigned state : pmap_.states_of(st.second))
                bv->set(state);
              nca_info->push_back(new nca_st_info(0, st.first, bv));
            }
        }

        // Helper function that marks states that we want to see finitely often
        // and save some information about states that we want to see infinitely
        // often (cf Header).
        void set_marks_using(std::vector<bool>& nca_is_inf_state,
                             vect_nca_info* nca_info)
        {
          for (unsigned s = 0; s < nb_states_; ++s)
            {
              unsigned src_scc = si_.scc_of(s);
              if (nca_is_inf_state[s])
                {
                  acc_cond::mark_t m = 0u;
                  for (auto& e : res_->out(s))
                    {
                      if (nca_info && e.acc && (si_.scc_of(e.dst) == src_scc
                                                   || state_based_))
                        m |= e.acc;
                      e.acc = 0u;
                    }

                  if (nca_info)
                    save_inf_nca_st(s, m, nca_info);
                }
              else
                {
                  for (auto& e : res_->out(s))
                    {
                      if (si_.scc_of(e.dst) == src_scc || state_based_)
                          e.acc = acc_cond::mark_t({0});
                      else
                        e.acc = 0u;
                    }
                }
            }
        }

      public:

        nsa_to_nca_converter(const const_twa_graph_ptr ref_prod,
                             const const_twa_graph_ptr ref_power,
                             std::vector<acc_cond::rs_pair>& pairs,
                             bool named_states = false,
                             bool was_rabin = false,
                             unsigned orig_num_st = 0)
          : aut_(ref_prod),
            state_based_((bool)aut_->prop_state_acc()),
            pairs_(pairs),
            nb_pairs_(pairs.size()),
            named_states_(named_states),
            res_(aug_subset_cons(ref_prod, ref_power, named_states_, pmap_)),
            res_map_(res_->get_named_prop<product_states>("product-states")),
            si_(scc_info(res_)),
            nb_states_(res_->num_states()),
            was_rabin_(was_rabin),
            orig_num_st_(orig_num_st)
        {
          if (was_rabin)
            orig_states_ = ref_prod->get_named_prop<std::vector<unsigned>>
                                      ("original-states");
        }

        ~nsa_to_nca_converter()
        {}

        twa_graph_ptr run(vect_nca_info* nca_info)
        {
          std::vector<bool> nca_is_inf_state;    // Accepting or rejecting sts.
          nca_is_inf_state.resize(nb_states_, false);

          // Iterate over all SCCs and check for accepting states. A state 's'
          // is accepting if there is a cycle containing 's' that visits
          // finitely often all acceptance sets marked as Fin or infinitely
          // often acceptance sets marked by Inf.
          unsigned nb_scc = si_.scc_count();
          for (unsigned scc = 0; scc < nb_scc; ++scc)
            for (unsigned st : si_.states_on_acc_cycle_of(scc))
              nca_is_inf_state[st] = true;

          set_marks_using(nca_is_inf_state, nca_info);

          res_->prop_state_acc(state_based_);
          res_->set_co_buchi();
          res_->merge_edges();
          return res_;
        }
    };
  }


  twa_graph_ptr
  nsa_to_nca(const const_twa_graph_ptr& ref,
             bool named_states,
             vect_nca_info* nca_info)
  {
    twa_graph_ptr ref_tmp = ref->acc().is_parity() ? to_generalized_streett(ref)
                                                   : nullptr;
    std::vector<acc_cond::rs_pair> pairs;
    if (!(ref_tmp ? ref_tmp : ref)->acc().is_streett_like(pairs))
      throw std::runtime_error("nsa_to_nca() only works with Streett-like or "
                               "Parity acceptance condition");

    nsa_to_nca_converter nca_converter(ref_tmp ? ref_tmp : ref,
                                       ref_tmp ? ref_tmp : ref,
                                       pairs,
                                       named_states,
                                       false);
    return nca_converter.run(nca_info);
  }


  twa_graph_ptr
  dnf_to_nca(const const_twa_graph_ptr& ref,
             bool named_states,
             vect_nca_info* nca_info)
  {
    const acc_cond::acc_code& code = ref->get_acceptance();
    if (!code.is_dnf())
      throw std::runtime_error("dnf_to_nca() only works with DNF acceptance "
                               "condition");

    auto streett_aut = spot::dnf_to_streett(ref, true);

    std::vector<acc_cond::rs_pair> pairs;
    if (!streett_aut->acc().is_streett_like(pairs))
      throw std::runtime_error("dnf_to_nca() could not convert the original "
          "automaton into an intermediate Streett-like automaton");

    nsa_to_nca_converter nca_converter(streett_aut,
                                       ref,
                                       pairs,
                                       named_states,
                                       true,
                                       ref->num_states());
    return nca_converter.run(nca_info);
  }


  twa_graph_ptr
  to_dca(const const_twa_graph_ptr& aut, bool named_states)
  {
    const acc_cond::acc_code& code = aut->get_acceptance();

    std::vector<acc_cond::rs_pair> pairs;
    if (aut->acc().is_streett_like(pairs) || aut->acc().is_parity())
      return nsa_to_nca(aut, named_states);
    else if (code.is_dnf())
      return dnf_to_nca(aut, named_states);
    else
      throw std::runtime_error("to_dca() only works with Streett-like, Parity "
                               "or any acceptance condition in DNF");
  }
}
