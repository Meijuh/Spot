// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2012, 2014-2017 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
// Copyright (C) 2003, 2004  Laboratoire d'Informatique de Paris 6 (LIP6),
// département Systèmes Répartis Coopératifs (SRC), Université Pierre
// et Marie Curie.
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

#include <ostream>
#include <sstream>
#include <stdexcept>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/dot.hh>
#include <spot/twa/bddprint.hh>
#include <spot/twaalgos/reachiter.hh>
#include <spot/misc/escape.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/kripke/fairkripke.hh>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <ctype.h>
#include <utility>


namespace spot
{
  namespace
  {
    constexpr int MAX_BULLET = 20;

    static constexpr const char palette[][8] =
      {
        "#1F78B4", /* blue */
        "#FF4DA0", /* pink */
        "#FF7F00", /* orange */
        "#6A3D9A", /* purple */
        "#33A02C", /* green */
        "#E31A1C", /* red */
        "#C4C400", /* yellowish */
        "#505050", /* gray */
        "#6BF6FF", /* light blue */
        "#FF9AFF", /* light pink */
        "#FF9C67", /* light orange */
        "#B2A4FF", /* light purple */
        "#A7ED79", /* light green */
        "#FF6868", /* light red */
        "#FFE040", /* light yellowish */
        "#C0C090", /* light gray */
      };

    constexpr int palette_mod = sizeof(palette) / sizeof(*palette);

    class dotty_output final
    {
      // Keep all 0/false-initialized values together.
      std::vector<std::string>* sn_ = nullptr;
      std::map<unsigned, unsigned>* highlight_edges_ = nullptr;
      std::map<unsigned, unsigned>* highlight_states_ = nullptr;
      std::vector<std::pair<unsigned, unsigned>>* sprod_ = nullptr;
      std::vector<unsigned>* orig_ = nullptr;
      std::set<unsigned>* incomplete_ = nullptr;
      std::string* name_ = nullptr;
      std::map<std::pair<int, int>, int> univ_done;

      acc_cond::mark_t inf_sets_ = 0U;
      acc_cond::mark_t fin_sets_ = 0U;
      unsigned opt_shift_sets_ = 0;
      enum { ShapeAuto = 0, ShapeCircle, ShapeEllipse } opt_shape_ = ShapeAuto;
      bool opt_force_acc_trans_ = false;
      bool opt_vertical_ = false;
      bool opt_name_ = false;
      bool opt_show_acc_ = false;
      bool mark_states_ = false;
      bool dcircles_ = false;
      bool opt_scc_ = false;
      bool opt_html_labels_ = false;
      bool opt_state_labels_ = false;
      bool opt_rainbow = false;
      bool opt_bullet = false;
      bool opt_bullet_but_buchi = false;
      bool opt_all_bullets = false;
      bool opt_ordered_edges_ = false;
      bool opt_numbered_edges_ = false;
      bool opt_orig_show_ = false;
      bool max_states_given_ = false; // related to max_states_

      const_twa_graph_ptr aut_;
      std::string opt_font_;
      std::string opt_node_color_;
      std::ostream& os_;
      bool opt_want_state_names_ = true;
      unsigned max_states_ = -1U; // related to max_states_given_

      bool opt_shared_univ_dest_ = true;

    public:

      unsigned max_states()
      {
        return max_states_;
      }

      bool max_states_given()
      {
        return max_states_given_;
      }

      void
      parse_opts(const char* options)
      {
        const char* orig = options;
        while (char c = *options++)
          switch (c)
            {
            case '.':
              {
                // Copy the value in a string, so future calls to
                // parse_opts do not fail if the environment has
                // changed.  (This matters particularly in an ipython
                // notebook, where it is tempting to redefine
                // SPOT_DOTDEFAULT.)
                static std::string def = []()
                  {
                    auto s = getenv("SPOT_DOTDEFAULT");
                    return s ? s : "";
                  }();
                // Prevent infinite recursions...
                if (orig == def.c_str())
                  throw std::runtime_error
                    (std::string("SPOT_DOTDEFAULT should not contain '.'"));
                if (!def.empty())
                  parse_opts(def.c_str());
                break;
              }
            case '+':
              {
                char* end;
                opt_shift_sets_ = strtoul(options, &end, 10);
                if (options == end)
                  throw std::runtime_error
                    ("missing number after '+' in print_dot() options");
                options = end;
                break;
              }
            case '<':
              {
                char* end;
                max_states_ = strtoul(options, &end, 10);
                if (options == end)
                  throw std::runtime_error
                    ("missing number after '<' in print_dot() options");
                if (max_states_ == 0)
                  {
                    max_states_ = -1U;
                    max_states_given_ = false;
                  }
                else
                  {
                    max_states_given_ = true;
                  }
                options = end;
                break;
              }
            case '#':
              opt_numbered_edges_ = true;
              break;
            case '1':
              opt_want_state_names_ = false;
              break;
            case 'a':
              opt_show_acc_ = true;
              break;
            case 'b':
              opt_bullet = true;
              opt_bullet_but_buchi = false;
              break;
            case 'B':
              opt_bullet = true;
              opt_bullet_but_buchi = true;
              break;
            case 'c':
              opt_shape_ = ShapeCircle;
              break;
            case 'C':
              if (*options != '(')
                throw std::runtime_error
                  ("invalid node color specification for print_dot()");
              {
                auto* end = strchr(++options, ')');
                if (!end)
                  throw std::runtime_error
                    ("invalid node color specification for print_dot()");
                opt_node_color_ = std::string(options, end - options);
                options = end + 1;
              }
              break;
            case 'd':
              opt_orig_show_ = true;
              break;
            case 'e':
              opt_shape_ = ShapeEllipse;
              break;
            case 'f':
              if (*options != '(')
                throw std::runtime_error
                  ("invalid font specification for print_dot()");
              {
                auto* end = strchr(++options, ')');
                if (!end)
                  throw std::runtime_error
                    ("invalid font specification for print_dot()");
                opt_font_ = std::string(options, end - options);
                options = end + 1;
              }
              break;
            case 'h':
              opt_vertical_ = false;
              break;
            case 'k':
              opt_state_labels_ = true;
              break;
            case 'n':
              opt_name_ = true;
              break;
            case 'N':
              opt_name_ = false;
              break;
            case 'o':
              opt_ordered_edges_ = true;
              break;
            case 'r':
              opt_html_labels_ = true;
              opt_rainbow = true;
              break;
            case 'R':
              opt_html_labels_ = true;
              opt_rainbow = false;
              break;
            case 's':
              opt_scc_ = true;
              break;
            case 'v':
              opt_vertical_ = true;
              break;
            case 't':
              opt_force_acc_trans_ = true;
              break;
            case 'y':
              opt_shared_univ_dest_ = false;
              break;
            default:
              throw std::runtime_error
                (std::string("unknown option for print_dot(): ") + c);
            }
      }

      dotty_output(std::ostream& os, const char* options)
        : os_(os)
      {
        parse_opts(options ? options : ".");
      }

      void
      output_set(std::ostream& os, int v) const
      {
        v += opt_shift_sets_;
        if (opt_bullet && (v >= 0) & (v <= MAX_BULLET))
          {
            static const char* const tab[MAX_BULLET + 1] = {
              "⓿", "❶", "❷", "❸",
              "❹", "❺", "❻", "❼",
              "❽", "❾", "❿", "⓫",
              "⓬", "⓭", "⓮", "⓯",
              "⓰", "⓱", "⓲", "⓳",
              "⓴",
            };
            os << tab[v];
          }
        else
          {
            os << v;
          }
      }

      void
      output_set(acc_cond::mark_t a) const
      {
        if (!opt_all_bullets)
          os_ << '{';
        const char* space = "";
        for (auto v: a.sets())
          {
            if (!opt_all_bullets)
              os_ << space;
            output_set(os_, v);
            space = ",";
          }
        if (!opt_all_bullets)
          os_ << '}';
      }

      const char*
      html_set_color(int v) const
      {
        if (opt_rainbow)
          return palette[(v + opt_shift_sets_) % palette_mod];
        // Color according to Fin/Inf
        if (inf_sets_.has(v))
          {
            if (fin_sets_.has(v))
              return palette[2];
            else
              return palette[0];
          }
        else
          {
            return palette[1];
          }
      }

      void
      output_html_set_aux(std::ostream& os, int v) const
      {
        os << "<font color=\"" << html_set_color(v) << "\">";
        output_set(os, v);
        os << "</font>";
      }

      void
      output_html_set(int v) const
      {
        output_html_set_aux(os_, v);
      }

      void
      output_html_set(acc_cond::mark_t a) const
      {
        if (!opt_all_bullets)
          os_ << '{';
        const char* space = "";
        for (auto v: a.sets())
          {
            if (!opt_all_bullets)
              os_ << space;
            output_html_set(v);
            space = ",";
          }
        if (!opt_all_bullets)
          os_ << '}';
      }

      std::string
      state_label(unsigned s) const
      {
        bdd label = bddfalse;
        for (auto& t: aut_->out(s))
          {
            label = t.cond;
            break;
          }
        if (label == bddfalse
            && incomplete_ && incomplete_->find(s) != incomplete_->end())
          return "...";
        return bdd_format_formula(aut_->get_dict(), label);
      }

      std::string string_dst(int dst, int color_num = -1)
      {
        std::ostringstream tmp_dst;
        tmp_dst << dst;
        if (!opt_shared_univ_dest_ && color_num >= 0)
          tmp_dst << '.' << color_num;
        return tmp_dst.str();
      }

      void
      print_dst(int dst, bool print_edges = false,
                const char* style = nullptr, int color_num = -1)
      {
        int& univ = univ_done[std::make_pair(dst, color_num)];
        if (univ == 2)
          return;
        std::string dest = string_dst(dst, color_num);
        if (univ == 0)
          os_ << "  " << dest << " [label=<>,shape=point]\n";
        if (print_edges)
          {
            for (unsigned d: aut_->univ_dests(dst))
              {
                os_ << "  " << dest << " -> " << d;
                if (style && *style)
                  os_ << " [" << style << ']';
                os_ << '\n';
              }
            univ = 2;
          }
        else
          {
            univ = 1;
          }
      }

      void print_acceptance_for_human()
      {
        const char* nl = opt_html_labels_ ? "<br/>" : "\\n";
        if (aut_->acc().is_generalized_buchi())
          {
            if (aut_->acc().is_all())
              os_ << nl << "[all]";
            else if (aut_->acc().is_buchi())
              os_ << nl << "[Büchi]";
            else
              os_ << nl << "[gen. Büchi " << aut_->num_sets() << ']';
          }
        else if (aut_->acc().is_generalized_co_buchi())
          {
            if (aut_->acc().is_none())
              os_ << nl << "[none]";
            else if (aut_->acc().is_co_buchi())
              os_ << nl << "[co-Büchi]";
            else
              os_ << nl << "[gen. co-Büchi " << aut_->num_sets() << ']';
          }
        else
          {
            int r = aut_->acc().is_rabin();
            assert(r != 0);
            if (r > 0)
              {
                os_ << nl << "[Rabin " << r << ']';
              }
            else
              {
                r = aut_->acc().is_streett();
                assert(r != 0);
                if (r > 0)
                  {
                    os_ << nl << "[Streett " << r << ']';
                  }
                else
                  {
                    std::vector<unsigned> pairs;
                    if (aut_->acc().is_generalized_rabin(pairs))
                      {
                        os_ << nl << "[gen. Rabin " << pairs.size() << ']';
                      }
                    else
                      {
                        bool max = false;
                        bool odd = false;
                        if (aut_->acc().is_parity(max, odd))
                          {
                            os_ << nl << "[parity "
                                << (max ? "max " : "min ")
                                << (odd ? "odd " : "even ")
                                << aut_->num_sets() << ']';
                          }
                        else
                          {
                            std::vector<acc_cond::rs_pair> r_pairs;
                            bool r_like = aut_->acc().is_rabin_like(r_pairs);
                            unsigned rsz = r_pairs.size();
                            std::vector<acc_cond::rs_pair> s_pairs;
                            bool s_like = aut_->acc().is_streett_like(s_pairs);
                            unsigned ssz = s_pairs.size();
                            if (r_like && (!s_like || (rsz <= ssz)))
                              os_ << nl << "[Rabin-like " << rsz << ']';
                            else if (s_like && (!r_like || (ssz < rsz)))
                              os_ << nl << "[Streett-like " << ssz << ']';
                          }
                      }
                  }
              }
          }
      }

      void
      start()
      {
        if (opt_html_labels_)
          std::tie(inf_sets_, fin_sets_) =
            aut_->get_acceptance().used_inf_fin_sets();
        if (opt_bullet && aut_->num_sets() <= MAX_BULLET)
          opt_all_bullets = true;
        os_ << "digraph G {\n";
        if (!opt_vertical_)
          os_ << "  rankdir=LR\n";
        if (name_ || opt_show_acc_)
          {
            if (!opt_html_labels_)
              {
                os_ << "  label=\"";
                if (name_)
                  {
                    escape_str(os_, *name_);
                    if (opt_show_acc_)
                      os_ << "\\n";
                  }
                if (opt_show_acc_)
                  {
                    if (!dcircles_)
                      {
                        aut_->get_acceptance().to_text
                          (os_, [this](std::ostream& os, int v)
                           {
                             this->output_set(os, v);
                           });
                      }
                    print_acceptance_for_human();
                  }
                os_ << "\"\n";
              }
            else
              {
                os_ << "  label=<";
                if (name_)
                  {
                    escape_html(os_, *name_);
                    if (opt_show_acc_)
                      os_ << "<br/>";
                  }
                if (opt_show_acc_)
                  {
                    if (!dcircles_)
                      {
                        aut_->get_acceptance().to_html
                          (os_, [this](std::ostream& os, int v)
                           {
                             this->output_html_set_aux(os, v);
                           });
                      }
                    print_acceptance_for_human();
                  }
                os_ << ">\n";
              }
            os_ << "  labelloc=\"t\"\n";
          }
        switch (opt_shape_)
          {
          case ShapeCircle:
            os_ << "  node [shape=\"circle\"]\n";
            break;
          case ShapeEllipse:
            // Do not print anything.  Ellipse is
            // the default shape used by GraphViz.
            break;
          case ShapeAuto:
            SPOT_UNREACHABLE();
          }
        if (!opt_node_color_.empty())
          os_ << "  node [style=\"filled\", fillcolor=\""
              << opt_node_color_ << "\"]\n";
        if (!opt_font_.empty())
          os_ << "  fontname=\"" << opt_font_
              << "\"\n  node [fontname=\"" << opt_font_
              << "\"]\n  edge [fontname=\"" << opt_font_
              << "\"]\n";
        // Always copy the environment variable into a static string,
        // so that we (1) look it up once, but (2) won't crash if the
        // environment is changed.
        static std::string extra = []()
          {
            auto s = getenv("SPOT_DOTEXTRA");
            return s ? s : "";
          }();
        // Any extra text passed in the SPOT_DOTEXTRA environment
        // variable should be output at the end of the "header", so
        // that our setup can be overridden.
        if (!extra.empty())
          os_ << "  " << extra << '\n';
        os_ << "  I [label=\"\", style=invis, ";
        os_ << (opt_vertical_ ? "height" : "width");
        int init = (int) aut_->get_init_state_number();
        os_ << "=0]\n  I -> " << init;
        if (init >= 0)
          os_ << '\n';
        else
          os_ << " [arrowhead=onormal]\n";
      }

      void
      end()
      {
        os_ << '}' << std::endl;
      }

      void
      process_state(unsigned s)
      {
        if (mark_states_ && !dcircles_)
          {
            acc_cond::mark_t acc = 0U;
            for (auto& t: aut_->out(s))
              {
                acc = t.acc;
                break;
              }

            bool has_name = sn_ && s < sn_->size() && !(*sn_)[s].empty();

            os_ << "  " << s << " [label=";
            if (!opt_html_labels_)
              {
                os_ << '"';
                if (has_name)
                  escape_str(os_, (*sn_)[s]);
                else if (sprod_)
                  os_ << (*sprod_)[s].first << ',' << (*sprod_)[s].second;
                else
                  os_ << s;
                if (orig_ && s < orig_->size())
                  os_ << " (" << (*orig_)[s] << ')';
                if (acc)
                  {
                    os_ << "\\n";
                    output_set(acc);
                  }
                if (opt_state_labels_)
                  escape_str(os_ << "\\n", state_label(s));
                os_ << '"';
              }
            else
              {
                os_ << '<';
                if (has_name)
                  escape_html(os_, (*sn_)[s]);
                else if (sprod_)
                  os_ << (*sprod_)[s].first << ',' << (*sprod_)[s].second;
                else
                  os_ << s;
                if (orig_ && s < orig_->size())
                  os_ << " (" << (*orig_)[s] << ')';
                if (acc)
                  {
                    os_ << "<br/>";
                    output_html_set(acc);
                  }
                if (opt_state_labels_)
                  escape_html(os_ << "<br/>", state_label(s));
                os_ << '>';
              }
          }
        else
          {
            os_ << "  " << s << " [label=\"";
            if (sn_ && s < sn_->size() && !(*sn_)[s].empty())
              escape_str(os_, (*sn_)[s]);
            else if (sprod_)
              os_ << (*sprod_)[s].first << ',' << (*sprod_)[s].second;
            else
              os_ << s;
            if (orig_ && s < orig_->size())
              os_ << " (" << (*orig_)[s] << ')';
            if (opt_state_labels_)
              escape_str(os_ << "\\n", state_label(s));
            os_ << '"';
            // Use state_acc_sets(), not state_is_accepting() because
            // on co-Büchi automata we want to mark the rejecting
            // states.
            if (dcircles_ && aut_->state_acc_sets(s))
              os_ << ", peripheries=2";
          }
        if (highlight_states_)
          {
            auto iter = highlight_states_->find(s);
            if (iter != highlight_states_->end())
              {
                os_ << ", style=\"bold";
                if (!opt_node_color_.empty())
                  os_ << ",filled";
                os_ << "\", color=\"" << palette[iter->second % palette_mod]
                    << '"';
              }
          }
        os_ << "]\n";
        if (incomplete_ && incomplete_->find(s) != incomplete_->end())
          os_ << "  u" << s << " [label=\"...\", shape=none, width=0, height=0"
            "]\n  " << s << " -> u" << s << " [style=dashed]\n";
      }

      void
      process_link(const twa_graph::edge_storage_t& t, int number,
                   bool print_edges)
      {
        if (print_edges)
          {
            os_ << "  " << t.src << " -> " << (int)t.dst;
            if (aut_->is_univ_dest(t.dst) && highlight_edges_
                && !opt_shared_univ_dest_)
              {
                auto idx = aut_->get_graph().index_of_edge(t);
                auto iter = highlight_edges_->find(idx);
                if (iter != highlight_edges_->end())
                  os_ << '.' << iter->second % palette_mod;
              }
            std::string label;
            if (!opt_state_labels_)
              label = bdd_format_formula(aut_->get_dict(), t.cond);
            if (!opt_html_labels_)
              {
                os_ << " [label=\"";
                escape_str(os_, label);
                if (!mark_states_)
                  if (auto a = t.acc)
                    {
                      if (!opt_state_labels_)
                        os_ << "\\n";
                      output_set(a);
                    }
                os_ << '"';
              }
            else
              {
                os_ << " [label=<";
                escape_html(os_, label);
                if (!mark_states_)
                  if (auto a = t.acc)
                    {
                      if (!opt_state_labels_)
                        os_ << "<br/>";
                      output_html_set(a);
                    }
                os_ << '>';
              }
            if (opt_ordered_edges_ || opt_numbered_edges_)
              {
                os_ << ", taillabel=\"";
                if (opt_ordered_edges_)
                  os_ << number;
                if (opt_ordered_edges_ && opt_numbered_edges_)
                  os_ << ' ';
                if (opt_numbered_edges_)
                  os_ << '#' << aut_->get_graph().index_of_edge(t);
                os_ << '"';
              }
          }

        std::string highlight;
        int color_num = -1;
        if (highlight_edges_)
          {
            auto idx = aut_->get_graph().index_of_edge(t);
            auto iter = highlight_edges_->find(idx);
            if (iter != highlight_edges_->end())
              {
                std::ostringstream o;
                o << "style=bold, color=\""
                  << palette[iter->second % palette_mod]
                  << '"';
                highlight = o.str();
                if (print_edges)
                  os_ << ", " << highlight;
                if (!opt_shared_univ_dest_)
                  color_num = iter->second % palette_mod;
              }
          }
        if (print_edges)
          {
            if (aut_->is_univ_dest(t.dst))
              os_ << ", arrowhead=onormal";
            os_ << "]\n";
          }
        if (aut_->is_univ_dest(t.dst))
          print_dst(t.dst, print_edges, highlight.c_str(), color_num);
      }

      void print(const const_twa_graph_ptr& aut)
      {
        aut_ = aut;
        if (opt_want_state_names_)
          {
            sn_ = aut->get_named_prop<std::vector<std::string>>("state-names");
            // We have no names.  Do we have product sources?
            if (!sn_)
              {
                sprod_ = aut->get_named_prop
                  <std::vector<std::pair<unsigned, unsigned>>>
                  ("product-states");
                if (sprod_ && aut->num_states() != sprod_->size())
                  sprod_ = nullptr;
              }
          }
        if (opt_orig_show_)
          orig_ = aut->get_named_prop<std::vector<unsigned>>("original-states");
        if (opt_state_labels_)
          {
            // Verify that we can use state labels for this automaton.
            unsigned n = aut->num_states();
            for (unsigned s = 0; s < n; ++s)
              {
                bool first = true;
                bdd cond = bddfalse;
                for (auto& t: aut->out(s))
                  if (first)
                    {
                      cond = t.cond;
                      first = false;
                    }
                  else if (t.cond != cond)
                    {
                      opt_state_labels_ = false;
                      break;
                    }
              }
          }
        highlight_edges_ =
          aut->get_named_prop<std::map<unsigned, unsigned>>("highlight-edges");
        highlight_states_ =
          aut->get_named_prop<std::map<unsigned, unsigned>>("highlight-states");
        incomplete_ =
          aut->get_named_prop<std::set<unsigned>>("incomplete-states");
        if (opt_name_)
          name_ = aut_->get_named_prop<std::string>("automaton-name");
        mark_states_ = (!opt_force_acc_trans_
                        && aut_->prop_state_acc().is_true());
        dcircles_ = (mark_states_
                     && (!opt_bullet || opt_bullet_but_buchi)
                     && (aut_->acc().is_buchi() || aut_->acc().is_co_buchi()));
        if (opt_shape_ == ShapeAuto)
          {
            if (sn_ || sprod_ || aut->num_states() > 100
                || opt_state_labels_ || orig_)
              {
                opt_shape_ = ShapeEllipse;
                // If all state names are short, prefer circles.
                if (!opt_state_labels_ && !orig_ &&
                    sn_ && std::all_of(sn_->begin(), sn_->end(),
                                       [](const std::string& s)
                                       { return s.size() <= 2; }))
                  opt_shape_ = ShapeCircle;
              }
            else
              {
                opt_shape_ = ShapeCircle;
              }
          }
        auto si =
          std::unique_ptr<scc_info>(opt_scc_ ? new scc_info(aut) : nullptr);

        start();
        if (si)
          {
            if (aut->is_existential())
              si->determine_unknown_acceptance();

            unsigned sccs = si->scc_count();
            for (unsigned i = 0; i < sccs; ++i)
              {
                os_ << "  subgraph cluster_" << i << " {\n";

                // Color the SCC to indicate whether is it accepting.
                if (!si->is_useful_scc(i))
                  os_ << "  color=grey\n";
                else if (si->is_trivial(i))
                  os_ << "  color=black\n";
                else if (si->is_accepting_scc(i))
                  os_ << "  color=green\n";
                else if (si->is_rejecting_scc(i))
                  os_ << "  color=red\n";
                else
                  // May only occur if the call to
                  // determine_unknown_acceptance() above is removed.
                  os_ << "  color=orange\n";

                if (name_ || opt_show_acc_)
                  {
                    // Reset the label, otherwise the graph label would
                    // be inherited by the cluster.
                    os_ << "  label=\"\"\n";
                  }
                for (auto s: si->states_of(i))
                  {
                    process_state(s);
                    int trans_num = 0;
                    unsigned scc_of_s = si->scc_of(s);
                    for (auto& t : aut_->out(s))
                      for (unsigned d: aut_->univ_dests(t.dst))
                        if (si->scc_of(d) == scc_of_s)
                          {
                            process_link(t, trans_num++, false);
                            break;
                          }
                  }
                os_ << "  }\n";
              }
          }
        int init = (int) aut_->get_init_state_number();
        if (init < 0)
          print_dst(init, true);
        unsigned ns = aut_->num_states();
        for (unsigned n = 0; n < ns; ++n)
          {
            if (!si || !si->reachable_state(n))
              process_state(n);
            int trans_num = 0;
            for (auto& t: aut_->out(n))
              process_link(t, trans_num++, true);
          }
        end();
      }
    };
  } // anonymous namespace

  std::ostream&
  print_dot(std::ostream& os, const const_twa_ptr& g,
                  const char* options)
  {
    dotty_output d(os, options);
    // Enable automatic state labels for Kripke structure.
    if (std::dynamic_pointer_cast<const fair_kripke>(g))
      d.parse_opts("k");
    auto aut = std::dynamic_pointer_cast<const twa_graph>(g);
    if (!aut || (d.max_states_given() && aut->num_states() >= d.max_states()))
      aut = make_twa_graph(g, twa::prop_set::all(), true, d.max_states() - 1);
    d.print(aut);
    return os;
  }


}
