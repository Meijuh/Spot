// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2012, 2014, 2015 Laboratoire de Recherche et
// Developpement de l'Epita (LRDE).
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
#include <stdexcept>
#include "twa/twagraph.hh"
#include "dot.hh"
#include "twa/bddprint.hh"
#include "reachiter.hh"
#include "misc/escape.hh"
#include "twa/twagraph.hh"
#include "twa/formula2bdd.hh"
#include "twaalgos/sccinfo.hh"
#include <cstdlib>
#include <cstring>
#include <ctype.h>


namespace spot
{
  namespace
  {
    constexpr int MAX_BULLET = 20;

    class dotty_output
    {
      std::ostream& os_;
      bool opt_force_acc_trans_ = false;
      bool opt_horizontal_ = true;
      bool opt_name_ = false;
      enum { ShapeAuto = 0, ShapeCircle, ShapeEllipse }
	opt_shape_ = ShapeAuto;
      bool opt_show_acc_ = false;
      bool mark_states_ = false;
      bool opt_scc_ = false;
      bool opt_html_labels_ = false;
      const_twa_graph_ptr aut_;
      std::vector<std::string>* sn_ = nullptr;
      std::string* name_ = nullptr;
      acc_cond::mark_t inf_sets_ = 0U;
      acc_cond::mark_t fin_sets_ = 0U;
      bool opt_rainbow = false;
      bool opt_bullet = false;
      bool opt_bullet_but_buchi = false;
      bool opt_all_bullets = false;
      bool opt_numbered_trans = false;
      bool opt_want_state_names_ = true;
      std::string opt_font_;

      const char* const palette9[9] =
	{
	  "#5DA5DA", /* blue */
	  "#F17CB0", /* pink */
	  "#FAA43A", /* orange */
	  "#B276B2", /* purple */
	  "#60BD68", /* green */
	  "#F15854", /* red */
	  "#B2912F", /* brown */
	  "#4D4D4D", /* gray */
	  "#DECF3F", /* yellow */
	};
      const char*const* palette = palette9;
      int palette_mod = 9;

    public:

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
	    case '1':
	      opt_want_state_names_ = false;
	      break;
	    case 'a':
	      opt_show_acc_ = true;
	      break;
	    case 'b':
	      opt_bullet = true;
	      break;
	    case 'B':
	      opt_bullet = true;
	      opt_bullet_but_buchi = true;
	      break;
	    case 'c':
	      opt_shape_ = ShapeCircle;
	      break;
	    case 'e':
	      opt_shape_ = ShapeEllipse;
	      break;
	    case 'f':
	      if (*options != '(')
		throw std::runtime_error
		  (std::string("invalid font specification for dotty()"));
	      {
		auto* end = strchr(++options, ')');
		if (!end)
		  throw std::runtime_error
		    (std::string("invalid font specification for dotty()"));
		opt_font_ = std::string(options, end - options);
		options = end + 1;
	      }
	      break;
	    case 'h':
	      opt_horizontal_ = true;
	      break;
	    case 'n':
	      opt_name_ = true;
	      break;
	    case 'N':
	      opt_name_ = false;
	      break;
	    case 'o':
	      opt_numbered_trans = true;
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
	      opt_horizontal_ = false;
	      break;
	    case 't':
	      opt_force_acc_trans_ = true;
	      break;
	    default:
	      throw std::runtime_error
		(std::string("unknown option for dotty(): ") + c);
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
	  return palette[v % palette_mod];
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

      void
      start()
      {
	if (opt_html_labels_)
	  std::tie(inf_sets_, fin_sets_) =
	    aut_->get_acceptance().used_inf_fin_sets();
	if (opt_bullet && aut_->num_sets() <= MAX_BULLET)
	  opt_all_bullets = true;
	os_ << "digraph G {\n";
	if (opt_horizontal_)
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
		  aut_->get_acceptance().to_text
		    (os_, [this](std::ostream& os, int v)
		     {
		       this->output_set(os, v);
		     });
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
		  aut_->get_acceptance().to_html
		    (os_, [this](std::ostream& os, int v)
		     {
		       this->output_html_set_aux(os, v);
		     });
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
	os_ << (opt_horizontal_ ? "width" : "height");
	os_ << "=0]\n  I -> " << aut_->get_init_state_number() << '\n';
      }

      void
      end()
      {
	os_ << '}' << std::endl;
      }

      void
      process_state(unsigned s)
      {
	if (mark_states_ &&
	    ((opt_bullet && !opt_bullet_but_buchi)
	     || aut_->num_sets() != 1))
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
		else
		  os_ << s;
		if (acc)
		  {
		    os_ << "\\n";
		    output_set(acc);
		  }
		os_ << '"';
	      }
	    else
	      {
		os_ << '<';
		if (has_name)
		  escape_html(os_, (*sn_)[s]);
		else
		  os_ << s;
		if (acc)
		  {
		    os_ << "<br/>";
		    output_html_set(acc);
		  }
		os_ << '>';
	      }
	    os_ << "]\n";

	  }
	else
	  {
	    os_ << "  " << s << " [label=\"";
	    if (sn_ && s < sn_->size() && !(*sn_)[s].empty())
	      escape_str(os_, (*sn_)[s]);
	    else
	      os_ << s;
	    os_ << '"';
	    // Use state_acc_sets(), not state_is_accepting() because
	    // on co-Büchi automata we want to mark the rejecting
	    // states.
	    if (mark_states_ && aut_->state_acc_sets(s))
	      os_ << ", peripheries=2";
	    os_ << "]\n";
	  }
      }

      void
      process_link(const twa_graph::edge_storage_t& t, int number)
      {
	std::string label = bdd_format_formula(aut_->get_dict(), t.cond);
	os_ << "  " << t.src << " -> " << t.dst;
	if (!opt_html_labels_)
	  {
	    os_ << " [label=\"";
	    escape_str(os_, label);
	    if (!mark_states_)
	      if (auto a = t.acc)
		{
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
		  os_ << "<br/>";
		  output_html_set(a);
		}
	    os_ << '>';
	  }
	if (opt_numbered_trans)
	  os_ << ",taillabel=\"" << number << '"';
	os_ << "]\n";
      }

      void print(const const_twa_graph_ptr& aut)
      {
	aut_ = aut;
	if (opt_want_state_names_)
	  sn_ = aut->get_named_prop<std::vector<std::string>>("state-names");
	if (opt_name_)
	  name_ = aut_->get_named_prop<std::string>("automaton-name");
	mark_states_ = !opt_force_acc_trans_ && aut_->has_state_based_acc();
	if (opt_shape_ == ShapeAuto)
	  {
	    if (sn_ || aut->num_states() > 100)
	      opt_shape_ = ShapeEllipse;
	    else
	      opt_shape_ = ShapeCircle;
	  }
	auto si =
	  std::unique_ptr<scc_info>(opt_scc_ ? new scc_info(aut) : nullptr);

	start();
	if (si)
	  {
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
		  process_state(s);
		os_ << "  }\n";
	      }
	  }
	unsigned ns = aut_->num_states();
	for (unsigned n = 0; n < ns; ++n)
	  {
	    if (!si || !si->reachable_state(n))
	      process_state(n);
	    int trans_num = 0;
	    for (auto& t: aut_->out(n))
	      process_link(t, trans_num++);
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
    auto aut = std::dynamic_pointer_cast<const twa_graph>(g);
    if (!aut)
      aut = make_twa_graph(g, twa::prop_set::all());
    d.print(aut);
    return os;
  }


}
