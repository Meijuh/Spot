// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2012, 2014 Laboratoire de Recherche et
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
#include "tgba/tgbagraph.hh"
#include "dotty.hh"
#include "dottydec.hh"
#include "tgba/bddprint.hh"
#include "reachiter.hh"
#include "misc/escape.hh"
#include "tgba/tgbagraph.hh"
#include "tgba/formula2bdd.hh"

namespace spot
{
  namespace
  {
    class dotty_output
    {
      std::ostream& os_;
      bool opt_force_acc_trans_ = false;
      bool opt_horizontal_ = true;
      bool opt_name_ = true;
      bool opt_circles_ = false;
      bool mark_states_ = false;
      const_tgba_digraph_ptr aut_;

    public:
      dotty_output(std::ostream& os, const char* options)
	: os_(os)
      {
	if (options)
	  while (char c = *options++)
	    switch (c)
	      {
	      case 'c':
		opt_circles_ = true;
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
	      case 'v':
		opt_horizontal_ = false;
		break;
	      case 't':
		opt_force_acc_trans_ = false;
		break;
	      default:
		throw std::runtime_error
		  (std::string("unknown option for dotty(): ") + c);
	      }
      }

      void
      start()
      {
	os_ << "digraph G {\n";
	if (opt_horizontal_)
	  os_ << "  rankdir=LR\n";
	if (opt_name_)
	  if (auto n = aut_->get_named_prop<std::string>("automaton-name"))
	    escape_str(os_ << "  label=\"", *n) << "\"\n  labelloc=\"t\"\n";
	if (opt_circles_)
	  os_ << "  node [shape=\"circle\"]\n";
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
	os_ << "  " << s << " [label=\"" << escape_str(aut_->format_state(s))
	    << '"';
	if (mark_states_ && aut_->state_is_accepting(s))
	  os_ << ", peripheries=2";
	os_ << "]\n";
      }

      void
      process_link(const tgba_digraph::trans_storage_t& t)
      {
	std::string label = bdd_format_formula(aut_->get_dict(), t.cond);
	label = escape_str(label);
	if (!mark_states_)
	  if (auto a = t.acc)
	    {
	      label += "\\n";
	      label += aut_->acc().format(a);
	    }
	os_ << "  " << t.src << " -> " << t.dst
	    << " [label=\"" + label + "\"]\n";
      }

      void print(const const_tgba_digraph_ptr& aut)
      {
	aut_ = aut;
	mark_states_ = !opt_force_acc_trans_ && aut_->has_state_based_acc();
	start();
	unsigned ns = aut_->num_states();
	for (unsigned n = 0; n < ns; ++n)
	  {
	    process_state(n);
	    for (auto& t: aut_->out(n))
	      process_link(t);
	  }
	end();
      }
    };


    class dotty_bfs : public tgba_reachable_iterator_breadth_first
    {
    public:
      dotty_bfs(std::ostream& os, const_tgba_ptr a, bool mark_accepting_states,
		const char* options, dotty_decorator* dd)
	: tgba_reachable_iterator_breadth_first(a), os_(os),
	  mark_accepting_states_(mark_accepting_states), dd_(dd),
	  sba_(std::dynamic_pointer_cast<const tgba_digraph>(a))
      {
	if (options)
	  while (char c = *options++)
	    switch (c)
	      {
	      case 'c':
		opt_circles = true;
		break;
	      case 'h':
		opt_horizontal = true;
		break;
	      case 'n':
		opt_name = true;
	        break;
	      case 'N':
		opt_name = false;
	        break;
	      case 'v':
		opt_horizontal = false;
		break;
	      case 't':
		mark_accepting_states_ = false;
		break;
	      default:
		throw std::runtime_error
		  (std::string("unknown option for dotty(): ") + c);
	      }
      }

      void
      start()
      {
	os_ << "digraph G {\n";
	if (opt_horizontal)
	  os_ << "  rankdir=LR\n";
	if (opt_name)
	  if (auto n = aut_->get_named_prop<std::string>("automaton-name"))
	    escape_str(os_ << "  label=\"", *n) << "\"\n  labelloc=\"t\"\n";
	if (opt_circles)
	  os_ << "  node [shape=\"circle\"]\n";
	os_ << "  0 [label=\"\", style=invis, ";
	os_ << (opt_horizontal ? "width" : "height");
	os_ << "=0]\n  0 -> 1\n";
      }

      void
      end()
      {
	os_ << '}' << std::endl;
      }

      void
      process_state(const state* s, int n, tgba_succ_iterator* si)
      {
	bool accepting;

	if (mark_accepting_states_)
	  {
	    if (sba_)
	      {
		accepting = sba_->state_is_accepting(s);
	      }
	    else
	      {
		si->first();
		auto a = si->current_acceptance_conditions();
		accepting = !si->done() && aut_->acc().accepting(a);
	      }
	  }
	else
	  {
	    accepting = false;
	  }

	os_ << "  " << n << ' '
	    << dd_->state_decl(aut_, s, n, si,
			       escape_str(aut_->format_state(s)),
			       accepting)
	    << '\n';
      }

      void
      process_link(const state* in_s, int in,
		   const state* out_s, int out, const tgba_succ_iterator* si)
      {
	std::string label =
	  bdd_format_formula(aut_->get_dict(),
			     si->current_condition());
	if (!mark_accepting_states_)
	  if (auto a = si->current_acceptance_conditions())
	    {
	      label += "\n";
	      label += aut_->acc().format(a);
	    }

	std::string s = aut_->transition_annotation(si);
	if (!s.empty())
	  {
	    if (*label.rbegin() != '\n')
	      label += '\n';
	    label += s;
	  }

	os_ << "  " << in << " -> " << out << ' '
	    << dd_->link_decl(aut_, in_s, in, out_s, out, si,
			      escape_str(label))
	    << '\n';
      }

    private:
      std::ostream& os_;
      bool mark_accepting_states_;
      dotty_decorator* dd_;
      const_tgba_digraph_ptr sba_;
      bool opt_horizontal = true;
      bool opt_name = true;
      bool opt_circles = false;
    };
  }

  std::ostream&
  dotty_reachable(std::ostream& os, const const_tgba_ptr& g,
		  bool assume_sba, const char* options,
		  dotty_decorator* dd)
  {
    if (dd)
      {
	dotty_bfs d(os, g, assume_sba || g->has_state_based_acc(), options, dd);
	d.run();
	return os;
      }
    dotty_output d(os, options);
    auto aut = make_tgba_digraph(g, tgba::prop_set::all());
    if (assume_sba)
      aut->prop_state_based_acc();
    d.print(aut);
    return os;
  }


}
