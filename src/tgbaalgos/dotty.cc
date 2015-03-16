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
#include "tgba/tgbagraph.hh"
#include "dotty.hh"
#include "tgba/bddprint.hh"
#include "reachiter.hh"
#include "misc/escape.hh"
#include "tgba/tgbagraph.hh"
#include "tgba/formula2bdd.hh"
#include "tgbaalgos/sccinfo.hh"
#include <cstdlib>

namespace spot
{
  namespace
  {
    class dotty_output
    {
      std::ostream& os_;
      bool opt_force_acc_trans_ = false;
      bool opt_horizontal_ = true;
      bool opt_name_ = false;
      bool opt_circles_ = false;
      bool opt_show_acc_ = false;
      bool mark_states_ = false;
      bool opt_scc_ = false;
      const_tgba_digraph_ptr aut_;
      std::vector<std::string>* sn_;
      std::string* name_ = nullptr;

    public:
      dotty_output(std::ostream& os, const char* options)
	: os_(os)
      {
	if (options)
	  while (char c = *options++)
	    switch (c)
	      {
	      case 'a':
		opt_show_acc_ = true;
		break;
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

      void
      start()
      {
	os_ << "digraph G {\n";
	if (opt_horizontal_)
	  os_ << "  rankdir=LR\n";
	if (name_ || opt_show_acc_)
	  {
	    os_ << "  label=\"";
	    if (name_)
	      {
		escape_str(os_, *name_);
		if (opt_show_acc_)
		  os_ << "\\n";
	      }
	    if (opt_show_acc_)
	      os_ << aut_->get_acceptance();
	    os_ << "\"\n  labelloc=\"t\"\n";
	  }
	if (opt_circles_)
	  os_ << "  node [shape=\"circle\"]\n";
	// Any extra text passed in the SPOT_DOTEXTRA environment
	// variable should be output at the end of the "header", so
	// that our setup can be overridden.
	static const char* extra = getenv("SPOT_DOTEXTRA");
	if (extra)
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
	os_ << "  " << s << " [label=\"";
	if (sn_ && s < sn_->size() && !(*sn_)[s].empty())
	  os_ << escape_str((*sn_)[s]);
	else
	  os_ << s;
	os_ << '"';
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
	sn_ = aut->get_named_prop<std::vector<std::string>>("state-names");
	if (opt_name_)
	  name_ = aut_->get_named_prop<std::string>("automaton-name");
	mark_states_ = !opt_force_acc_trans_ && aut_->is_sba();
	auto si =
	  std::unique_ptr<scc_info>(opt_scc_ ? new scc_info(aut) : nullptr);
	start();
	if (si)
	  {
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
	    for (auto& t: aut_->out(n))
	      process_link(t);
	  }
	end();
      }
    };
  } // anonymous namespace

  std::ostream&
  dotty_reachable(std::ostream& os, const const_tgba_ptr& g,
		  const char* options)
  {
    dotty_output d(os, options);
    auto aut = std::dynamic_pointer_cast<const tgba_digraph>(g);
    if (!aut)
      aut = make_tgba_digraph(g, tgba::prop_set::all());
    d.print(aut);
    return os;
  }


}
