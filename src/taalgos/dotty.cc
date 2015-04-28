// -*- coding: utf-8 -*-
// Copyright (C) 2010, 2012, 2014, 2015 Laboratoire de Recherche et
// Developpement de l Epita (LRDE).
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
#include "dotty.hh"
#include "twa/bddprint.hh"
#include "reachiter.hh"
#include "misc/escape.hh"
#include "misc/bareword.hh"
#include <cstdlib>
#include <cstring>

namespace spot
{
  namespace
  {
    class dotty_bfs : public ta_reachable_iterator_breadth_first
    {
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
	    case 'A':
	      opt_hide_sets_ = true;
	      break;
	    case 'c':
	      opt_circles_ = true;
	      break;
	    case 'h':
	      opt_horizontal_ = true;
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
	    case 'v':
	      opt_horizontal_ = false;
	      break;
	    case '1':
	    case 'a':
	    case 'b':
	    case 'n':
	    case 'N':
	    case 'o':
	    case 'r':
	    case 'R':
	    case 's':
	    case 't':
	      // All these options are implemented by dotty() on TGBA,
	      // but are not implemented here.  We simply ignore them,
	      // because raising an exception if they are in
	      // SPOT_DEFAULT would be annoying.
	      break;
	    default:
	      throw std::runtime_error
		(std::string("unknown option for dotty(): ") + c);
	    }
      }

    public:
      dotty_bfs(std::ostream& os, const const_ta_ptr& a,
		const char* opt) :
        ta_reachable_iterator_breadth_first(a), os_(os)
      {
	parse_opts(opt ? opt : ".");
      }

      void
      start()
      {
        os_ << "digraph G {\n";

	if (opt_horizontal_)
	  os_ << "  rankdir=LR\n";
	if (opt_circles_)
	  os_ << "  node [shape=\"circle\"]\n";
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

        artificial_initial_state_ = t_automata_->get_artificial_initial_state();

        ta::states_set_t init_states_set;

        ta::states_set_t::const_iterator it;

        if (artificial_initial_state_)
	  {
	    init_states_set.insert(artificial_initial_state_);
	    os_ << "  0 [label=\"\", style=invis, height=0]\n  0 -> 1\n";
	  }
        else
	  {
	    int n = 0;
	    init_states_set = t_automata_->get_initial_states_set();
	    for (it = init_states_set.begin();
		 it != init_states_set.end(); ++it)
	      {
		bdd init_condition = t_automata_->get_state_condition(*it);
		std::string label = bdd_format_formula(t_automata_->get_dict(),
						       init_condition);
		++n;
		os_ << "  " << -n << "  [label=\"\", style=invis, height=0]\n  "
		    << -n << " -> " << n << " [label=\"" << label << "\"]\n";
	      }
	  }
      }

      void
      end()
      {
        os_ << '}' << std::endl;
      }

      void
      process_state(const state* s, int n)
      {

        std::string style;
        if (t_automata_->is_accepting_state(s))
	  style = ",peripheries=2";

	if (t_automata_->is_livelock_accepting_state(s))
	  style += ",shape=box";

	os_ << "  " << n << " [label=";
	if (s == artificial_initial_state_)
	  os_ << "init";
	else
	  os_ << quote_unless_bare_word(t_automata_->format_state(s));
	os_ << style << "]\n";
      }

      void
      process_link(int in, int out, const ta_succ_iterator* si)
      {
	bdd_dict_ptr d = t_automata_->get_dict();
	std::string label =
	  ((in == 1 && artificial_initial_state_)
	   ? bdd_format_formula(d, si->current_condition())
	   : bdd_format_accset(d, si->current_condition()));

	if (label.empty())
	  label = "{}";

	if (!opt_hide_sets_)
	  {
	    label += "\n";
	    label += t_automata_->acc().
	      format(si->current_acceptance_conditions());
	  }

        os_ << "  " << in << " -> " << out << " [label=\"";
	escape_str(os_, label);
	os_ << "\"]\n";
      }

    private:
      std::ostream& os_;
      spot::state* artificial_initial_state_;

      bool opt_horizontal_ = true;
      bool opt_circles_ = false;
      bool opt_hide_sets_ = false;
      std::string opt_font_;
    };

  }

  std::ostream&
  dotty_reachable(std::ostream& os, const const_ta_ptr& a, const char* opt)
  {
    dotty_bfs d(os, a, opt);
    d.run();
    return os;
  }

}
