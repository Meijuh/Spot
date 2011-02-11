// Copyright (C) 2010 Laboratoire de Recherche et Developpement
// de l Epita (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Spot; see the file COPYING.  If not, write to the Free
// Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
// 02111-1307, USA.

#include <ostream>
#include "dotty.hh"
#include "tgba/bddprint.hh"
#include "reachiter.hh"
#include "misc/escape.hh"
#include "misc/bareword.hh"

namespace spot
{
  namespace
  {
    class dotty_bfs : public ta_reachable_iterator_breadth_first
    {
    public:
      dotty_bfs(std::ostream& os, const ta* a) :
        ta_reachable_iterator_breadth_first(a), os_(os)
      {
      }

      void
      start()
      {
        os_ << "digraph G {" << std::endl;

        int n = 0;
        const ta::states_set_t init_states_set =
            t_automata_->get_initial_states_set();
        ta::states_set_t::const_iterator it;

        for (it = (init_states_set.begin()); it != init_states_set.end(); it++)
          {
            //    cout << (*it).first << " => " << (*it).second << endl;

            bdd init_condition = t_automata_->get_state_condition(*it);
            std::string label = bdd_format_formula(t_automata_->get_dict(),
                init_condition);
            ++n;
            os_ << -n << "  [label=\"\", style=invis, height=0]" << std::endl;
            os_ << "  " << -n << " -> " << n << " " << "[label=\"" + label
                + "\"]" << std::endl;

          }
      }

      void
      end()
      {
        os_ << "}" << std::endl;
      }

      void
      process_state(const state* s, int n)
      {

        std::string shape = "ellipse";
        std::string style = "solid";
        if (t_automata_->is_accepting_state(s))
          {
            shape = "doublecircle";
            style = "bold";
          }

        if (t_automata_->is_livelock_accepting_state(s))
          {
            shape = "octagon";
            style = "bold";
          }
        if (t_automata_->is_livelock_accepting_state(s)
            && t_automata_->is_accepting_state(s))
          {
            shape = "doubleoctagon";
            style = "bold";
          }

        os_ << "  " << n << " [label=" << quote_unless_bare_word(
            t_automata_->format_state(s)) << "]" << "[shape=\"" + shape + "\"]"
            << "[style=\"" + style + "\"]" << std::endl;

      }

      void
      process_link(int in, int out, const ta_succ_iterator* si)
      {

        os_ << "  " << in << " -> " << out << " [label=\"";
        escape_str(os_, bdd_format_accset(t_automata_->get_dict(),
            si->current_condition()))

        << "\"]" << std::endl;

      }

    private:
      std::ostream& os_;
    };

  }

  std::ostream&
  dotty_reachable(std::ostream& os, const ta* a)
  {
    dotty_bfs d(os, a);
    d.run();
    return os;
  }

}
