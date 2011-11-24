// Copyright (C) 2011 Laboratoire de Recherche et Developpement
// de l'Epita (LRDE)
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


#ifndef SPOT_KRIPKE_KRIPKEPRINT_HH
# define SPOT_KRIPKE_KRIPKEPRINT_HH

# include <iosfwd>
# include "tgbaalgos/reachiter.hh"
namespace spot
{

  class kripke_explicit;
  class state_kripke;
  class kripke_succ_iterator;
  class kripke;

  /// \brief Iterate over all reachable states of a spot::kripke
  /// Override start and process_state methods from
  /// tgba_reachable_iterator_breadth_first.
  class KripkePrinter : public tgba_reachable_iterator_breadth_first
  {
    public:
      KripkePrinter(const kripke* state, std::ostream& os);

      void start();

      void process_state(const state*, int, tgba_succ_iterator* si);

    private:
      std::ostream& os_;
  };

} // End namespace spot

#endif /* !KRIPKEPRINT_HH_ */
