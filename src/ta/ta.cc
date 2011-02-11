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



#include "ta.hh"

namespace spot
{



  scc_stack_ta::connected_component::connected_component(int i)
   {
     index = i;
     is_accepting = false;
   }

   scc_stack_ta::connected_component&
   scc_stack_ta::top()
   {
     return s.front();
   }

   const scc_stack_ta::connected_component&
   scc_stack_ta::top() const
   {
     return s.front();
   }

   void
   scc_stack_ta::pop()
   {
     // assert(rem().empty());
     s.pop_front();
   }

   void
   scc_stack_ta::push(int index)
   {
     s.push_front(connected_component(index));
   }

   std::list<state*>&
   scc_stack_ta::rem()
   {
     return top().rem;
   }

   size_t
   scc_stack_ta::size() const
   {
     return s.size();
   }

   bool
   scc_stack_ta::empty() const
   {
     return s.empty();
   }


}


