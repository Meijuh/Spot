// -*- coding: utf-8 -*-
// Copyright (C) 2011, 2015-2017 Laboratoire de Recherche et Développement
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

#pragma once

#include <memory>
#include <type_traits>

// We usually write code like
//   subtypename* i = down_cast<subtypename*>(m);
//   ... use i ...
// When NDEBUG is set, the down_cast is a fast static_cast.
// Otherwise, the down_cast is a dynamic_cast and may return 0
// on error, which is caught by an assert in the down_cast function.
//
// NB: It is valid to use down_cast with non-pointer template argument:
//    subtypename& i = down_cast<subtypename&>(m);
// If an error occurs during the cast, an exception is thrown.
//
// NB: down_cast can also be used on shared_ptr.

namespace
{
  // A helper struct to check that downcasts are performed down an inheritance
  // hierarchy, not between unrelated types.
  template<typename Base, typename Derived>
  struct is_base_of : std::is_base_of<Base, Derived>
  {};
  template<typename Base, typename Derived>
  struct is_base_of<Base*, Derived*> : is_base_of<Base, Derived>
  {};
  // Also handle smart pointers.
  template<typename Base, typename Derived>
  struct is_base_of<std::shared_ptr<Base>, std::shared_ptr<Derived>>
    : is_base_of<Base, Derived>
  {};

  // std::is_pointer does not detect smart pointers.
  // Make our own version that detects pointer, plain or smart.
  template<typename T>
  struct is_pointer : std::is_pointer<T>
  {};
  template<typename T>
  struct is_pointer<std::shared_ptr<T>> : std::true_type
  {};

  template<typename T, typename U, bool check>
  struct _downcast;

  // A down-cast on non-pointer type is legitimate, e.g. down_cast<Derived&>(m);
  // An error in the dynamic_cast will throw an exception.
  template<typename T, typename U>
  struct _downcast<T, U, false>
  {
    static_assert(is_base_of<U, T>::value, "invalid downcast");

    static
    inline
    T
    cast(U u)
#ifdef NDEBUG
    noexcept
#else
    noexcept(is_pointer<T>::value)
#endif
    {
#ifdef NDEBUG
      return static_cast<T>(u);
#else
      return dynamic_cast<T>(u);
#endif
    }
  };

  // A specialization for smart pointer, so that down_cast can be used
  // uniformly.
  // NB: Use
  //    auto d = down_cast<std::shared_ptr<T>>(b);
  // instead of
  //    auto d = std::dynamic_pointer_cast<T>(b);
  template<typename T, typename U>
  struct _downcast<std::shared_ptr<T>, U, false>
  {
    static_assert(is_base_of<U, std::shared_ptr<T>>::value, "invalid downcast");

    static
    inline
    std::shared_ptr<T>
    cast(U u) noexcept
    {
#ifdef NDEBUG
      return std::static_pointer_cast<T>(u);
#else
      return std::dynamic_pointer_cast<T>(u);
#endif
    }
  };

  // Pointer type specialization.
  // Cast errors are caught by an assertion, no exception is thrown.
  template<typename T, typename U>
  struct _downcast<T, U, true>
  {
    static
    inline
    T
    cast(U u) noexcept
    {
      T t = _downcast<T, U, false>::cast(u);
      SPOT_ASSERT(t);
      return t;
    }
  };
} // anonymous namespace

// The actual function to call.
template<typename T, typename U>
inline
T
down_cast(U u)
#ifdef NDEBUG
    noexcept
#else
    noexcept(is_pointer<T>::value)
#endif
{
  return _downcast<T, U, is_pointer<T>::value>::cast(u);
}

