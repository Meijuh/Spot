// -*- coding: utf-8 -*-
// Copyright (C) 2006, 2014 Petr Ročkai <me@mornfall.net>
// Copyright (C) 2013-2015 Vladimír Štill <xstill@fi.muni.cz>
// Copyright (C) 2017 Henrich Lauko <xlauko@mail.muni.cz>
//
// This file is a modification of brick-types file from brick library.
//
// Permission to use, copy, modify, and distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
// ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
// ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
// OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

#pragma once

#include <type_traits>

namespace spot
{
  template<typename E>
  using is_enum_class = std::integral_constant<bool,
    std::is_enum<E>::value && !std::is_convertible<E, int>::value>;

  template<typename self>
  struct strong_enum_flags {
    static_assert(is_enum_class<self>::value, "Not an enum class.");
    using type = strong_enum_flags<self>;
    using underlying_type = typename std::underlying_type<self>::type;

    constexpr strong_enum_flags() noexcept : store(0) {}
    constexpr strong_enum_flags(self flag) noexcept :
      store(static_cast<underlying_type>(flag))
    {}

    explicit constexpr strong_enum_flags(underlying_type st) noexcept
      : store(st) {}

    constexpr explicit operator underlying_type() const noexcept
    {
      return store;
    }

    type &operator|=(type o) noexcept
    {
      store |= o.store;
      return *this;
    }

    type &operator&=(type o) noexcept
    {
      store &= o.store;
      return *this;
    }

    type &operator^=(type o) noexcept
    {
      store ^= o.store;
      return *this;
    }

    friend constexpr type operator~(type a)
    {
      return type(~a.store);
    }

    friend constexpr type operator|(type a, type b) noexcept
    {
      return type(a.store | b.store);
    }

    friend constexpr type operator&(type a, type b) noexcept
    {
      return type(a.store & b.store);
    }

    friend constexpr type operator^(type a, type b) noexcept
    {
      return type(a.store ^ b.store);
    }

    friend constexpr bool operator==(type a, type b) noexcept
    {
      return a.store == b.store;
    }

    friend constexpr bool operator!=(type a, type b) noexcept
    {
      return a.store != b.store;
    }


    constexpr bool has(self x) const noexcept
    {
      return ((*this) &x);
    }

    type clear(self x) noexcept
    {
      store &= ~underlying_type(x);
      return *this;
    }

    explicit constexpr operator bool() const noexcept
    {
      return store;
    }

  private:
    underlying_type store;
  };
}
