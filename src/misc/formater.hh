// -*- coding: utf-8 -*-
// Copyright (C) 2012 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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

#ifndef SPOT_SRC_MISC_FORMATER_HH
#define SPOT_SRC_MISC_FORMATER_HH

#include <iostream>
#include <string>
#include <vector>

namespace spot
{
  class printable
  {
  public:
    ~printable()
    {
    }
    virtual void
    print(std::ostream&, const char*) const = 0;
  };


  template <class T>
  class printable_value: public printable
  {
  protected:
    T val_;
  public:
    operator T() const
    {
      return val_;
    }

    printable_value&
    operator=(const T& new_val)
    {
      val_ = new_val;
      return *this;
    }

    virtual void
    print(std::ostream& os, const char*) const
    {
      os << val_;
    }
  };

  /// The default callback simply writes "%c".
  class printable_id: public printable
  {
  public:
    virtual void
    print(std::ostream& os, const char* x) const
    {
      os << '%' << *x;
    }
  };

  /// Called by default for "%%" and "%\0".
  class printable_percent: public printable
  {
  public:
    virtual void
    print(std::ostream& os, const char*) const
    {
      os << '%';
    }
  };


  class formater
  {
    printable_id id;
    printable_percent percent;
  public:

    formater()
      : has_(256), call_(256, &id)
    {
      call_['%'] = call_[0] = &percent;
    }

    /// Collect the %-sequences occurring in \a fmt.
    void
    prime(const char* fmt)
    {
      for (const char* pos = fmt; *pos; ++pos)
	if (*pos == '%')
	  {
	    char c = *++pos;
	    has_[c] = true;
	    if (!c)
	      break;
	  }
    }

    /// Collect the %-sequences occurring in \a fmt.
    void
    prime(const std::string& fmt)
    {
      prime(fmt.c_str());
    }

    /// Whether %c occurred in the primed formats.
    bool
    has(char c) const
    {
      return has_[c];
    }

    /// Declare a callback function for %c.
    void
    declare(char c, const printable* f)
    {
      call_[c] = f;
    }

    /// Remember where to output any string.
    void
    set_output(std::ostream& output)
    {
      output_ = &output;
    }

    /// Expand the %-sequences in \a fmt, write the result on \a output_.
    std::ostream&
    format(const char* fmt)
    {
      for (const char* pos = fmt; *pos; ++pos)
	if (*pos != '%')
	  {
	    *output_ << *pos;
	  }
	else
	  {
	    char c = *++pos;
	    call_[c]->print(*output_, pos);
	    if (!c)
	      break;
	  }
      return *output_;
    }

    /// Expand the %-sequences in \a fmt, write the result on \a output.
    std::ostream&
    format(std::ostream& output, const char* fmt)
    {
      set_output(output);
      return format(fmt);
    }

    /// Expand the %-sequences in \a fmt, write the result on \a output_.
    std::ostream&
    format(const std::string& fmt)
    {
      return format(fmt.c_str());
    }

    /// Expand the %-sequences in \a fmt, write the result on \a output.
    std::ostream&
    format(std::ostream& output, const std::string& fmt)
    {
      return format(output, fmt.c_str());
    }

  private:
    std::vector<bool> has_;
    std::vector<const printable*> call_;
  protected:
    std::ostream* output_;
    const char* pos_;
  };

}

#endif // SPOT_SRC_MISC_FORMATER_HH
