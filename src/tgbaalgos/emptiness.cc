// -*- coding: utf-8 -*-
// Copyright (C) 2009, 2011, 2012, 2013, 2014 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
// Copyright (C) 2004, 2005 Laboratoire d'Informatique de Paris 6 (LIP6),
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

#include <sstream>
#include "emptiness.hh"
#include "tgba/tgba.hh"
#include "tgba/bddprint.hh"
#include "tgbaalgos/gtec/gtec.hh"
#include "tgbaalgos/gv04.hh"
#include "tgbaalgos/magic.hh"
#include "tgbaalgos/se05.hh"
#include "tgbaalgos/tau03.hh"
#include "tgbaalgos/tau03opt.hh"

namespace spot
{

  // tgba_run
  //////////////////////////////////////////////////////////////////////

  tgba_run::~tgba_run()
  {
    for (steps::const_iterator i = prefix.begin(); i != prefix.end(); ++i)
      i->s->destroy();
    for (steps::const_iterator i = cycle.begin(); i != cycle.end(); ++i)
      i->s->destroy();
  }

  tgba_run::tgba_run(const tgba_run& run)
  {
    for (steps::const_iterator i = run.prefix.begin();
	 i != run.prefix.end(); ++i)
      {
	step s = { i->s->clone(), i->label, i->acc };
	prefix.push_back(s);
      }
    for (steps::const_iterator i = run.cycle.begin();
	 i != run.cycle.end(); ++i)
      {
	step s = { i->s->clone(), i->label, i->acc };
	cycle.push_back(s);
      }
  }

  tgba_run&
  tgba_run::operator=(const tgba_run& run)
  {
    if (&run != this)
      {
	this->~tgba_run();
	new(this) tgba_run(run);
      }
    return *this;
  }

  // print_tgba_run
  //////////////////////////////////////////////////////////////////////

  std::ostream&
  print_tgba_run(std::ostream& os,
		 const tgba* a,
		 const tgba_run* run)
  {
    bdd_dict* d = a->get_dict();
    os << "Prefix:" << std::endl;
    for (tgba_run::steps::const_iterator i = run->prefix.begin();
	 i != run->prefix.end(); ++i)
      {
	os << "  " << a->format_state(i->s) << std::endl;
	os << "  |  ";
	bdd_print_formula(os, d, i->label);
	os << '\t';
	bdd_print_accset(os, d, i->acc);
	os << std::endl;
      }
    os << "Cycle:" << std::endl;
    for (tgba_run::steps::const_iterator i = run->cycle.begin();
	 i != run->cycle.end(); ++i)
      {
	os << "  " << a->format_state(i->s) << std::endl;
	os << "  |  ";
	bdd_print_formula(os, d, i->label);
	os << '\t';
	bdd_print_accset(os, d, i->acc);
	os << '\n';
      }
    return os;
  }

  // emptiness_check_result
  //////////////////////////////////////////////////////////////////////

  tgba_run*
  emptiness_check_result::accepting_run()
  {
    return 0;
  }

  const unsigned_statistics*
  emptiness_check_result::statistics() const
  {
    return dynamic_cast<const unsigned_statistics*>(this);
  }

  const char*
  emptiness_check_result::parse_options(char* options)
  {
    option_map old(o_);
    const char* s = o_.parse_options(options);
    options_updated(old);
    return s;
  }

  void
  emptiness_check_result::options_updated(const option_map&)
  {
  }


  // emptiness_check
  //////////////////////////////////////////////////////////////////////

  emptiness_check::~emptiness_check()
  {
  }

  const unsigned_statistics*
  emptiness_check::statistics() const
  {
    return dynamic_cast<const unsigned_statistics*>(this);
  }

  const char*
  emptiness_check::parse_options(char* options)
  {
    option_map old(o_);
    const char* s = o_.parse_options(options);
    options_updated(old);
    return s;
  }

  void
  emptiness_check::options_updated(const option_map&)
  {
  }

  bool
  emptiness_check::safe() const
  {
    return true;
  }

  std::ostream&
  emptiness_check::print_stats(std::ostream& os) const
  {
    return os;
  }

  // emptiness_check_instantiator
  //////////////////////////////////////////////////////////////////////

  namespace
  {

    spot::emptiness_check*
    couvreur99_cons(const spot::tgba* a, spot::option_map o)
    {
      return spot::couvreur99(a, o);
    }

    struct ec_algo
    {
      const char* name;
      spot::emptiness_check* (*construct)(const spot::tgba*,
					  spot::option_map);
      unsigned int min_acc;
      unsigned int max_acc;
    };

    ec_algo ec_algos[] =
      {
	{ "Cou99",     couvreur99_cons,                     0, -1U },
	{ "CVWY90",    spot::magic_search,                  0,   1 },
	{ "GV04",      spot::explicit_gv04_check,           0,   1 },
	{ "SE05",      spot::se05,                          0,   1 },
	{ "Tau03",     spot::explicit_tau03_search,         1, -1U },
	{ "Tau03_opt", spot::explicit_tau03_opt_search,     0, -1U },
      };
  }

  emptiness_check_instantiator::emptiness_check_instantiator(option_map o,
							     void* i)
    : o_(o), info_(i)
  {
  }

  unsigned int
  emptiness_check_instantiator::min_acceptance_conditions() const
  {
    return static_cast<ec_algo*>(info_)->min_acc;
  }

  unsigned int
  emptiness_check_instantiator::max_acceptance_conditions() const
  {
    return static_cast<ec_algo*>(info_)->max_acc;
  }

  emptiness_check*
  emptiness_check_instantiator::instantiate(const tgba* a) const
  {
    return static_cast<ec_algo*>(info_)->construct(a, o_);
  }

  emptiness_check_instantiator*
  emptiness_check_instantiator::construct(const char* name, const char** err)
  {
    // Skip spaces.
    while (*name && strchr(" \t\n", *name))
      ++name;

    const char* opt_str = strchr(name, '(');
    option_map o;
    if (opt_str)
      {
	const char* opt_start = opt_str + 1;
	const char* opt_end = strchr(opt_start, ')');
	if (!opt_end)
	  {
	    *err = opt_start;
	    return 0;
	  }
	std::string opt(opt_start, opt_end);

	const char* res = o.parse_options(opt.c_str());
	if (res)
	  {
	    *err  = opt.c_str() - res + opt_start;
	    return 0;
	  }
      }

    if (!opt_str)
      opt_str = name + strlen(name);

    // Ignore spaces before `(' (or trailing spaces).
    while (opt_str > name && strchr(" \t\n", *--opt_str))
      continue;
    std::string n(name, opt_str + 1);


    ec_algo* info = ec_algos;
    for (unsigned i = 0; i < sizeof(ec_algos)/sizeof(*ec_algos); ++i, ++info)
      if (n == info->name)
	{
	  *err = 0;
	  return new emptiness_check_instantiator(o, info);
	}
    *err = name;
    return 0;
  }

  // tgba_run_to_tgba
  //////////////////////////////////////////////////////////////////////

  tgba_digraph*
  tgba_run_to_tgba(const tgba* a, const tgba_run* run)
  {
    auto d = a->get_dict();
    auto res = new tgba_digraph(d);
    auto& g = res->get_graph();
    d->register_all_variables_of(a, res);

    const state* s = a->get_init_state();
    unsigned src;
    unsigned dst;
    const tgba_run::steps* l;
    bdd seen_acc = bddfalse;

    typedef std::unordered_map<const state*, unsigned,
			       state_ptr_hash, state_ptr_equal> state_map;
    state_map seen;

    if (run->prefix.empty())
        l = &run->cycle;
    else
        l = &run->prefix;

    tgba_run::steps::const_iterator i = l->begin();

    assert(s->compare(i->s) == 0);
    src = g.new_state();
    seen.insert(std::make_pair(i->s, src));

    for (; i != l->end();)
      {
        // expected outgoing transition
        bdd label = i->label;
        bdd acc = i->acc;

        // compute the next expected state
        const state* next;
        ++i;
        if (i != l->end())
          {
            next = i->s;
          }
        else
          {
            if (l == &run->prefix)
              {
                l = &run->cycle;
                i = l->begin();
              }
            next = l->begin()->s;
          }

        // browse the actual outgoing transitions and
	// look for next;
	const state* the_next = nullptr;
	for (auto j: a->succ(s))
          {
            if (j->current_condition() != label
                || j->current_acceptance_conditions() != acc)
              continue;

            const state* s2 = j->current_state();
            if (s2->compare(next) == 0)
              {
		the_next = s2;
		break;
	      }
	    s2->destroy();
          }
        assert(res);
        s->destroy();
	s = the_next;


	auto p = seen.insert(std::make_pair(next, 0));
	if (p.second)
	  p.first->second = g.new_state();
	dst = p.first->second;

	g.new_transition(src, dst, label, acc);
	src = dst;

        // Sum acceptance conditions.
        if (l == &run->cycle && i != l->begin())
	  seen_acc |= acc;
      }

    s->destroy();

    assert(seen_acc == a->all_acceptance_conditions());
    return res;
  }

}
