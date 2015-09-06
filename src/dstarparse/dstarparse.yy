/* -*- coding: utf-8 -*-
** Copyright (C) 2013, 2014, 2015 Laboratoire de Recherche et
** Développement de l'Epita (LRDE).
**
** This file is part of Spot, a model checking library.
**
** Spot is free software; you can redistribute it and/or modify it
** under the terms of the GNU General Public License as published by
** the Free Software Foundation; either version 3 of the License, or
** (at your option) any later version.
**
** Spot is distributed in the hope that it will be useful, but WITHOUT
** ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
** or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
** License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/
%language "C++"
%locations
%defines
%expect 0 // No shift/reduce
%name-prefix "dstaryy"
%debug
%error-verbose
%lex-param { spot::parse_aut_error_list& error_list }
%define api.location.type "spot::location"

%code requires
{
#include <string>
#include <cstring>
#include "ltlast/constant.hh"
#include "public.hh"

  inline namespace dstaryy_support
  {
    typedef std::map<int, bdd> map_t;

    struct result_
    {
      spot::parsed_aut_ptr h;
      spot::ltl::environment* env;
      std::vector<bdd> guards;
      std::vector<bdd>::const_iterator cur_guard;
      map_t dest_map;
      unsigned int cur_state;
      int plus;
      int minus;

      int states = -1;
      unsigned start_state = 0U;
      unsigned accpair_count = 0U;
      std::vector<int> ap;
      std::set<int> ap_set;

      bool accpair_count_seen:1;
      bool start_state_seen:1;
      bool ignore_more_ap:1;

      result_():
	accpair_count_seen(false),
	start_state_seen(false),
	ignore_more_ap(false)
      {
      }
    };
  }
}

%parse-param {spot::parse_aut_error_list& error_list}
%parse-param {result_& res}
%union
{
  std::string* str;
  unsigned int num;
  spot::acc_cond::mark_t mark;
}

%code
{
#include <sstream>
/* dstarparse.hh and parsedecl.hh include each other recursively.
   We must ensure that YYSTYPE is declared (by the above %union)
   before parsedecl.hh uses it. */
#include "parsedecl.hh"

  static void fill_guards(result_& res);
}

%token DRA "DRA"
%token DSA "DSA"
%token V2 "v2"
%token EXPLICIT "explicit"
%token ACCPAIRS "Acceptance-Pairs:"
%token AP "AP:";
%token START "Start:";
%token STATES "States:";
%token STATE "State:";
%token ACCSIG "Acc-Sig:";
%token ENDOFHEADER "---";
%token EOL "new line";
%token <str> STRING "string";
%token <num> NUMBER "number";

%type <num> sign
%type <mark> dstar_accsigs dstar_state_accsig

%destructor { delete $$; } <str>
%printer {
    if ($$)
      debug_stream() << *$$;
    else
      debug_stream() << "\"\""; } <str>
%printer { debug_stream() << $$; } <num>

%%
dstar: dstar_header ENDOFHEADER eols dstar_states
       { res.h->loc = @$; }

eols : EOL | eols EOL
opt_eols: | opt_eols EOL

dstar_type: DRA
       {
         res.h->type = spot::parsed_aut_type::DRA;
         res.plus = 1;
         res.minus = 0;
       }
       | DSA
       {
	 res.h->type = spot::parsed_aut_type::DSA;
         res.plus = 0;
         res.minus = 1;
       }

dstar_header: dstar_type opt_eols V2 opt_eols EXPLICIT opt_eols dstar_sizes
  {
    bool err = false;
    if (res.states < 0)
      {
	error(@5, "missing state count");
	err = true;
      }
    if (!res.accpair_count_seen)
      {
	error(@5, "missing acceptance-pair count");
	err = true;
      }
    if (!res.start_state_seen)
      {
	error(@5, "missing start-state number");
	err = true;
      }
    if (!res.ignore_more_ap)
      {
	error(@5, "missing atomic proposition definition");
	err = true;
      }
    if (err)
      {
	res.h->aut = nullptr;
	YYABORT;
      }
    res.h->aut->new_states(res.states);;
    res.h->aut->set_init_state(res.start_state);
    fill_guards(res);
    res.cur_guard = res.guards.end();
  }

aps:
  | aps STRING opt_eols
  {
    if (!res.ignore_more_ap)
      {
	auto f = res.env->require(*$2);
	auto d = res.h->aut->get_dict();
	int b = 0;
	if (f == nullptr)
	  {
	    std::ostringstream out;
	    out << "unknown atomic proposition \"" << *$2 << "\"";
	    error(@1, out.str());
	    f = spot::ltl::default_environment::instance()
	      .require("$unknown$");
	    b = d->register_proposition(f, res.h->aut);
	  }
	else
	  {
	    b = d->register_proposition(f, res.h->aut);
	    if (!res.ap_set.emplace(b).second)
	      {
		std::ostringstream out;
		out << "duplicate atomic proposition \"" << *$2 << "\"";
		error(@1, out.str());
	      }
	  }
	f->destroy();
	res.ap.push_back(b);
      }
    delete $2;
  }

dstar_sizes:
  | dstar_sizes error eols
  {
    error(@2, "unknown header ignored");
  }
  | dstar_sizes ACCPAIRS opt_eols NUMBER opt_eols
  {
    res.accpair_count = $4;
    res.accpair_count_seen = true;
    res.h->aut->set_acceptance(2 * $4,
				  res.h->type == spot::parsed_aut_type::DRA
				  ? spot::acc_cond::acc_code::rabin($4)
				  : spot::acc_cond::acc_code::streett($4));
  }
  | dstar_sizes STATES opt_eols NUMBER opt_eols
  {
    res.states = $4;
  }
  | dstar_sizes START opt_eols NUMBER opt_eols
  {
    res.start_state = $4;
    res.start_state_seen = true;
  }
  | dstar_sizes AP opt_eols NUMBER { res.ap.reserve($4); } opt_eols aps
  {
    if (!res.ignore_more_ap)
      {
	int announced = $4;
	int given = res.ap.size();
	if (given != announced)
	  {
	    std::ostringstream str;
	    str << announced << " atomic propositions announced but "
		<< given << " given";
	    error(@$, str.str());
	  }
	if (given > 31)
	  {
	    error(@$,
		  "ltl2star does not support more than 31 "
		  "atomic propositions");
	  }
	res.ignore_more_ap = true;
      }
    else
      {
	error(@$, "additional declaration of APs");
      }
  }

opt_name: | STRING opt_eols
  {
    delete $1;
  }

dstar_state_id: STATE opt_eols NUMBER opt_eols opt_name
  {
    if (res.cur_guard != res.guards.end())
      error(@1, "not enough transitions for previous state");
    if (res.states < 0 || $3 >= (unsigned) res.states)
      {
	std::ostringstream o;
	if (res.states > 0)
	  {
	    o << "state numbers should be in the range [0.."
	      << res.states - 1 << "]";
	  }
	else
	  {
	    o << "no states have been declared";
	  }
	error(@3, o.str());
      }
    res.cur_guard = res.guards.begin();
    res.dest_map.clear();
    res.cur_state = $3;
  }

sign: '+' { $$ = res.plus; }
  |   '-' { $$ = res.minus; }

// Membership to a pair is represented as (+NUM,-NUM)
dstar_accsigs: opt_eols
  {
    $$ = 0U;
  }
  | dstar_accsigs sign NUMBER opt_eols
  {
    if (res.states < 0 || res.cur_state >= (unsigned) res.states)
      break;
    if ($3 < res.accpair_count)
      {
	$$ = $1;
	$$.set($3 * 2 + $2);
      }
    else
      {
	std::ostringstream o;
	if (res.accpair_count > 0)
	  {
	    o << "acceptance pairs should be in the range [0.."
	      << res.accpair_count - 1 << "]";
	  }
	else
	  {
	    o << "no acceptance pairs have been declared";
	  }
	error(@3, o.str());
      }
  }

dstar_state_accsig: ACCSIG dstar_accsigs { $$ = $2; }

dstar_transitions:
  | dstar_transitions NUMBER opt_eols
  {
    std::pair<map_t::iterator, bool> i =
      res.dest_map.emplace($2, *res.cur_guard);
    if (!i.second)
      i.first->second |= *res.cur_guard;
    ++res.cur_guard;
  }

dstar_states:
  | dstar_states dstar_state_id dstar_state_accsig dstar_transitions
  {
    for (auto i: res.dest_map)
      res.h->aut->new_edge(res.cur_state, i.first, i.second, $3);
  }
%%

static void fill_guards(result_& r)
{
  spot::bdd_dict_ptr d = r.h->aut->get_dict();
  size_t nap = r.ap.size();

  int* vars = new int[nap];
  for (unsigned i = 0; i < nap; ++i)
    vars[i] = r.ap[nap - 1 - i];

  // build the 2^nap possible guards
  r.guards.reserve(1U << nap);
  for (size_t i = 0; i < (1U << nap); ++i)
    r.guards.push_back(bdd_ibuildcube(i, nap, vars));
  r.cur_guard = r.guards.begin();

  delete[] vars;
}

void
dstaryy::parser::error(const location_type& location,
		       const std::string& message)
{
  error_list.emplace_back(location, message);
}

namespace spot
{
  parsed_aut_ptr
  dstar_parse(const std::string& name,
	      parse_aut_error_list& error_list,
	      const bdd_dict_ptr& dict,
	      ltl::environment& env,
	      bool debug)
  {
    if (dstaryyopen(name))
      {
	error_list.emplace_back(spot::location(),
				std::string("Cannot open file ") + name);
	return nullptr;
      }
    result_ r;
    r.h = std::make_shared<spot::parsed_aut>();
    r.h->aut = make_twa_graph(dict);
    r.h->aut->prop_deterministic(true);
    r.h->aut->prop_state_based_acc(true);
    r.env = &env;
    dstaryy::parser parser(error_list, r);
    parser.set_debug_level(debug);
    parser.parse();
    dstaryyclose();
    return r.h;
  }
}

// Local Variables:
// mode: c++
// End:
