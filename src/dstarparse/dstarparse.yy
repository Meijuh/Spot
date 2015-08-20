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

    enum dstar_type { Rabin, Streett };

    struct result_
    {
      spot::parsed_aut_ptr d;
      dstar_type type;
      spot::ltl::environment* env;
      std::vector<bdd> guards;
      std::vector<bdd>::const_iterator cur_guard;
      map_t dest_map;
      int cur_state;
      int plus;
      int minus;

      unsigned state_count = 0U;
      unsigned start_state = 0U;
      unsigned accpair_count = 0U;
      std::vector<std::string> aps;

      bool state_count_seen:1;
      bool accpair_count_seen:1;
      bool start_state_seen:1;
      bool aps_seen:1;

      result_():
	state_count_seen(false),
	accpair_count_seen(false),
	start_state_seen(false),
	aps_seen(false)
      {
      }
    };
  }
}

%parse-param {spot::parse_aut_error_list& error_list}
%parse-param {result_& result}
%union
{
  std::string* str;
  unsigned int num;
  spot::acc_cond::mark_t acc;
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
%type <acc> accsigs state_accsig

%destructor { delete $$; } <str>
%printer {
    if ($$)
      debug_stream() << *$$;
    else
      debug_stream() << "\"\""; } <str>
%printer { debug_stream() << $$; } <num>

%%
dstar: header ENDOFHEADER eols states
       { result.d->loc = @$; }

eols : EOL | eols EOL
opt_eols: | opt_eols EOL

auttype: DRA
       {
         result.type = Rabin;
         result.plus = 1;
         result.minus = 0;
       }
       | DSA
       {
	 result.type = Streett;
         result.plus = 0;
         result.minus = 1;
       }

header: auttype opt_eols V2 opt_eols EXPLICIT opt_eols sizes
  {
    bool err = false;
    if (!result.state_count_seen)
      {
	error(@5, "missing state count");
	err = true;
      }
    if (!result.accpair_count_seen)
      {
	error(@5, "missing acceptance-pair count");
	err = true;
      }
    if (!result.start_state_seen)
      {
	error(@5, "missing start-state number");
	err = true;
      }
    if (!result.aps_seen)
      {
	error(@5, "missing atomic proposition definition");
	err = true;
      }
    if (err)
      {
	result.d->aut = nullptr;
	YYABORT;
      }
    result.d->aut->new_states(result.state_count);;
    result.d->aut->set_init_state(result.start_state);
    fill_guards(result);
  }

aps:
  | aps STRING opt_eols
  {
    result.aps.push_back(*$2);
    delete $2;
  }

sizes:
  | sizes error eols
  {
    error(@2, "unknown header ignored");
  }
  | sizes ACCPAIRS opt_eols NUMBER opt_eols
  {
    result.accpair_count = $4;
    result.accpair_count_seen = true;
    result.d->aut->set_acceptance(2 * $4,
				  result.type == Rabin ?
				  spot::acc_cond::acc_code::rabin($4) :
				  spot::acc_cond::acc_code::streett($4));
  }
  | sizes STATES opt_eols NUMBER opt_eols
  {
    result.state_count = $4;
    result.state_count_seen = true;
  }
  | sizes START opt_eols NUMBER opt_eols
  {
    result.start_state = $4;
    result.start_state_seen = true;
  }
  | sizes AP opt_eols NUMBER opt_eols aps
  {
    int announced = $4;
    int given = result.aps.size();
    if (given != announced)
      {
	std::ostringstream str;
	str << announced << " atomic propositions announced but "
	    << given << " given";
	error(@4 + @6, str.str());
      }
    if (given > 31)
      {
	error(@4 + @6,
	      "ltl2star does not support more than 31 atomic propositions");
      }
    result.aps_seen = true;
  }

opt_name: | STRING opt_eols
  {
    delete $1;
  }

state_id: STATE opt_eols NUMBER opt_eols opt_name
  {
    if (result.cur_guard != result.guards.end())
      error(@1, "not enough transitions for previous state");
    if ($3 >= result.state_count)
      {
	std::ostringstream o;
	if (result.state_count > 0)
	  {
	    o << "state numbers should be in the range [0.."
	      << result.state_count - 1<< "]";
	  }
	else
	  {
	    o << "no states have been declared";
	  }
	error(@3, o.str());
      }
    result.cur_guard = result.guards.begin();
    result.dest_map.clear();
    result.cur_state = $3;
  }

sign: '+' { $$ = result.plus; }
  |   '-' { $$ = result.minus; }

// Membership to a pair is represented as (+NUM,-NUM)
accsigs: opt_eols
  {
    $$ = 0U;
  }
  | accsigs sign NUMBER opt_eols
  {
    if ((unsigned) result.cur_state >= result.state_count)
      break;
    if ($3 < result.accpair_count)
      {
	$$ = $1;
	$$.set($3 * 2 + $2);
      }
    else
      {
	std::ostringstream o;
	if (result.accpair_count > 0)
	  {
	    o << "acceptance pairs should be in the range [0.."
	      << result.accpair_count - 1 << "]";
	  }
	else
	  {
	    o << "no acceptance pairs have been declared";
	  }
	error(@3, o.str());
      }
  }

state_accsig: ACCSIG accsigs { $$ = $2; }

transitions:
  | transitions NUMBER opt_eols
  {
    std::pair<map_t::iterator, bool> i =
      result.dest_map.emplace($2, *result.cur_guard);
    if (!i.second)
      i.first->second |= *result.cur_guard;
    ++result.cur_guard;
  }

states:
  | states state_id state_accsig transitions
  {
    for (auto i: result.dest_map)
      result.d->aut->new_edge(result.cur_state, i.first, i.second, $3);
  }
%%

static void fill_guards(result_& r)
{
  spot::bdd_dict_ptr d = r.d->aut->get_dict();

  size_t nap = r.aps.size();
  int* vars = new int[nap];

  // Get a BDD variable for each atomic proposition
  for (size_t i = 0; i < nap; ++i)
    {
      const spot::ltl::formula* f = r.env->require(r.aps[i]);
      vars[nap - 1 - i] = d->register_proposition(f, r.d->aut);
      f->destroy();
    }

  // build the 2^nap possible guards
  r.guards.reserve(1U << nap);
  for (size_t i = 0; i < (1U << nap); ++i)
    r.guards.push_back(bdd_ibuildcube(i, nap, vars));

  delete[] vars;
  r.cur_guard = r.guards.end();
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
    r.d = std::make_shared<spot::parsed_aut>();
    r.d->aut = make_twa_graph(dict);
    r.d->aut->prop_deterministic(true);
    r.d->aut->prop_state_based_acc(true);
    r.env = &env;
    dstaryy::parser parser(error_list, r);
    parser.set_debug_level(debug);
    parser.parse();
    dstaryyclose();
    return r.d;
  }
}

// Local Variables:
// mode: c++
// End:
