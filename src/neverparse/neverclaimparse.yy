/* -*- coding: utf-8 -*-
** Copyright (C) 2010, 2011, 2012, 2013, 2014 Laboratoire de Recherche
** et Développement de l'Epita (LRDE).
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
%name-prefix "neverclaimyy"
%debug
%error-verbose
%lex-param { spot::neverclaim_parse_error_list& error_list }
%define api.location.type "spot::location"

%code requires
{
#include <string>
#include <cstring>
#include "public.hh"
#include "tgba/formula2bdd.hh"

/* Cache parsed formulae.  Labels on arcs are frequently identical and
   it would be a waste of time to parse them to formula* over and
   over, and to register all their atomic_propositions in the
   bdd_dict.  Keep the bdd result around so we can reuse it.  */
  typedef std::map<std::string, bdd> formula_cache;

  typedef std::pair<const bdd*, std::string*> pair;
  typedef typename spot::tgba_digraph::namer<std::string>::type named_tgba_t;
}

%parse-param {spot::neverclaim_parse_error_list& error_list}
%parse-param {spot::ltl::environment& parse_environment}
%parse-param {spot::tgba_digraph_ptr& result}
%parse-param {named_tgba_t*& namer}
%parse-param {formula_cache& fcache}
%union
{
  std::string* str;
  pair* p;
  std::list<pair>* list;
  const bdd* b;
}

%code
{
#include "ltlast/constant.hh"
#include "ltlparse/public.hh"

/* neverclaimparse.hh and parsedecl.hh include each other recursively.
   We must ensure that YYSTYPE is declared (by the above %union)
   before parsedecl.hh uses it. */
#include "parsedecl.hh"
using namespace spot::ltl;
static bool accept_all_needed = false;
static bool accept_all_seen = false;
static std::map<std::string, spot::location> labels;
}

%token NEVER "never"
%token SKIP "skip"
%token IF "if"
%token FI "fi"
%token DO "do"
%token OD "od"
%token ARROW "->"
%token GOTO "goto"
%token FALSE "false"
%token ATOMIC "atomic"
%token ASSERT "assert"
%token <str> FORMULA "boolean formula"
%token <str> IDENT "identifier"
%type <b> formula
%type <str> opt_dest formula_or_ident
%type <p> transition src_dest
%type <list> transitions transition_block
%type <str> one_ident ident_list


%destructor { delete $$; } <str>
%destructor { delete $$->second; delete $$; } <p>
%destructor {
  for (std::list<pair>::iterator i = $$->begin();
       i != $$->end(); ++i)
  {
    delete i->second;
  }
  delete $$;
  } <list>
%printer {
    if ($$)
      debug_stream() << *$$;
    else
      debug_stream() << "\"\""; } <str>

%%
neverclaim:
  "never" '{' states '}'


states:
  /* empty */
  | state
  | states ';' state
  | states ';'

one_ident: IDENT ':'
    {
      namer->new_state(*$1);
      std::pair<std::map<std::string, spot::location>::const_iterator, bool>
	res = labels.insert(std::make_pair(*$1, @1));
      if (!res.second)
	{
	  error(@1, std::string("redefinition of ") + *$1 + "...");
	  error(res.first->second, std::string("... ")  + *$1 + " previously defined here");
	}
      $$ = $1;
    }


ident_list: one_ident
  | ident_list one_ident
    {
      namer->alias_state(namer->get_state(*$1), *$2);
      // Keep any identifier that starts with accept.
      if (strncmp("accept", $1->c_str(), 6))
        {
          delete $1;
          $$ = $2;
        }
      else
        {
	  delete $2;
	  $$ = $1;
        }
    }


transition_block:
  "if" transitions "fi"
    {
      $$ = $2;
    }
  | "do" transitions "od"
    {
      $$ = $2;
    }

state:
  ident_list "skip"
    {
      if (*$1 == "accept_all")
	accept_all_seen = true;

      namer->new_transition(*$1, *$1, bddtrue,
			    !strncmp("accept", $1->c_str(), 6) ?
			    result->all_acceptance_conditions() :
			    static_cast<const bdd>(bddfalse));
      delete $1;
    }
  | ident_list { delete $1; }
  | ident_list "false" { delete $1; }
  | ident_list transition_block
    {
      bdd acc = !strncmp("accept", $1->c_str(), 6) ?
	result->all_acceptance_conditions() :
	static_cast<const bdd>(bddfalse);
      for (auto& p: *$2)
	namer->new_transition(*$1, *p.second, *p.first, acc);
      // Free the list
      delete $1;
      for (auto& p: *$2)
	delete p.second;
      delete $2;
    }


transitions:
  /* empty */ { $$ = new std::list<pair>; }
  | transitions transition
    {
      if ($2)
	{
	  $1->push_back(*$2);
	  delete $2;
	}
      $$ = $1;
    }


formula_or_ident: FORMULA | IDENT

formula: formula_or_ident
     {
       formula_cache::const_iterator i = fcache.find(*$1);
       if (i == fcache.end())
	 {
	   parse_error_list pel;
	   const formula* f =
	     spot::ltl::parse_boolean(*$1, pel, parse_environment,
				      debug_level(), true);
	   for (auto& j: pel)
	     {
	       // Adjust the diagnostic to the current position.
	       spot::location here = @1;
	       here.end.line = here.begin.line + j.first.end.line - 1;
	       here.end.column = here.begin.column + j.first.end.column;
	       here.begin.line += j.first.begin.line - 1;
	       here.begin.column += j.first.begin.column;
	       error_list.emplace_back(here, j.second);
	     }
           bdd cond = bddfalse;
	   if (f)
	     {
	       cond = formula_to_bdd(f, result->get_dict(), result);
	       f->destroy();
	     }
	   $$ = &(fcache[*$1] = cond);
	 }
       else
	 {
	   $$ = &i->second;
	 }
       delete $1;
     }
   | "false"
     {
       $$ = &bddfalse;
     }

opt_dest:
  /* empty */
    {
      $$ = 0;
    }
  | "->" "goto" IDENT
    {
      $$ = $3;
    }
  | "->" "assert" FORMULA
    {
      delete $3;
      $$ = new std::string("accept_all");
      accept_all_needed = true;
    }

src_dest: formula opt_dest
    {
      // If there is no destination, do ignore the transition.
      // This happens for instance with
      //   if
      //   :: false
      //   fi
      if (!$2)
	{
	  $$ = 0;
	}
      else
	{
	  $$ = new pair($1, $2);
	  namer->new_state(*$2);
	}
    }


transition:
  ':' ':' "atomic" '{' src_dest '}'
    {
      $$ = $5;
    }
  | ':' ':' src_dest
    {
      $$ = $3;
    }
%%

void
neverclaimyy::parser::error(const location_type& location,
			    const std::string& message)
{
  error_list.emplace_back(location, message);
}

namespace spot
{
  tgba_digraph_ptr
  neverclaim_parse(const std::string& name,
		   neverclaim_parse_error_list& error_list,
		   bdd_dict_ptr dict,
		   environment& env,
		   bool debug)
  {
    if (neverclaimyyopen(name))
      {
	error_list.emplace_back(spot::location(),
				std::string("Cannot open file ") + name);
	return 0;
      }
    formula_cache fcache;
    tgba_digraph_ptr result = make_tgba_digraph(dict);
    auto namer = result->create_namer<std::string>();
    result->set_single_acceptance_set();
    result->prop_state_based_acc();

    neverclaimyy::parser parser(error_list, env, result, namer, fcache);
    parser.set_debug_level(debug);
    parser.parse();
    neverclaimyyclose();

    if (accept_all_needed && !accept_all_seen)
      {
	unsigned n = namer->new_state("accept_all");
	result->new_acc_transition(n, n, bddtrue);
      }
    accept_all_needed = false;
    accept_all_seen = false;
    labels.clear();

    delete namer;
    return result;
  }
}

// Local Variables:
// mode: c++
// End:
