/* -*- coding: utf-8 -*-
** Copyright (C) 2009, 2010, 2012, 2013, 2014 Laboratoire de Recherche
** et Développement de l'Epita (LRDE).
** Copyright (C) 2003, 2004, 2005, 2006 Laboratoire d'Informatique de
** Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
** Université Pierre et Marie Curie.
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
%name-prefix "tgbayy"
%debug
%error-verbose
%define api.location.type "spot::location"

%code requires
{
#include <string>
#include "public.hh"
#include "priv/accmap.hh"
#include "tgba/formula2bdd.hh"

/* Cache parsed formulae.  Labels on arcs are frequently identical and
   it would be a waste of time to parse them to formula* over and
   over, and to register all their atomic_propositions in the
   bdd_dict.  Keep the bdd result around so we can reuse it.  */
  typedef std::map<std::string, bdd> formula_cache;
  typedef typename spot::tgba_digraph::namer<std::string>::type named_tgba_t;
}

%parse-param {spot::tgba_parse_error_list& error_list}
%parse-param {spot::ltl::environment& parse_environment}
%parse-param {spot::acc_mapper_string& acc_map}
%parse-param {spot::tgba_digraph*& result}
%parse-param {named_tgba_t*& namer}
%parse-param {formula_cache& fcache}
%union
{
  int token;
  std::string* str;
  const spot::ltl::formula* f;
  bdd* acc;
}

%code
{
#include "ltlast/constant.hh"
#include "ltlparse/public.hh"
#include <map>

/* tgbaparse.hh and parsedecl.hh include each other recursively.
   We must ensure that YYSTYPE is declared (by the above %union)
   before parsedecl.hh uses it. */
#include "parsedecl.hh"
using namespace spot::ltl;

typedef std::pair<bool, spot::ltl::formula*> pair;
}

%token <str> STRING UNTERMINATED_STRING
%token <str> IDENT
%type <str> strident string
%type <str> condition
%type <acc> acc_list
%token ACC_DEF

%destructor { delete $$; } <str>
%destructor { delete $$; } <acc>

%printer { debug_stream() << *$$; } <str>
%printer { debug_stream() << *$$; } <acc>

%%
tgba: acceptance_decl lines
      | acceptance_decl
      { namer->new_state("0"); }
      | lines
      |
      { namer->new_state("0"); };

acceptance_decl: ACC_DEF acc_decl ';'
      { acc_map.commit(); }

/* At least one line.  */
lines: line
       | lines line
       ;

line: strident ',' strident ',' condition ',' acc_list ';'
       {
	 bdd cond = bddtrue;
	 if ($5)
	   {
	     formula_cache::const_iterator i = fcache.find(*$5);
	     if (i == fcache.end())
	       {
		 parse_error_list pel;
		 const formula* f =
		   spot::ltl::parse_boolean(*$5, pel, parse_environment,
					    debug_level());
		 for (auto& j: pel)
		   {
		     // Adjust the diagnostic to the current position.
		     spot::location here = @5;
		     here.end.line = here.begin.line + j.first.end.line - 1;
		     here.end.column = here.begin.column + j.first.end.column;
		     here.begin.line += j.first.begin.line - 1;
		     here.begin.column += j.first.begin.column;
		     error_list.emplace_back(here, j.second);
		   }
		 if (f)
		   {
		     cond = formula_to_bdd(f, result->get_dict(), result);
		     f->destroy();
		   }
		 fcache[*$5] = cond;
	       }
	     else
	       {
		 cond = i->second;
	       }
	   }
	 unsigned s = namer->new_state(*$1);
	 unsigned d = namer->new_state(*$3);
	 namer->graph().new_transition(s, d, cond, *$7);
	 delete $1;
	 delete $3;
	 delete $5;
	 delete $7;
       }
       ;

string: STRING
       | UNTERMINATED_STRING
       {
	 $$ = $1;
	 error_list.emplace_back(@1, "unterminated string");
       }

strident: string | IDENT

condition:
       {
	 $$ = 0;
       }
       | string
       {
	 $$ = $1;
       }
       ;

acc_list:
       {
	 $$ = new bdd(bddfalse);
       }
       | acc_list strident
       {
	 if (*$2 != "" && *$2 != "false")
	   {
	     auto p = acc_map.lookup(*$2);
	     if (! p.first)
	       {
		 error_list.emplace_back(@2,
			 "undeclared acceptance condition `" + *$2 + "'");
		 // $2 will be destroyed on error recovery.
		 YYERROR;
	       }
	     *$1 |= p.second;
	   }
	 delete $2;
	 $$ = $1;
       }
       ;


acc_decl:
       | acc_decl strident
       {
	 if (! acc_map.declare(*$2))
	   {
	     std::string s = "acceptance condition `";
	     s += *$2;
	     s += "' unknown in environment `";
	     s += acc_map.get_env().name();
	     s += "'";
	     error_list.emplace_back(@2, s);
	     YYERROR;
	   }
	 delete $2;
       }
       ;

%%

void
tgbayy::parser::error(const location_type& location,
		      const std::string& message)
{
  error_list.emplace_back(location, message);
}

namespace spot
{
  tgba_digraph*
  tgba_parse(const std::string& name,
	     tgba_parse_error_list& error_list,
	     bdd_dict* dict,
	     environment& env,
	     environment& envacc,
	     bool debug)
  {
    if (tgbayyopen(name))
      {
	error_list.emplace_back(spot::location(),
				std::string("Cannot open file ") + name);
	return 0;
      }
    formula_cache fcache;
    tgba_digraph* result = new tgba_digraph(dict);
    auto namer = result->create_namer<std::string>();
    spot::acc_mapper_string acc_map(result, envacc);
    tgbayy::parser parser(error_list, env, acc_map, result, namer, fcache);
    parser.set_debug_level(debug);
    parser.parse();
    tgbayyclose();

    if (namer)			// No fatal error
      {
	delete namer;
	return result;
      }
    else			// Fatal error
      {
	delete result;
	return nullptr;
      }
  }
}

// Local Variables:
// mode: c++
// End:
