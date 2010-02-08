/* Copyright (C) 2009, 2010 Laboratoire de Recherche et Développement
** de l'Epita (LRDE).
** Copyright (C) 2003, 2004, 2005, 2006 Laboratoire d'Informatique de
** Paris 6 (LIP6), département Systèmes Répartis Coopératifs (SRC),
** Université Pierre et Marie Curie.
**
** This file is part of Spot, a model checking library.
**
** Spot is free software; you can redistribute it and/or modify it
** under the terms of the GNU General Public License as published by
** the Free Software Foundation; either version 2 of the License, or
** (at your option) any later version.
**
** Spot is distributed in the hope that it will be useful, but WITHOUT
** ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
** or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
** License for more details.
**
** You should have received a copy of the GNU General Public License
** along with Spot; see the file COPYING.  If not, write to the Free
** Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
** 02111-1307, USA.
*/
%language "C++"
%locations
%defines
%name-prefix "ltlyy"
%debug
%error-verbose
%expect 0

%code requires
{
#include <string>
#include "public.hh"
#include "ltlast/allnodes.hh"
}

%parse-param {spot::ltl::parse_error_list &error_list}
%parse-param {spot::ltl::environment &parse_environment}
%parse-param {spot::ltl::formula* &result}
%union
{
  std::string* str;
  spot::ltl::formula* ltl;
}

%code {
/* ltlparse.hh and parsedecl.hh include each other recursively.
   We mut ensure that YYSTYPE is declared (by the above %union)
   before parsedecl.hh uses it. */
#include "parsedecl.hh"
using namespace spot::ltl;

#define missing_right_op(res, op, str)			\
  do							\
    {							\
      error_list.push_back(parse_error(op,		\
       "missing right operand for \"" str "\""));	\
      res = constant::false_instance();			\
    }							\
  while (0);

#define missing_right_binop(res, left, op, str)	\
  do						\
    {						\
      left->destroy();				\
      missing_right_op(res, op, str);		\
    }						\
  while (0);

}


/* All tokens.  */

%token START_LTL "LTL start marker"
%token START_RATEXP "RATEXP start marker"
%token PAR_OPEN "opening parenthesis" PAR_CLOSE "closing parenthesis"
%token BRACE_OPEN "opening brace" BRACE_CLOSE "closing brace"
%token OP_OR "or operator" OP_XOR "xor operator" OP_AND "and operator"
%token OP_IMPLIES "implication operator" OP_EQUIV "equivalent operator"
%token OP_U "until operator" OP_R "release operator"
%token OP_W "weak until operator" OP_M "strong release operator"
%token OP_F "sometimes operator" OP_G "always operator"
%token OP_X "next operator" OP_NOT "not operator"
%token OP_UCONCAT "universal concat operator"
%token OP_ECONCAT "existential concat operator"
%token <str> ATOMIC_PROP "atomic proposition"
%token OP_STAR "star operator" OP_CONCAT "concat operator"
%token CONST_TRUE "constant true" CONST_FALSE "constant false"
%token END_OF_INPUT "end of formula" CONST_EMPTYWORD "empty word"
%token OP_POST_NEG "negative suffix" OP_POST_POS "positive suffix"

/* Priorities.  */

/* Low priority regex operator. */
%left OP_UCONCAT OP_ECONCAT

%left OP_CONCAT

/* Logical operators.  */
%left OP_IMPLIES OP_EQUIV
%left OP_OR
%left OP_XOR
%left OP_AND

/* LTL operators.  */
%left OP_U OP_R OP_M OP_W
%nonassoc OP_F OP_G
%nonassoc OP_X

/* High priority regex operator. */
%nonassoc OP_STAR

/* Not has the most important priority after Wring's `=0' and `=1'.  */
%nonassoc OP_NOT

%nonassoc OP_POST_NEG OP_POST_POS

%type <ltl> subformula booleanatom rationalexp bracedrationalexp

%destructor { delete $$; } <str>
%destructor { $$->destroy(); } <ltl>

%printer { debug_stream() << *$$; } <str>

%%
result:       START_LTL subformula END_OF_INPUT
	      { result = $2;
		YYACCEPT;
	      }
	    | START_LTL enderror
	      {
		result = 0;
		YYABORT;
	      }
	    | START_LTL subformula enderror
	      {
		result = $2;
		YYACCEPT;
	      }
	    | START_LTL emptyinput
              { YYABORT; }
            | START_RATEXP rationalexp END_OF_INPUT
	      { result = $2;
		YYACCEPT;
	      }
	    | START_RATEXP enderror
	      {
		result = 0;
		YYABORT;
	      }
	    | START_RATEXP rationalexp enderror
	      {
		result = $2;
		YYACCEPT;
	      }
	    | START_RATEXP emptyinput
              { YYABORT; }

emptyinput: END_OF_INPUT
              {
		error_list.push_back(parse_error(@$, "empty input"));
		result = 0;
	      }

enderror: error END_OF_INPUT
              {
		error_list.push_back(parse_error(@1,
						 "ignoring trailing garbage"));
	      }

/* The reason we use `constant::false_instance()' for error recovery
   is that it isn't reference counted.  (Hence it can't leak references.)  */

booleanatom: ATOMIC_PROP
	      {
		$$ = parse_environment.require(*$1);
		if (! $$)
		  {
		    std::string s = "unknown atomic proposition `";
		    s += *$1;
		    s += "' in environment `";
		    s += parse_environment.name();
		    s += "'";
		    error_list.push_back(parse_error(@1, s));
		    delete $1;
		    YYERROR;
		  }
		else
		  delete $1;
	      }
	    | ATOMIC_PROP OP_POST_POS
	      {
		$$ = parse_environment.require(*$1);
		if (! $$)
		  {
		    std::string s = "unknown atomic proposition `";
		    s += *$1;
		    s += "' in environment `";
		    s += parse_environment.name();
		    s += "'";
		    error_list.push_back(parse_error(@1, s));
		    delete $1;
		    YYERROR;
		  }
		else
		  delete $1;
	      }
	    | ATOMIC_PROP OP_POST_NEG
	      {
		$$ = parse_environment.require(*$1);
		if (! $$)
		  {
		    std::string s = "unknown atomic proposition `";
		    s += *$1;
		    s += "' in environment `";
		    s += parse_environment.name();
		    s += "'";
		    error_list.push_back(parse_error(@1, s));
		    delete $1;
		    YYERROR;
		  }
		else
		  delete $1;
		$$ = unop::instance(unop::Not, $$);
	      }
	    | CONST_TRUE
	      { $$ = constant::true_instance(); }
	    | CONST_FALSE
	      { $$ = constant::false_instance(); }

rationalexp: booleanatom
	    | CONST_EMPTYWORD
	      { $$ = constant::empty_word_instance(); }
	    | PAR_OPEN rationalexp PAR_CLOSE
	      { $$ = $2; }
	    | PAR_OPEN error PAR_CLOSE
	      { error_list.push_back(parse_error(@$,
		 "treating this parenthetical block as false"));
		$$ = constant::false_instance();
	      }
	    | PAR_OPEN rationalexp END_OF_INPUT
	      { error_list.push_back(parse_error(@1 + @2,
				      "missing closing parenthesis"));
		$$ = $2;
	      }
	    | PAR_OPEN error END_OF_INPUT
	      { error_list.push_back(parse_error(@$,
                    "missing closing parenthesis, "
		    "treating this parenthetical block as false"));
		$$ = constant::false_instance();
	      }
	    | rationalexp OP_AND rationalexp
	      { $$ = multop::instance(multop::And, $1, $3); }
	    | rationalexp OP_AND error
              { missing_right_binop($$, $1, @2, "and operator"); }
	    | rationalexp OP_OR rationalexp
	      { $$ = multop::instance(multop::Or, $1, $3); }
	    | rationalexp OP_OR error
              { missing_right_binop($$, $1, @2, "or operator"); }
	    | rationalexp OP_CONCAT rationalexp
	      { $$ = multop::instance(multop::Concat, $1, $3); }
	    | rationalexp OP_CONCAT error
              { missing_right_binop($$, $1, @2, "concat operator"); }
	    | rationalexp OP_STAR
	      { $$ = unop::instance(unop::Star, $1); }

bracedrationalexp: BRACE_OPEN rationalexp BRACE_CLOSE
              { $$ = $2; }
            | BRACE_OPEN error BRACE_CLOSE
	      { error_list.push_back(parse_error(@$,
		 "treating this brace block as false"));
		$$ = constant::false_instance();
	      }
            | BRACE_OPEN rationalexp END_OF_INPUT
	      { error_list.push_back(parse_error(@1 + @2,
				      "missing closing brace"));
		$$ = $2;
	      }
	    | BRACE_OPEN error END_OF_INPUT
	      { error_list.push_back(parse_error(@$,
                    "missing closing brace, "
		    "treating this brace block as false"));
		$$ = constant::false_instance();
	      }

subformula: booleanatom
	    | PAR_OPEN subformula PAR_CLOSE
	      { $$ = $2; }
	    | PAR_OPEN error PAR_CLOSE
	      { error_list.push_back(parse_error(@$,
		 "treating this parenthetical block as false"));
		$$ = constant::false_instance();
	      }
	    | PAR_OPEN subformula END_OF_INPUT
	      { error_list.push_back(parse_error(@1 + @2,
				      "missing closing parenthesis"));
		$$ = $2;
	      }
	    | PAR_OPEN error END_OF_INPUT
	      { error_list.push_back(parse_error(@$,
                    "missing closing parenthesis, "
		    "treating this parenthetical block as false"));
		$$ = constant::false_instance();
	      }
	    | subformula OP_AND subformula
	      { $$ = multop::instance(multop::And, $1, $3); }
	    | subformula OP_AND error
              { missing_right_binop($$, $1, @2, "and operator"); }
	    | subformula OP_OR subformula
	      { $$ = multop::instance(multop::Or, $1, $3); }
	    | subformula OP_OR error
              { missing_right_binop($$, $1, @2, "or operator"); }
	    | subformula OP_XOR subformula
	      { $$ = binop::instance(binop::Xor, $1, $3); }
	    | subformula OP_XOR error
	      { missing_right_binop($$, $1, @2, "xor operator"); }
	    | subformula OP_IMPLIES subformula
	      { $$ = binop::instance(binop::Implies, $1, $3); }
	    | subformula OP_IMPLIES error
	      { missing_right_binop($$, $1, @2, "implication operator"); }
	    | subformula OP_EQUIV subformula
	      { $$ = binop::instance(binop::Equiv, $1, $3); }
	    | subformula OP_EQUIV error
	      { missing_right_binop($$, $1, @2, "equivalent operator"); }
	    | subformula OP_U subformula
	      { $$ = binop::instance(binop::U, $1, $3); }
	    | subformula OP_U error
	      { missing_right_binop($$, $1, @2, "until operator"); }
	    | subformula OP_R subformula
	      { $$ = binop::instance(binop::R, $1, $3); }
	    | subformula OP_R error
	      { missing_right_binop($$, $1, @2, "release operator"); }
	    | subformula OP_W subformula
	      { $$ = binop::instance(binop::W, $1, $3); }
	    | subformula OP_W error
	      { missing_right_binop($$, $1, @2, "weak until operator"); }
	    | subformula OP_M subformula
	      { $$ = binop::instance(binop::M, $1, $3); }
	    | subformula OP_M error
	      { missing_right_binop($$, $1, @2, "strong release operator"); }
	    | OP_F subformula
	      { $$ = unop::instance(unop::F, $2); }
	    | OP_F error
	      { missing_right_op($$, @1, "sometimes operator"); }
	    | OP_G subformula
	      { $$ = unop::instance(unop::G, $2); }
	    | OP_G error
	      { missing_right_op($$, @1, "always operator"); }
	    | OP_X subformula
	      { $$ = unop::instance(unop::X, $2); }
	    | OP_X error
	      { missing_right_op($$, @1, "next operator"); }
	    | OP_NOT subformula
	      { $$ = unop::instance(unop::Not, $2); }
	    | OP_NOT error
	      { missing_right_op($$, @1, "not operator"); }
            | bracedrationalexp OP_UCONCAT subformula
	      { $$ = binop::instance(binop::UConcat, $1, $3); }
            | bracedrationalexp OP_UCONCAT error
	      { missing_right_binop($$, $1, @2, "universal concat operator"); }
            | bracedrationalexp OP_ECONCAT subformula
	      { $$ = binop::instance(binop::EConcat, $1, $3); }
            | bracedrationalexp OP_ECONCAT error
	      { missing_right_binop($$, $1, @2, "universal concat operator"); }
;

%%

void
ltlyy::parser::error(const location_type& location, const std::string& message)
{
  error_list.push_back(parse_error(location, message));
}

namespace spot
{
  namespace ltl
  {
    formula*
    parse(const std::string& ltl_string,
	  parse_error_list& error_list,
	  environment& env,
	  bool debug)
    {
      formula* result = 0;
      flex_set_buffer(ltl_string.c_str(),
		      ltlyy::parser::token::START_LTL);
      ltlyy::parser parser(error_list, env, result);
      parser.set_debug_level(debug);
      parser.parse();
      return result;
    }

    formula*
    parse_ratexp(const std::string& ratexp_string,
		 parse_error_list& error_list,
		 environment& env,
		 bool debug)
    {
      formula* result = 0;
      flex_set_buffer(ratexp_string.c_str(),
		      ltlyy::parser::token::START_RATEXP);
      ltlyy::parser parser(error_list, env, result);
      parser.set_debug_level(debug);
      parser.parse();
      return result;
    }

  }
}

// Local Variables:
// mode: c++
// End:
