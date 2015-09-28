/* -*- coding: utf-8 -*-
** Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014, 2015 Laboratoire
** de Recherche et Développement de l'Epita (LRDE).
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
%name-prefix "ltlyy"
%debug
%error-verbose
%expect 0
%lex-param { spot::ltl::parse_error_list& error_list }
%define api.location.type "spot::location"

%code requires
{
#include <string>
#include <sstream>
#include "public.hh"
#include "tl/formula.hh"
#include "tl/print.hh"

  struct minmax_t { unsigned min, max; };
}

%parse-param {spot::ltl::parse_error_list &error_list}
%parse-param {spot::ltl::environment &parse_environment}
%parse-param {spot::ltl::formula &result}
%union
{
  std::string* str;
  const spot::ltl::fnode* ltl;
  unsigned num;
  minmax_t minmax;
}

%code {
/* ltlparse.hh and parsedecl.hh include each other recursively.
   We mut ensure that YYSTYPE is declared (by the above %union)
   before parsedecl.hh uses it. */
#include "parsedecl.hh"
using namespace spot::ltl;

#define missing_right_op_msg(op, str)		\
  error_list.emplace_back(op,			\
    "missing right operand for \"" str "\"");

#define missing_right_op(res, op, str)		\
  do						\
    {						\
      missing_right_op_msg(op, str);		\
      res = fnode::ff();		\
    }						\
  while (0);

// right is missing, so complain and use left.
#define missing_right_binop(res, left, op, str)	\
  do						\
    {						\
      missing_right_op_msg(op, str);		\
      res = left;				\
    }						\
  while (0);

// right is missing, so complain and use false.
#define missing_right_binop_hard(res, left, op, str)	\
  do							\
    {							\
      left->destroy();					\
      missing_right_op(res, op, str);			\
    }							\
  while (0);

  enum parser_type { parser_ltl, parser_bool, parser_sere };

  static formula
  try_recursive_parse(const std::string& str,
		      const spot::location& location,
		      spot::ltl::environment& env,
		      bool debug,
		      parser_type type,
		      spot::ltl::parse_error_list& error_list)
    {
      // We want to parse a U (b U c) as two until operators applied
      // to the atomic propositions a, b, and c.  We also want to
      // parse a U (b == c) as one until operator applied to the
      // atomic propositions "a" and "b == c".  The only problem is
      // that we do not know anything about "==" or in general about
      // the syntax of atomic proposition of our users.
      //
      // To support that, the lexer will return "b U c" and "b == c"
      // as PAR_BLOCK tokens.  We then try to parse such tokens
      // recursively.  If, as in the case of "b U c", the block is
      // successfully parsed as a formula, we return this formula.
      // Otherwise, we convert the string into an atomic proposition
      // (it's up to the environment to check the syntax of this
      // proposition, and maybe reject it).

      if (str.empty())
	{
	  error_list.emplace_back(location, "unexpected empty block");
	  return nullptr;
	}

      spot::ltl::parse_error_list suberror;
      formula f;
      switch (type)
	{
	case parser_sere:
	  f = spot::ltl::parse_infix_sere(str, suberror, env, debug, true);
	  break;
	case parser_bool:
	  f = spot::ltl::parse_infix_boolean(str, suberror, env, debug, true);
	  break;
	case parser_ltl:
	  f = spot::ltl::parse_infix_psl(str, suberror, env, debug, true);
	  break;
	}

      if (suberror.empty())
	return f;

      f = env.require(str);
      if (!f)
	{
	  std::string s = "atomic proposition `";
	  s += str;
	  s += "' rejected by environment `";
	  s += env.name();
	  s += "'";
	  error_list.emplace_back(location, s);
	}
      return f;
    }
}


/* All tokens.  */

%token START_LTL "LTL start marker"
%token START_LBT "LBT start marker"
%token START_SERE "SERE start marker"
%token START_BOOL "BOOLEAN start marker"
%token PAR_OPEN "opening parenthesis" PAR_CLOSE "closing parenthesis"
%token <str> PAR_BLOCK "(...) block"
%token <str> BRA_BLOCK "{...} block"
%token <str> BRA_BANG_BLOCK "{...}! block"
%token BRACE_OPEN "opening brace" BRACE_CLOSE "closing brace"
%token BRACE_BANG_CLOSE "closing brace-bang"
%token OP_OR "or operator" OP_XOR "xor operator"
%token OP_AND "and operator" OP_SHORT_AND "short and operator"
%token OP_IMPLIES "implication operator" OP_EQUIV "equivalent operator"
%token OP_U "until operator" OP_R "release operator"
%token OP_W "weak until operator" OP_M "strong release operator"
%token OP_F "sometimes operator" OP_G "always operator"
%token OP_X "next operator" OP_NOT "not operator"
%token OP_STAR "star operator" OP_BSTAR "bracket star operator"
%token OP_BFSTAR "bracket fusion-star operator"
%token OP_PLUS "plus operator"
%token OP_FPLUS "fusion-plus operator"
%token OP_STAR_OPEN "opening bracket for star operator"
%token OP_FSTAR_OPEN "opening bracket for fusion-star operator"
%token OP_EQUAL_OPEN "opening bracket for equal operator"
%token OP_GOTO_OPEN "opening bracket for goto operator"
%token OP_SQBKT_CLOSE "closing bracket"
%token <num> OP_SQBKT_NUM "number for square bracket operator"
%token OP_UNBOUNDED "unbounded mark"
%token OP_SQBKT_SEP "separator for square bracket operator"
%token OP_UCONCAT "universal concat operator"
%token OP_ECONCAT "existential concat operator"
%token OP_UCONCAT_NONO "universal non-overlapping concat operator"
%token OP_ECONCAT_NONO "existential non-overlapping concat operator"
%token <str> ATOMIC_PROP "atomic proposition"
%token OP_CONCAT "concat operator" OP_FUSION "fusion operator"
%token CONST_TRUE "constant true" CONST_FALSE "constant false"
%token END_OF_INPUT "end of formula"
%token OP_POST_NEG "negative suffix" OP_POST_POS "positive suffix"

/* Priorities.  */

/* Low priority SERE-LTL binding operator. */
%nonassoc OP_UCONCAT OP_ECONCAT OP_UCONCAT_NONO OP_ECONCAT_NONO

%left OP_CONCAT
%left OP_FUSION

/* Logical operators.  */
%right OP_IMPLIES OP_EQUIV
%left OP_OR
%left OP_XOR
%left OP_AND OP_SHORT_AND

/* OP_STAR can be used as an AND when occurring in some LTL formula in
   Wring's syntax (so it has to be close to OP_AND), and as a Kleen
   Star in SERE (so it has to be close to OP_BSTAR -- luckily
   U/R/M/W/F/G/X are not used in SERE). */
%left OP_STAR

/* LTL operators.  */
%right OP_U OP_R OP_M OP_W
%nonassoc OP_F OP_G
%nonassoc OP_X

/* High priority regex operator. */
%nonassoc OP_BSTAR OP_STAR_OPEN OP_PLUS
          OP_BFSTAR OP_FSTAR_OPEN OP_FPLUS
          OP_EQUAL_OPEN OP_GOTO_OPEN

/* Not has the most important priority (after Wring's `=0' and `=1',
   but as those can only attach to atomic proposition, they do not
   need any precedence).  */
%nonassoc OP_NOT

%type <ltl> subformula booleanatom sere lbtformula boolformula
%type <ltl> bracedsere parenthesedsubformula
%type <minmax> starargs fstarargs equalargs sqbracketargs gotoargs

%destructor { delete $$; } <str>
%destructor { $$->destroy(); } <ltl>

%printer { debug_stream() << *$$; } <str>
%printer { spot::ltl::print_psl(debug_stream(), formula($$)); } <ltl>
%printer { spot::ltl::print_sere(debug_stream(), formula($$)); } sere bracedsere
%printer { debug_stream() << $$; } <num>
%printer { debug_stream() << $$.min << ".." << $$.max; } <minmax>

%%
result:       START_LTL subformula END_OF_INPUT
              {
		result = formula($2);
		YYACCEPT;
	      }
	    | START_LTL enderror
	      {
		result = nullptr;
		YYABORT;
	      }
	    | START_LTL subformula enderror
	      {
		result = formula($2);
		YYACCEPT;
	      }
	    | START_LTL emptyinput
              { YYABORT; }
            | START_BOOL boolformula END_OF_INPUT
	      {
		result = formula($2);
		YYACCEPT;
	      }
	    | START_BOOL enderror
	      {
		result = nullptr;
		YYABORT;
	      }
	    | START_BOOL boolformula enderror
	      {
		result = formula($2);
		YYACCEPT;
	      }
	    | START_BOOL emptyinput
              { YYABORT; }
            | START_SERE sere END_OF_INPUT
	      {
		result = formula($2);
		YYACCEPT;
	      }
	    | START_SERE enderror
	      {
		result = nullptr;
		YYABORT;
	      }
	    | START_SERE sere enderror
	      {
		result = formula($2);
		YYACCEPT;
	      }
	    | START_SERE emptyinput
              { YYABORT; }
            | START_LBT lbtformula END_OF_INPUT
	      {
		result = formula($2);
		YYACCEPT;
	      }
	    | START_LBT enderror
	      {
		result = nullptr;
		YYABORT;
	      }
	    | START_LBT lbtformula enderror
	      {
		result = formula($2);
		YYACCEPT;
	      }
	    | START_LBT emptyinput
              { YYABORT; }

emptyinput: END_OF_INPUT
              {
		error_list.emplace_back(@$, "empty input");
		result = nullptr;
	      }

enderror: error END_OF_INPUT
              {
		error_list.emplace_back(@1, "ignoring trailing garbage");
	      }


OP_SQBKT_SEP_unbounded: OP_SQBKT_SEP | OP_SQBKT_SEP OP_UNBOUNDED
OP_SQBKT_SEP_opt: | OP_SQBKT_SEP_unbounded
error_opt: | error

/* for [*i..j] and [=i..j] */
sqbracketargs: OP_SQBKT_NUM OP_SQBKT_SEP OP_SQBKT_NUM OP_SQBKT_CLOSE
              { $$.min = $1; $$.max = $3; }
	     | OP_SQBKT_NUM OP_SQBKT_SEP_unbounded OP_SQBKT_CLOSE
              { $$.min = $1; $$.max = fnode::unbounded(); }
	     | OP_SQBKT_SEP OP_SQBKT_NUM OP_SQBKT_CLOSE
              { $$.min = 0U; $$.max = $2; }
	     | OP_SQBKT_SEP_opt OP_SQBKT_CLOSE
              { $$.min = 0U; $$.max = fnode::unbounded(); }
	     | OP_SQBKT_NUM OP_SQBKT_CLOSE
              { $$.min = $$.max = $1; }

/* [->i..j] has default values that are different than [*] and [=]. */
gotoargs: OP_GOTO_OPEN OP_SQBKT_NUM OP_SQBKT_SEP OP_SQBKT_NUM OP_SQBKT_CLOSE
           { $$.min = $2; $$.max = $4; }
	  | OP_GOTO_OPEN OP_SQBKT_NUM OP_SQBKT_SEP_unbounded OP_SQBKT_CLOSE
           { $$.min = $2; $$.max = fnode::unbounded(); }
	  | OP_GOTO_OPEN OP_SQBKT_SEP OP_SQBKT_NUM OP_SQBKT_CLOSE
           { $$.min = 1U; $$.max = $3; }
	  | OP_GOTO_OPEN OP_SQBKT_SEP_unbounded OP_SQBKT_CLOSE
           { $$.min = 1U; $$.max = fnode::unbounded(); }
	  | OP_GOTO_OPEN OP_SQBKT_CLOSE
           { $$.min = $$.max = 1U; }
	  | OP_GOTO_OPEN OP_SQBKT_NUM OP_SQBKT_CLOSE
           { $$.min = $$.max = $2; }
	  | OP_GOTO_OPEN error OP_SQBKT_CLOSE
           { error_list.emplace_back(@$, "treating this goto block as [->]");
             $$.min = $$.max = 1U; }
          | OP_GOTO_OPEN error_opt END_OF_INPUT
	   { error_list.
	       emplace_back(@$, "missing closing bracket for goto operator");
	     $$.min = $$.max = 0U; }

kleen_star: OP_STAR | OP_BSTAR

starargs: kleen_star
            { $$.min = 0U; $$.max = fnode::unbounded(); }
        | OP_PLUS
	    { $$.min = 1U; $$.max = fnode::unbounded(); }
	| OP_STAR_OPEN sqbracketargs
	    { $$ = $2; }
	| OP_STAR_OPEN error OP_SQBKT_CLOSE
            { error_list.emplace_back(@$, "treating this star block as [*]");
              $$.min = 0U; $$.max = fnode::unbounded(); }
        | OP_STAR_OPEN error_opt END_OF_INPUT
	    { error_list.emplace_back(@$, "missing closing bracket for star");
	      $$.min = $$.max = 0U; }

fstarargs: OP_BFSTAR
            { $$.min = 0U; $$.max = fnode::unbounded(); }
        | OP_FPLUS
	    { $$.min = 1U; $$.max = fnode::unbounded(); }
	| OP_FSTAR_OPEN sqbracketargs
	    { $$ = $2; }
	| OP_FSTAR_OPEN error OP_SQBKT_CLOSE
            { error_list.emplace_back
		(@$, "treating this fusion-star block as [:*]");
              $$.min = 0U; $$.max = fnode::unbounded(); }
        | OP_FSTAR_OPEN error_opt END_OF_INPUT
	    { error_list.emplace_back
		(@$, "missing closing bracket for fusion-star");
	      $$.min = $$.max = 0U; }

equalargs: OP_EQUAL_OPEN sqbracketargs
	    { $$ = $2; }
	| OP_EQUAL_OPEN error OP_SQBKT_CLOSE
            { error_list.emplace_back(@$, "treating this equal block as [*]");
              $$.min = 0U; $$.max = fnode::unbounded(); }
        | OP_EQUAL_OPEN error_opt END_OF_INPUT
	    { error_list.
		emplace_back(@$, "missing closing bracket for equal operator");
	      $$.min = $$.max = 0U; }


booleanatom: ATOMIC_PROP
	      {
		$$ = parse_environment.require(*$1).to_node_();
		if (! $$)
		  {
		    std::string s = "unknown atomic proposition `";
		    s += *$1;
		    s += "' in environment `";
		    s += parse_environment.name();
		    s += "'";
		    error_list.emplace_back(@1, s);
		    delete $1;
		    YYERROR;
		  }
		else
		  delete $1;
	      }
	    | ATOMIC_PROP OP_POST_POS
	      {
		$$ = parse_environment.require(*$1).to_node_();
		if (! $$)
		  {
		    std::string s = "unknown atomic proposition `";
		    s += *$1;
		    s += "' in environment `";
		    s += parse_environment.name();
		    s += "'";
		    error_list.emplace_back(@1, s);
		    delete $1;
		    YYERROR;
		  }
		else
		  delete $1;
	      }
	    | ATOMIC_PROP OP_POST_NEG
	      {
		$$ = parse_environment.require(*$1).to_node_();
		if (! $$)
		  {
		    std::string s = "unknown atomic proposition `";
		    s += *$1;
		    s += "' in environment `";
		    s += parse_environment.name();
		    s += "'";
		    error_list.emplace_back(@1, s);
		    delete $1;
		    YYERROR;
		  }
		else
		  delete $1;
		$$ = fnode::unop(op::Not, $$);
	      }
	    | CONST_TRUE
	      { $$ = fnode::tt(); }
	    | CONST_FALSE
	      { $$ = fnode::ff(); }

sere: booleanatom
            | OP_NOT sere
	      {
		if ($2->is_boolean())
		  {
		    $$ = fnode::unop(op::Not, $2);
		  }
		else
		  {
		    error_list.emplace_back(@2,
                       "not a boolean expression: inside a SERE `!' can only "
                       "be applied to a Boolean expression");
		    error_list.emplace_back(@$, "treating this block as false");
		    $2->destroy();
		    $$ = fnode::ff();
		  }
	      }
            | bracedsere
	    | PAR_BLOCK
              {
		$$ =
		  try_recursive_parse(*$1, @1, parse_environment,
				      debug_level(), parser_sere, error_list)
		  .to_node_();
		delete $1;
		if (!$$)
		  YYERROR;
	      }
	    | PAR_OPEN sere PAR_CLOSE
	      { $$ = $2; }
	    | PAR_OPEN error PAR_CLOSE
	      { error_list.
		  emplace_back(@$,
			       "treating this parenthetical block as false");
		$$ = fnode::ff();
	      }
	    | PAR_OPEN sere END_OF_INPUT
	      { error_list.emplace_back(@1 + @2, "missing closing parenthesis");
		$$ = $2;
	      }
	    | PAR_OPEN error END_OF_INPUT
	      { error_list.emplace_back(@$,
                    "missing closing parenthesis, "
		    "treating this parenthetical block as false");
		$$ = fnode::ff();
	      }
	    | sere OP_AND sere
	      { $$ = fnode::multop(op::AndRat, {$1, $3}); }
	    | sere OP_AND error
	      { missing_right_binop($$, $1, @2,
				    "length-matching and operator"); }
	    | sere OP_SHORT_AND sere
	      { $$ = fnode::multop(op::AndNLM, {$1, $3}); }
	    | sere OP_SHORT_AND error
              { missing_right_binop($$, $1, @2,
                                    "non-length-matching and operator"); }
	    | sere OP_OR sere
	      { $$ = fnode::multop(op::OrRat, {$1, $3}); }
	    | sere OP_OR error
              { missing_right_binop($$, $1, @2, "or operator"); }
	    | sere OP_CONCAT sere
	      { $$ = fnode::multop(op::Concat, {$1, $3}); }
	    | sere OP_CONCAT error
              { missing_right_binop($$, $1, @2, "concat operator"); }
	    | sere OP_FUSION sere
	      { $$ = fnode::multop(op::Fusion, {$1, $3}); }
	    | sere OP_FUSION error
              { missing_right_binop($$, $1, @2, "fusion operator"); }
	    | starargs
	      {
		if ($1.max < $1.min)
		  {
		    error_list.emplace_back(@1, "reversed range");
		    std::swap($1.max, $1.min);
		  }
		$$ = fnode::bunop(op::Star, fnode::tt(), $1.min, $1.max);
	      }
	    | sere starargs
	      {
		if ($2.max < $2.min)
		  {
		    error_list.emplace_back(@2, "reversed range");
		    std::swap($2.max, $2.min);
		  }
		$$ = fnode::bunop(op::Star, $1, $2.min, $2.max);
	      }
	    | sere fstarargs
	      {
		if ($2.max < $2.min)
		  {
		    error_list.emplace_back(@2, "reversed range");
		    std::swap($2.max, $2.min);
		  }
		$$ = fnode::bunop(op::FStar, $1, $2.min, $2.max);
	      }
	    | sere equalargs
	      {
		if ($2.max < $2.min)
		  {
		    error_list.emplace_back(@2, "reversed range");
		    std::swap($2.max, $2.min);
		  }
		if ($1->is_boolean())
		  {
		    $$ = formula::sugar_equal(formula($1),
					      $2.min, $2.max).to_node_();
		  }
		else
		  {
		    error_list.emplace_back(@1,
				"not a boolean expression: [=...] can only "
				"be applied to a Boolean expression");
		    error_list.emplace_back(@$,
				"treating this block as false");
		    $1->destroy();
		    $$ = fnode::ff();
		  }
	      }
	    | sere gotoargs
	      {
		if ($2.max < $2.min)
		  {
		    error_list.emplace_back(@2, "reversed range");
		    std::swap($2.max, $2.min);
		  }
		if ($1->is_boolean())
		  {
		    $$ = formula::sugar_goto(formula($1),
					     $2.min, $2.max).to_node_();
		  }
		else
		  {
		    error_list.emplace_back(@1,
				"not a boolean expression: [->...] can only "
				"be applied to a Boolean expression");
		    error_list.emplace_back(@$,
				"treating this block as false");
		    $1->destroy();
		    $$ = fnode::ff();
		  }
	      }
	    | sere OP_XOR sere
	      {
		if ($1->is_boolean() && $3->is_boolean())
		  {
		    $$ = fnode::binop(op::Xor, $1, $3);
		  }
		else
		  {
		    if (!$1->is_boolean())
		      {
			error_list.emplace_back(@1,
                         "not a boolean expression: inside SERE `<->' can only "
                         "be applied to Boolean expressions");
                      }
		    if (!$3->is_boolean())
		      {
			error_list.emplace_back(@3,
                         "not a boolean expression: inside SERE `<->' can only "
                         "be applied to Boolean expressions");
                      }
		    error_list.emplace_back(@$, "treating this block as false");
		    $1->destroy();
		    $3->destroy();
		    $$ = fnode::ff();
		  }
	      }
	    | sere OP_XOR error
	      { missing_right_binop($$, $1, @2, "xor operator"); }
	    | sere OP_IMPLIES sere
	      {
		if ($1->is_boolean())
		  {
		    $$ = fnode::binop(op::Implies, $1, $3);
		  }
		else
		  {
		    if (!$1->is_boolean())
		      {
			error_list.emplace_back(@1,
                         "not a boolean expression: inside SERE `->' can only "
                         "be applied to a Boolean expression");
                      }
		    error_list.emplace_back(@$, "treating this block as false");
		    $1->destroy();
		    $3->destroy();
		    $$ = fnode::ff();
		  }
	      }
	    | sere OP_IMPLIES error
	      { missing_right_binop($$, $1, @2, "implication operator"); }
	    | sere OP_EQUIV sere
	      {
		if ($1->is_boolean() && $3->is_boolean())
		  {
		    $$ = fnode::binop(op::Equiv, $1, $3);
		  }
		else
		  {
		    if (!$1->is_boolean())
		      {
			error_list.emplace_back(@1,
                         "not a boolean expression: inside SERE `<->' can only "
                         "be applied to Boolean expressions");
                      }
		    if (!$3->is_boolean())
		      {
			error_list.emplace_back(@3,
                         "not a boolean expression: inside SERE `<->' can only "
                         "be applied to Boolean expressions");
                      }
		    error_list.emplace_back(@$, "treating this block as false");
		    $1->destroy();
		    $3->destroy();
		    $$ = fnode::ff();
		  }
	      }
	    | sere OP_EQUIV error
	      { missing_right_binop($$, $1, @2, "equivalent operator"); }

bracedsere: BRACE_OPEN sere BRACE_CLOSE
              { $$ = $2; }
            | BRACE_OPEN sere error BRACE_CLOSE
	      { error_list.emplace_back(@3, "ignoring this");
		$$ = $2;
	      }
            | BRACE_OPEN error BRACE_CLOSE
	      { error_list.emplace_back(@$,
					"treating this brace block as false");
		$$ = fnode::ff();
	      }
            | BRACE_OPEN sere END_OF_INPUT
	      { error_list.emplace_back(@1 + @2,
					"missing closing brace");
		$$ = $2;
	      }
	    | BRACE_OPEN sere error END_OF_INPUT
	      { error_list. emplace_back(@3,
                  "ignoring trailing garbage and missing closing brace");
		$$ = $2;
	      }
	    | BRACE_OPEN error END_OF_INPUT
	      { error_list.emplace_back(@$,
                    "missing closing brace, "
		    "treating this brace block as false");
		$$ = fnode::ff();
	      }
            | BRA_BLOCK
              {
		$$ = try_recursive_parse(*$1, @1, parse_environment,
					 debug_level(),
					 parser_sere, error_list).to_node_();
		delete $1;
		if (!$$)
		  YYERROR;
	      }

parenthesedsubformula: PAR_BLOCK
              {
		$$ = try_recursive_parse(*$1, @1, parse_environment,
					 debug_level(), parser_ltl, error_list)
		  .to_node_();
		delete $1;
		if (!$$)
		  YYERROR;
	      }
            | PAR_OPEN subformula PAR_CLOSE
	      { $$ = $2; }
	    | PAR_OPEN subformula error PAR_CLOSE
	      { error_list.emplace_back(@3, "ignoring this");
		$$ = $2;
	      }
	    | PAR_OPEN error PAR_CLOSE
	      { error_list.emplace_back(@$,
		 "treating this parenthetical block as false");
		$$ = fnode::ff();
	      }
	    | PAR_OPEN subformula END_OF_INPUT
	      { error_list.emplace_back(@1 + @2, "missing closing parenthesis");
		$$ = $2;
	      }
	    | PAR_OPEN subformula error END_OF_INPUT
	      { error_list.emplace_back(@3,
                "ignoring trailing garbage and missing closing parenthesis");
		$$ = $2;
	      }
	    | PAR_OPEN error END_OF_INPUT
	      { error_list.emplace_back(@$,
                    "missing closing parenthesis, "
		    "treating this parenthetical block as false");
		$$ = fnode::ff();
	      }


boolformula: booleanatom
            | PAR_BLOCK
              {
		$$ = try_recursive_parse(*$1, @1, parse_environment,
					 debug_level(), parser_bool, error_list)
		  .to_node_();
		delete $1;
		if (!$$)
		  YYERROR;
	      }
            | PAR_OPEN boolformula PAR_CLOSE
	      { $$ = $2; }
	    | PAR_OPEN boolformula error PAR_CLOSE
	      { error_list.emplace_back(@3, "ignoring this");
		$$ = $2;
	      }
	    | PAR_OPEN error PAR_CLOSE
	      { error_list.emplace_back(@$,
		 "treating this parenthetical block as false");
		$$ = fnode::ff();
	      }
	    | PAR_OPEN boolformula END_OF_INPUT
	      { error_list.emplace_back(@1 + @2,
					"missing closing parenthesis");
		$$ = $2;
	      }
	    | PAR_OPEN boolformula error END_OF_INPUT
	      { error_list.emplace_back(@3,
                "ignoring trailing garbage and missing closing parenthesis");
		$$ = $2;
	      }
	    | PAR_OPEN error END_OF_INPUT
	      { error_list.emplace_back(@$,
                    "missing closing parenthesis, "
		    "treating this parenthetical block as false");
		$$ = fnode::ff();
	      }
	    | boolformula OP_AND boolformula
	      { $$ = fnode::multop(op::And, {$1, $3}); }
	    | boolformula OP_AND error
              { missing_right_binop($$, $1, @2, "and operator"); }
	    | boolformula OP_SHORT_AND boolformula
	      { $$ = fnode::multop(op::And, {$1, $3}); }
	    | boolformula OP_SHORT_AND error
              { missing_right_binop($$, $1, @2, "and operator"); }
	    | boolformula OP_STAR boolformula
	      { $$ = fnode::multop(op::And, {$1, $3}); }
	    | boolformula OP_STAR error
              { missing_right_binop($$, $1, @2, "and operator"); }
	    | boolformula OP_OR boolformula
	      { $$ = fnode::multop(op::Or, {$1, $3}); }
	    | boolformula OP_OR error
              { missing_right_binop($$, $1, @2, "or operator"); }
	    | boolformula OP_XOR boolformula
	      { $$ = fnode::binop(op::Xor, $1, $3); }
	    | boolformula OP_XOR error
	      { missing_right_binop($$, $1, @2, "xor operator"); }
	    | boolformula OP_IMPLIES boolformula
	      { $$ = fnode::binop(op::Implies, $1, $3); }
	    | boolformula OP_IMPLIES error
	      { missing_right_binop($$, $1, @2, "implication operator"); }
	    | boolformula OP_EQUIV boolformula
	      { $$ = fnode::binop(op::Equiv, $1, $3); }
	    | boolformula OP_EQUIV error
	      { missing_right_binop($$, $1, @2, "equivalent operator"); }
	    | OP_NOT boolformula
	      { $$ = fnode::unop(op::Not, $2); }
	    | OP_NOT error
	      { missing_right_op($$, @1, "not operator"); }

subformula: booleanatom
            | parenthesedsubformula
	    | subformula OP_AND subformula
              { $$ = fnode::multop(op::And, {$1, $3}); }
	    | subformula OP_AND error
              { missing_right_binop($$, $1, @2, "and operator"); }
	    | subformula OP_SHORT_AND subformula
	      { $$ = fnode::multop(op::And, {$1, $3}); }
	    | subformula OP_SHORT_AND error
              { missing_right_binop($$, $1, @2, "and operator"); }
	    | subformula OP_STAR subformula
	      { $$ = fnode::multop(op::And, {$1, $3}); }
	    | subformula OP_STAR error
              { missing_right_binop($$, $1, @2, "and operator"); }
	    | subformula OP_OR subformula
	      { $$ = fnode::multop(op::Or, {$1, $3}); }
	    | subformula OP_OR error
              { missing_right_binop($$, $1, @2, "or operator"); }
	    | subformula OP_XOR subformula
 	      { $$ = fnode::binop(op::Xor, $1, $3); }
	    | subformula OP_XOR error
	      { missing_right_binop($$, $1, @2, "xor operator"); }
	    | subformula OP_IMPLIES subformula
	      { $$ = fnode::binop(op::Implies, $1, $3); }
	    | subformula OP_IMPLIES error
	      { missing_right_binop($$, $1, @2, "implication operator"); }
	    | subformula OP_EQUIV subformula
	      { $$ = fnode::binop(op::Equiv, $1, $3); }
	    | subformula OP_EQUIV error
	      { missing_right_binop($$, $1, @2, "equivalent operator"); }
	    | subformula OP_U subformula
	      { $$ = fnode::binop(op::U, $1, $3); }
	    | subformula OP_U error
	      { missing_right_binop($$, $1, @2, "until operator"); }
	    | subformula OP_R subformula
	      { $$ = fnode::binop(op::R, $1, $3); }
	    | subformula OP_R error
	      { missing_right_binop($$, $1, @2, "release operator"); }
	    | subformula OP_W subformula
	      { $$ = fnode::binop(op::W, $1, $3); }
	    | subformula OP_W error
	      { missing_right_binop($$, $1, @2, "weak until operator"); }
	    | subformula OP_M subformula
	      { $$ = fnode::binop(op::M, $1, $3); }
	    | subformula OP_M error
	      { missing_right_binop($$, $1, @2, "strong release operator"); }
	    | OP_F subformula
	      { $$ = fnode::unop(op::F, $2); }
	    | OP_F error
	      { missing_right_op($$, @1, "sometimes operator"); }
	    | OP_G subformula
	      { $$ = fnode::unop(op::G, $2); }
	    | OP_G error
	      { missing_right_op($$, @1, "always operator"); }
	    | OP_X subformula
	      { $$ = fnode::unop(op::X, $2); }
	    | OP_X error
	      { missing_right_op($$, @1, "next operator"); }
	    | OP_NOT subformula
	      { $$ = fnode::unop(op::Not, $2); }
	    | OP_NOT error
	      { missing_right_op($$, @1, "not operator"); }
            | bracedsere
	      { $$ = fnode::unop(op::Closure, $1); }
            | bracedsere OP_UCONCAT subformula
	      { $$ = fnode::binop(op::UConcat, $1, $3); }
            | bracedsere parenthesedsubformula
	      { $$ = fnode::binop(op::UConcat, $1, $2); }
            | bracedsere OP_UCONCAT error
	      { missing_right_binop_hard($$, $1, @2,
				    "universal overlapping concat operator"); }
            | bracedsere OP_ECONCAT subformula
	      { $$ = fnode::binop(op::EConcat, $1, $3); }
            | bracedsere OP_ECONCAT error
	      { missing_right_binop_hard($$, $1, @2,
				    "existential overlapping concat operator");
	      }
            | bracedsere OP_UCONCAT_NONO subformula
	      /* {SERE}[]=>EXP = {SERE;1}[]->EXP */
	      { $$ = fnode::binop(op::UConcat,
				  fnode::multop(op::Concat, {$1, fnode::tt()}),
				  $3); }
            | bracedsere OP_UCONCAT_NONO error
	      { missing_right_binop_hard($$, $1, @2,
				  "universal non-overlapping concat operator");
	      }
            | bracedsere OP_ECONCAT_NONO subformula
	      /* {SERE}<>=>EXP = {SERE;1}<>->EXP */
	      { $$ = fnode::binop(op::EConcat,
				  fnode::multop(op::Concat, {$1, fnode::tt()}),
				  $3); }
            | bracedsere OP_ECONCAT_NONO error
	      { missing_right_binop_hard($$, $1, @2,
				"existential non-overlapping concat operator");
	      }
            | BRACE_OPEN sere BRACE_BANG_CLOSE
	      /* {SERE}! = {SERE} <>-> 1 */
	      { $$ = fnode::binop(op::EConcat, $2, fnode::tt()); }
            | BRA_BANG_BLOCK
              {
		$$ = try_recursive_parse(*$1, @1, parse_environment,
					 debug_level(), parser_sere, error_list)
		  .to_node_();
		delete $1;
		if (!$$)
		  YYERROR;
		$$ = fnode::binop(op::EConcat, $$, fnode::tt());
	      }

lbtformula: ATOMIC_PROP
	      {
		$$ = parse_environment.require(*$1).to_node_();
		if (! $$)
		  {
		    std::string s = "atomic proposition `";
		    s += *$1;
		    s += "' rejected by environment `";
		    s += parse_environment.name();
		    s += "'";
		    error_list.emplace_back(@1, s);
		    delete $1;
		    YYERROR;
		  }
		else
		  delete $1;
	      }
            | '!' lbtformula
	      { $$ = fnode::unop(op::Not, $2); }
            | '&' lbtformula lbtformula
	      { $$ = fnode::multop(op::And, {$2, $3}); }
            | '|' lbtformula lbtformula
	      { $$ = fnode::multop(op::Or, {$2, $3}); }
            | '^' lbtformula lbtformula
	      { $$ = fnode::binop(op::Xor, $2, $3); }
            | 'i' lbtformula lbtformula
	      { $$ = fnode::binop(op::Implies, $2, $3); }
            | 'e' lbtformula lbtformula
	      { $$ = fnode::binop(op::Equiv, $2, $3); }
            | 'X' lbtformula
	      { $$ = fnode::unop(op::X, $2); }
            | 'F' lbtformula
	      { $$ = fnode::unop(op::F, $2); }
            | 'G' lbtformula
	      { $$ = fnode::unop(op::G, $2); }
            | 'U' lbtformula lbtformula
	      { $$ = fnode::binop(op::U, $2, $3); }
            | 'V' lbtformula lbtformula
	      { $$ = fnode::binop(op::R, $2, $3); }
            | 'R' lbtformula lbtformula
	      { $$ = fnode::binop(op::R, $2, $3); }
            | 'W' lbtformula lbtformula
	      { $$ = fnode::binop(op::W, $2, $3); }
            | 'M' lbtformula lbtformula
	      { $$ = fnode::binop(op::M, $2, $3); }
            | 't'
	      { $$ = fnode::tt(); }
            | 'f'
	      { $$ = fnode::ff(); }
            ;

%%

void
ltlyy::parser::error(const location_type& location, const std::string& message)
{
  error_list.emplace_back(location, message);
}

namespace spot
{
  namespace ltl
  {
    formula
    parse_infix_psl(const std::string& ltl_string,
		    parse_error_list& error_list,
		    environment& env,
		    bool debug, bool lenient)
    {
      formula result = nullptr;
      flex_set_buffer(ltl_string,
		      ltlyy::parser::token::START_LTL,
		      lenient);
      ltlyy::parser parser(error_list, env, result);
      parser.set_debug_level(debug);
      parser.parse();
      flex_unset_buffer();
      return result;
    }

    formula
    parse_infix_boolean(const std::string& ltl_string,
			parse_error_list& error_list,
			environment& env,
			bool debug, bool lenient)
    {
      formula result = nullptr;
      flex_set_buffer(ltl_string,
		      ltlyy::parser::token::START_BOOL,
		      lenient);
      ltlyy::parser parser(error_list, env, result);
      parser.set_debug_level(debug);
      parser.parse();
      flex_unset_buffer();
      return result;
    }

    formula
    parse_prefix_ltl(const std::string& ltl_string,
	  parse_error_list& error_list,
	  environment& env,
	  bool debug)
    {
      formula result = nullptr;
      flex_set_buffer(ltl_string,
		      ltlyy::parser::token::START_LBT,
		      false);
      ltlyy::parser parser(error_list, env, result);
      parser.set_debug_level(debug);
      parser.parse();
      flex_unset_buffer();
      return result;
    }

    formula
    parse_infix_sere(const std::string& sere_string,
		     parse_error_list& error_list,
		     environment& env,
		     bool debug,
		     bool lenient)
    {
      formula result = nullptr;
      flex_set_buffer(sere_string,
		      ltlyy::parser::token::START_SERE,
		      lenient);
      ltlyy::parser parser(error_list, env, result);
      parser.set_debug_level(debug);
      parser.parse();
      flex_unset_buffer();
      return result;
    }

    formula
    parse_formula(const std::string& ltl_string, environment& env)
    {
      parse_error_list pel;
      formula f = parse_infix_psl(ltl_string, pel, env);
      std::ostringstream s;
      if (format_parse_errors(s, ltl_string, pel))
	{
	  parse_error_list pel2;
	  formula g = parse_prefix_ltl(ltl_string, pel2, env);
	  if (pel2.empty())
	    return g;
	  else
	    throw parse_error(s.str());
	}
      return f;
    }

  }
}

// Local Variables:
// mode: c++
// End:
