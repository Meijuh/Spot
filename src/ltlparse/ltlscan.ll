/* Copyright (C) 2010, 2011, 2012, Laboratoire de Recherche et
** Développement de l'Epita (LRDE).
** Copyright (C) 2003, 2004  Laboratoire d'Informatique de Paris 6 (LIP6),
** département Systèmes Répartis Coopératifs (SRC), Université Pierre
** et Marie Curie.
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
%option noyywrap warn 8bit batch
%option prefix="ltlyy"
%option outfile="lex.yy.c"

%{
#include <string>
#include <boost/lexical_cast.hpp>
#include "ltlparse/parsedecl.hh"

/* Hack Flex so we read from a string instead of reading from a file.  */
#define YY_INPUT(buf, result, max_size)					\
  do {									\
    result = (max_size < to_parse_size) ? max_size : to_parse_size;	\
    memcpy(buf, to_parse, result);					\
    to_parse_size -= result;						\
    to_parse += result;							\
  } while (0);

#define YY_USER_ACTION \
  yylloc->columns(yyleng);

static const char* to_parse = 0;
static size_t to_parse_size = 0;
static int start_token = 0;

typedef ltlyy::parser::token token;

void
flex_set_buffer(const char* buf, int start_tok)
{
  to_parse = buf;
  to_parse_size = strlen(to_parse);
  start_token = start_tok;
}

%}

%s not_prop
%x sqbracket

BOX       "[]"|"□"|"⬜"|"◻"
DIAMOND   "<>"|"◇"|"⋄"|"♢"
ARROWL    "->"|"-->"|"→"|"⟶"
DARROWL   "=>"|"⇒"|"⟹"
ARROWLR   "<->"|"<-->"|"↔"
DARROWLR  "<=>"|"⇔"
CIRCLE    "()"|"○"|"◯"
NOT       "!"|"~"|"¬"
BOXARROW  {BOX}{ARROWL}|"|"{ARROWL}|"↦"
BOXDARROW {BOX}{DARROWL}|"|"{DARROWL}|"⤇"

%%

%{
  if (start_token)
    {
      int t = start_token;
      start_token = 0;
      return t;
    }
  yylloc->step();
%}

"("				BEGIN(0); return token::PAR_OPEN;
")"				BEGIN(not_prop); return token::PAR_CLOSE;
"{"                             BEGIN(0); return token::BRACE_OPEN;
"}"[ \t\n]*"!"			BEGIN(not_prop); return token::BRACE_BANG_CLOSE;
"}"				BEGIN(not_prop); return token::BRACE_CLOSE;

  /* Must go before the other operators, because the F of FALSE
     should not be mistaken with a unary F. */
"1"|[tT][rR][uU][eE]		BEGIN(0); return token::CONST_TRUE;
"0"|[fF][aA][lL][sS][eE]	BEGIN(0); return token::CONST_FALSE;


  /* ~ comes from Goal, ! from everybody else */
{NOT}				BEGIN(0); return token::OP_NOT;

  /* PSL operators */
{BOXARROW}			BEGIN(0); return token::OP_UCONCAT;
{DIAMOND}{ARROWL}		BEGIN(0); return token::OP_ECONCAT;
{BOXDARROW}			BEGIN(0); return token::OP_UCONCAT_NONO;
{DIAMOND}{DARROWL}		BEGIN(0); return token::OP_ECONCAT_NONO;
";"				BEGIN(0); return token::OP_CONCAT;
":"				BEGIN(0); return token::OP_FUSION;
"*"				BEGIN(0); return token::OP_STAR;
"[*]"				BEGIN(0); return token::OP_BSTAR;
"[+]"				BEGIN(0); return token::OP_PLUS;
"[*"				BEGIN(sqbracket); return token::OP_STAR_OPEN;
"[="				BEGIN(sqbracket); return token::OP_EQUAL_OPEN;
"["{ARROWL}			BEGIN(sqbracket); return token::OP_GOTO_OPEN;
<sqbracket>"]"			BEGIN(0); return token::OP_SQBKT_CLOSE;
<sqbracket>[0-9]+		{
                                  unsigned num = 0;
                                  try {
                                    num = boost::lexical_cast<unsigned>(yytext);
				    yylval->num = num;
				    return token::OP_SQBKT_NUM;
                                  }
                                  catch (boost::bad_lexical_cast &)
                                  {
                                    error_list.push_back(
				      spot::ltl::parse_error(*yylloc,
					"value too large ignored"));
				    // Skip this number and read next token
                                    yylloc->step();
				  }
				}
  /* .. is from PSL and EDL
   : is from Verilog and PSL
   to is from VHDL
   , is from Perl */
<sqbracket>","|".."|":"|"to"	return token::OP_SQBKT_SEP;

  /* In SVA you use [=1:$] instead of [=1..].  We will also accept
     [=1..$] and [=1:].  The PSL LRM shows examples like [=1:inf]
     instead, so will accept this too.  */
<sqbracket>"$"|"inf"		return token::OP_UNBOUNDED;

  /* & and | come from Spin.  && and || from LTL2BA.
     /\, \/, and xor are from LBTT.
     --> and <--> come from Goal.
     +,*,^ are from Wring. */
"||"|"|"|"+"|"\\/"|"∨"|"∪"	BEGIN(0); return token::OP_OR;
"&&"|"/\\"|"∧"|"∩"		BEGIN(0); return token::OP_AND;
"&"				BEGIN(0); return token::OP_SHORT_AND;
"^"|"xor"|"⊕"			BEGIN(0); return token::OP_XOR;
{ARROWL}|{DARROWL}		BEGIN(0); return token::OP_IMPLIES;
{ARROWLR}|{DARROWLR}		BEGIN(0); return token::OP_EQUIV;

  /* <>, [], and () are used in Spin.  */
"F"|{DIAMOND}			BEGIN(0); return token::OP_F;
"G"|{BOX}			BEGIN(0); return token::OP_G;
"U"				BEGIN(0); return token::OP_U;
"R"|"V"				BEGIN(0); return token::OP_R;
"X"|{CIRCLE}			BEGIN(0); return token::OP_X;
"W"				BEGIN(0); return token::OP_W;
"M"				BEGIN(0); return token::OP_M;

  /* The combining overline or macron (overbar) should normally
     occur only after a single letter, but we do not check that. */
"=0"|"̅"|"̄"			return token::OP_POST_NEG;
"=1"				return token::OP_POST_POS;

<*>[ \t\n]+			/* discard whitespace */ yylloc->step ();

  /* An Atomic proposition cannot start with the letter
     used by a unary operator (F,G,X), unless this
     letter is followed by a digit in which case we assume
     it's an ATOMIC_PROP (even though F0 could be seen as Ffalse, we
     don't, because Ffalse is never used in practice).
  */
<INITIAL>[a-zA-EH-WYZ_.][a-zA-Z0-9_.]* |
<INITIAL>[FGX][0-9][a-zA-Z0-9_.]* |
  /*
     However if we have just parsed an atomic proposition, then we are
     not expecting another atomic proposition, so we can be stricter
     and disallow propositions that start with M, U, R, V, and W.  If
     you wonder why we do this, consider the Wring formula `p=0Uq=1'.
     When p is parsed, we enter the not_prop start condition, we
     remain into this condition when `=0' is processed, and then
     because we are in this condition we will not consider `Uq' as an
     atomic proposition but as a `U' operator followed by a `q' atomic
     proposition.

     We also disable atomic proposition that may look like a combination
     of a binary operator followed by several unary operators.
     E.g. UFXp.   This way, `p=0UFXp=1' will be parsed as `(p=0)U(F(X(p=1)))'.
  */
<not_prop>[a-zA-EH-LN-QSTYZ_.][a-zA-EH-WYZ0-9_.]* |
<not_prop>[a-zA-EH-LN-QSTYZ_.][a-zA-EH-WYZ0-9_.][a-zA-Z0-9_.]* {
			  yylval->str = new std::string(yytext, yyleng);
			  BEGIN(not_prop);
			  return token::ATOMIC_PROP;
			}

  /* Atomic propositions can also be enclosed in double quotes.  */
\"[^\"]*\"		{
			  yylval->str = new std::string(yytext + 1,
							yyleng - 2);
			  BEGIN(not_prop);
			  return token::ATOMIC_PROP;
			}

<*>.			return *yytext;

<<EOF>>			return token::END_OF_INPUT;

%{
  /* Dummy use of yyunput to shut up a gcc warning.  */
  (void) &yyunput;
%}
