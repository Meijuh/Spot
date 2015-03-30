/* -*- coding: utf-8 -*-
** Copyright (C) 2014, 2015 Laboratoire de Recherche et Développement
** de l'Epita (LRDE).
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
%option noyywrap
%option prefix="hoayy"
%option outfile="lex.yy.c"
/* %option debug */

%{
#include <string>
#include <sys/stat.h>
#include "hoaparse/parsedecl.hh"
#include "misc/escape.hh"

#define YY_USER_ACTION yylloc->columns(yyleng);
#define YY_NEVER_INTERACTIVE 1

typedef hoayy::parser::token token;
static unsigned comment_level = 0;
static unsigned parent_level = 0;
static int orig_cond = 0;
static bool lbtt_s = false;
static bool lbtt_t = false;
static unsigned lbtt_states = 0;

%}

eol         \n+|\r+
eol2        (\n\r)+|(\r\n)+
identifier  [[:alpha:]_][[:alnum:]_-]*

%x in_COMMENT in_STRING in_NEVER_PAR
%s in_HOA in_NEVER in_LBTT_HEADER
%s in_LBTT_STATE in_LBTT_INIT in_LBTT_TRANS
%s in_LBTT_T_ACC in_LBTT_S_ACC in_LBTT_GUARD
%%

%{
  std::string s;
  yylloc->step();

  auto parse_int = [&](){
    errno = 0;
    char* end;
    unsigned long n = strtoul(yytext, &end, 10);
    yylval->num = n;
    if (errno || yylval->num != n)
      {
        error_list.push_back(spot::hoa_parse_error(*yylloc, "value too large"));
        yylval->num = 0;
      }
    return end;
  };
%}


                        /* skip blanks and comments */
{eol}			yylloc->lines(yyleng); yylloc->step();
{eol2}			yylloc->lines(yyleng / 2); yylloc->step();
[ \t\v\f]+		yylloc->step();
"/""*"+			{
                          orig_cond = YY_START;
			  BEGIN(in_COMMENT);
			  comment_level = 1;
			}
<INITIAL>"HOA:"           BEGIN(in_HOA); return token::HOA;
<INITIAL,in_HOA>"--ABORT--" BEGIN(INITIAL); throw spot::hoa_abort{*yylloc};
<INITIAL>"never"	  BEGIN(in_NEVER); return token::NEVER;

<INITIAL>[0-9]+[ \t][0-9]+[ts]?  {
	                  BEGIN(in_LBTT_HEADER);
			  char* end = 0;
			  errno = 0;
			  unsigned long n = strtoul(yytext, &end, 10);
			  yylval->num = n;
			  unsigned s = end - yytext;
			  yylloc->end = yylloc->begin;
 			  yylloc->end.columns(s);
			  yyless(s);
			  if (errno || yylval->num != n)
			    {
                              error_list.push_back(
			        spot::hoa_parse_error(*yylloc,
				  "value too large"));
			      yylval->num = 0;
                            }
                          lbtt_states = yylval->num;
			  return token::LBTT;
			}

<in_HOA>{
  "States:"		return token::STATES;
  "Start:"		return token::START;
  "AP:"			return token::AP;
  "Alias:"              return token::ALIAS;
  "Acceptance:"         return token::ACCEPTANCE;
  "acc-name:"           return token::ACCNAME;
  "tool:"               return token::TOOL;
  "name:"               return token::NAME;
  "properties:"         return token::PROPERTIES;
  "--BODY--"		return token::BODY;
  "--END--"		BEGIN(INITIAL); return token::END;
  "State:"		return token::STATE;
  [tf{}()\[\]&|!]	return *yytext;

  {identifier}          {
			   yylval->str = new std::string(yytext, yyleng);
			   return token::IDENTIFIER;
			}
  {identifier}":"       {
			   yylval->str = new std::string(yytext, yyleng - 1);
			   return token::HEADERNAME;
			}
  "@"[[:alnum:]_-]+     {
			   yylval->str = new std::string(yytext + 1, yyleng - 1);
			   return token::ANAME;
			}
  [0-9]+                parse_int(); return token::INT;
}

<in_NEVER>{
  "skip"		return token::SKIP;
  "if"			return token::IF;
  "fi"			return token::FI;
  "do"			return token::DO;
  "od"			return token::OD;
  "->"			return token::ARROW;
  "goto"		return token::GOTO;
  "false"|"0"		return token::FALSE;
  "atomic"		return token::ATOMIC;
  "assert"		return token::ASSERT;

  ("!"[ \t]*)?"("	{
			  parent_level = 1;
			  BEGIN(in_NEVER_PAR);
			  yylval->str = new std::string(yytext, yyleng);
			}

  "true"|"1"		{
                          yylval->str = new std::string(yytext, yyleng);
			  return token::FORMULA;
                        }

  [a-zA-Z][a-zA-Z0-9_]* {
			  yylval->str = new std::string(yytext, yyleng);
	                  return token::IDENTIFIER;
		        }
}

  /* Note: the LBTT format is scanf friendly, but not Bison-friendly.
     If we only tokenize it as a stream of INTs, the parser will have
     a very hard time recognizing what is a state from what is a
     transitions.  As a consequence we abuse the start conditions to
     maintain a state an return integers with different sementic types
     depending on the purpose of those integers. */
<in_LBTT_HEADER>{
  [0-9]+[st]*           {
			  BEGIN(in_LBTT_STATE);
                          auto end = parse_int();
			  lbtt_s = false;
			  lbtt_t = false;
			  if (end)
			    while (int c = *end++)
			      if (c == 's')
			        lbtt_s = true;
			      else // c == 't'
			        lbtt_t = true;
  		          if (!lbtt_t)
			    lbtt_s = true;
			  if (lbtt_states == 0)
			    {
                              BEGIN(INITIAL);
                              return token::LBTT_EMPTY;
			    }
			  if (lbtt_s && !lbtt_t)
			    return token::INT_S;
			  else
			    return token::INT;
			}
}

<in_LBTT_STATE>[0-9]+   {
                           parse_int();
			   BEGIN(in_LBTT_INIT);
			   return token::STATE_NUM;
			}
<in_LBTT_INIT>[01]	{
                           yylval->num = *yytext - '0';
			   if (lbtt_s)
			      BEGIN(in_LBTT_S_ACC);
			   else
			      BEGIN(in_LBTT_TRANS);
			   return token::INT;
			}
<in_LBTT_S_ACC>{
  [0-9]+		parse_int(); return token::ACC;
  "-1"                  BEGIN(in_LBTT_TRANS); yylloc->step();
}
<in_LBTT_TRANS>{
  [0-9]+                {
			  parse_int();
			  if (lbtt_t)
			    BEGIN(in_LBTT_T_ACC);
			  else
			    BEGIN(in_LBTT_GUARD);
			  return token::DEST_NUM;
			}
  "-1"			{
                          if (--lbtt_states)
			    {
			       BEGIN(in_LBTT_STATE);
			       yylloc->step();
			    }
			  else
			    {
			       BEGIN(INITIAL);
			       return token::ENDAUT;
			    }
			}
}
<in_LBTT_T_ACC>{
  [0-9]+	        parse_int(); return token::ACC;
  "-1"			BEGIN(in_LBTT_GUARD); yylloc->step();
}
<in_LBTT_GUARD>{
  [^\n\r]*		{
  			  yylval->str = new std::string(yytext, yyleng);
			  BEGIN(in_LBTT_TRANS);
 			  return token::STRING;
			}
}


<in_COMMENT>{
  "/""*"+		++comment_level;
  [^*/\n\r]*		continue;
  "/"[^*\n\r]*		continue;
  "*"+[^*/\n\r]*	continue;
  {eol}			yylloc->lines(yyleng); yylloc->end.column = 1;
  {eol2}		yylloc->lines(yyleng / 2); yylloc->end.column = 1;
  "*"+"/"		if (--comment_level == 0) BEGIN(orig_cond);
  <<EOF>>		{
                           BEGIN(orig_cond);
                           error_list.push_back(
			     spot::hoa_parse_error(*yylloc,
			       "unclosed comment"));
			   return 0;
                        }
}

  /* matched late, so that the in_LBTT_GUARD pattern has precedence */
"\""                    {
                          orig_cond = YY_START;
			  BEGIN(in_STRING);
			  comment_level = 1;
			}

<in_STRING>{
  \"	                {
                           BEGIN(orig_cond);
			   yylval->str = new std::string(s);
			   return token::STRING;
 			}
  {eol}			{
  			  s.append(yytext, yyleng);
                          yylloc->lines(yyleng); yylloc->end.column = 1;
			}
  {eol2}		{
  			  s.append(yytext, yyleng);
                          yylloc->lines(yyleng / 2); yylloc->end.column = 1;
			}
  \\.			s += yytext[1];
  [^\\\"\n\r]+		s.append(yytext, yyleng);
  <<EOF>>		{
                           error_list.push_back(
			     spot::hoa_parse_error(*yylloc,
			       "unclosed string"));
                           BEGIN(orig_cond);
			   yylval->str = new std::string(s);
			   return token::STRING;
                        }
}

<in_NEVER_PAR>{
  "("		        {
			  ++parent_level;
			  yylval->str->append(yytext, yyleng);
			}
  /* if we match ")&&(" or ")||(", stay in <in_NEVER_PAR> mode */
  ")"[ \t]*("&&"|"||")[ \t!]*"(" {
	                  yylval->str->append(yytext, yyleng);
			}
  ")"                   {
	                  yylval->str->append(yytext, yyleng);
			  if (!--parent_level)
			    {
                              BEGIN(in_NEVER);
			      spot::trim(*yylval->str);
			      return token::FORMULA;
			    }
			}
  {eol}			{
                          yylval->str->append(yytext, yyleng);
			  yylloc->lines(yyleng); yylloc->end.column = 1;
			}
  {eol2}		{
			  yylval->str->append(yytext, yyleng);
  			  yylloc->lines(yyleng / 2); yylloc->end.column = 1;
			}
  [^()\n\r]+		yylval->str->append(yytext, yyleng);
  <<EOF>>		{
                          error_list.push_back(
			    spot::hoa_parse_error(*yylloc,
 			      "missing closing parenthese"));
                          yylval->str->append(parent_level, ')');
                          BEGIN(in_NEVER);
			  spot::trim(*yylval->str);
			  return token::FORMULA;
			}
}

.			return *yytext;

%{
  /* Dummy use of yyunput to shut up a gcc warning.  */
  (void) &yyunput;
%}

%%

namespace spot
{
  void
  hoayyreset()
  {
    BEGIN(INITIAL);
    comment_level = 0;
    parent_level = 0;
  }

  int
  hoayyopen(const std::string &name)
  {
    bool want_interactive = false;

    // yy_flex_debug = 1;
    if (name == "-")
      {
        yyin = stdin;

        // If the input is a pipe, make the scanner
        // interactive so that it does not wait for the input
        // buffer to be full to process automata.
        struct stat s;
        if (fstat(fileno(stdin), &s) < 0)
           throw std::runtime_error("fstat failed");
	if (S_ISFIFO(s.st_mode))
	  want_interactive = true;
      }
    else
      {
        yyin = fopen(name.c_str(), "r");
        if (!yyin)
	  return 1;
      }
    // Reset the lexer in case a previous parse
    // ended badly.
    YY_NEW_FILE;
    hoayyreset();
    if (want_interactive)
      yy_set_interactive(true);
    return 0;
  }

  int
  hoayyopen(int fd)
  {
    bool want_interactive = false;

    yyin = fdopen(fd, "r");

    // If the input is a pipe, make the scanner
    // interactive so that it does not wait for the input
    // buffer to be full to process automata.
    struct stat s;
    if (fstat(fd, &s) < 0)
      throw std::runtime_error("fstat failed");
    if (S_ISFIFO(s.st_mode))
      want_interactive = true;

    // Reset the lexer in case a previous parse
    // ended badly.
    YY_NEW_FILE;
    hoayyreset();
    if (want_interactive)
      yy_set_interactive(true);
    return 0;
  }

  void
  hoayyclose()
  {
    fclose(yyin);
  }
}
