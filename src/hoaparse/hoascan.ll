/* -*- coding: utf-8 -*-
** Copyright (C) 2014 Laboratoire de Recherche et Développement
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
#include "hoaparse/parsedecl.hh"
#include "misc/escape.hh"

#define YY_USER_ACTION yylloc->columns(yyleng);
#define YY_NEVER_INTERACTIVE 1

typedef hoayy::parser::token token;
static unsigned comment_level = 0;
static unsigned parent_level = 0;
static int orig_cond = 0;
static bool missing_parent = false;

%}

eol         \n+|\r+
eol2        (\n\r)+|(\r\n)+
identifier  [[:alpha:]_][[:alnum:]_-]*

%x in_COMMENT in_STRING in_NEVER_PAR
%s in_HOA in_NEVER

%%

%{
  std::string s;
  yylloc->step();
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
"\""                    {
                          orig_cond = YY_START;
			  BEGIN(in_STRING);
			  comment_level = 1;
			}
"HOA:"                  BEGIN(in_HOA); return token::HOA;
<INITIAL,in_HOA>"--ABORT--" BEGIN(INITIAL); throw spot::hoa_abort{*yylloc};
"never"			BEGIN(in_NEVER); return token::NEVER;

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
  [0-9]+		{
			  errno = 0;
			  unsigned long n = strtoul(yytext, 0, 10);
                          yylval->num = n;
			  if (errno || yylval->num != n)
			    {
                              error_list.push_back(
			        spot::hoa_parse_error(*yylloc,
				  "value too large"));
			      yylval->num = 0;
                            }
                          return token::INT;
			}
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


<in_COMMENT>{
  "/""*"+		++comment_level;
  [^*/\n]*		continue;
  "/"[^*\n]*		continue;
  "*"+[^*/\n]*		continue;
  "\n"+			yylloc->end.column = 1;	yylloc->lines(yyleng);
  "*"+"/"		if (--comment_level == 0) BEGIN(orig_cond);
  <<EOF>>		{
                           error_list.push_back(
			     spot::hoa_parse_error(*yylloc,
			       "unclosed comment"));
			   return 0;
                        }
}

<in_STRING>{
  \"	                {
                           BEGIN(orig_cond);
			   yylval->str = new std::string(s);
			   return token::STRING;
 			}
  \\.			s += yytext[1];
  [^\\\"]+		s.append(yytext, yyleng);
  <<EOF>>		{
                           error_list.push_back(
			     spot::hoa_parse_error(*yylloc,
			       "unclosed string"));
			   return 0;
                        }
}

<in_NEVER_PAR>{
	 "("		{
			  ++parent_level;
			  yylval->str->append(yytext, yyleng);
			}
         /* if we match ")&&(" or ")||(", stay in <in_NEVER_PAR> mode */
         ")"[ \t]*("&&"|"||")[ \t!]*"(" {
	                  yylval->str->append(yytext, yyleng);
			}
	 ")"		{
	                  yylval->str->append(yytext, yyleng);
			  if (!--parent_level)
			    {
                              BEGIN(in_NEVER);
			      spot::trim(*yylval->str);
			      return token::FORMULA;
			    }
			}
         [^()]+		yylval->str->append(yytext, yyleng);
	 <<EOF>>	{
			  unput(')');
			  if (!missing_parent)
                             error_list.push_back(
			       spot::hoa_parse_error(*yylloc,
 				"missing closing parenthese"));
				  missing_parent = true;
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
  int
  hoayyopen(const std::string &name)
  {
    // yy_flex_debug = 1;
    if (name == "-")
      {
        yyin = stdin;
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
    BEGIN(INITIAL);
    comment_level = 0;
    parent_level = 0;
    missing_parent = false;
    return 0;
  }

  void
  hoayyclose()
  {
    fclose(yyin);
  }
}
