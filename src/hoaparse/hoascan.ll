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

#define YY_USER_ACTION yylloc->columns(yyleng);
#define YY_NEVER_INTERACTIVE 1

typedef hoayy::parser::token token;
static unsigned comment_level = 0;

%}

eol         \n+|\r+
eol2        (\n\r)+|(\r\n)+
identifier  [[:alpha:]_][[:alnum:]_-]*

%x in_COMMENT in_STRING

%%

%{
  std::string s;
  yylloc->step();
%}


                        /* skip blanks and comments */
{eol}			yylloc->lines(yyleng); yylloc->step();
{eol2}			yylloc->lines(yyleng / 2); yylloc->step();
[ \t\v\f]+		yylloc->step();
"/""*"+			BEGIN(in_COMMENT); comment_level = 1;
"\""			BEGIN(in_STRING);

"HOA:"                  return token::HOA;
"States:"		return token::STATES;
"Start:"		return token::START;
"AP:"			return token::AP;
"Alias:"                return token::ALIAS;
"Acceptance:"           return token::ACCEPTANCE;
"acc-name:"             return token::ACCNAME;
"tool:"                 return token::TOOL;
"name:"                 return token::NAME;
"properties:"           return token::PROPERTIES;
"--BODY--"		return token::BODY;
"--ABORT--"		throw spot::hoa_abort{*yylloc};
"--END--"		return token::END;
"State:"		return token::STATE;
[tf{}()\[\]&|!]		return *yytext;

{identifier}            {
			   yylval->str = new std::string(yytext, yyleng);
			   return token::IDENTIFIER;
			}
{identifier}":"         {
			   yylval->str = new std::string(yytext, yyleng - 1);
			   return token::HEADERNAME;
			}
"@"[[:alnum:]_-]+       {
			   yylval->str = new std::string(yytext + 1, yyleng - 1);
			   return token::ANAME;
			}
[0-9]+			{
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

<in_COMMENT>{
  "/""*"+		++comment_level;
  [^*/\n]*		continue;
  "/"[^*\n]*		continue;
  "*"+[^*/\n]*		continue;
  "\n"+			yylloc->end.column = 1;	yylloc->lines(yyleng);
  "*"+"/"		if (--comment_level == 0) BEGIN(INITIAL);
  <<EOF>>		{
                           error_list.push_back(
			     spot::hoa_parse_error(*yylloc,
			       "unclosed comment"));
			   return 0;
                        }
}

<in_STRING>{
  \"	                {
                           BEGIN(INITIAL);
			   yylval->str = new std::string(s);
			   return token::STRING;
 			}
  \\\"			s += '"';
  \\.			s += yytext[1];
  [^\\\"]+		s.append(yytext, yyleng);
  <<EOF>>		{
                           error_list.push_back(
			     spot::hoa_parse_error(*yylloc,
			       "unclosed string"));
			   return 0;
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
    return 0;
  }

  void
  hoayyclose()
  {
    fclose(yyin);
  }
}
