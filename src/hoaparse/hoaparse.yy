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
%language "C++"
%locations
%defines
%expect 0 // No shift/reduce
%name-prefix "hoayy"
%debug
%error-verbose
%lex-param { spot::hoa_parse_error_list& error_list }
%define api.location.type "spot::location"

%code requires
{
#include <string>
#include <cstring>
#include <sstream>
#include <unordered_map>
#include "ltlast/constant.hh"
#include "public.hh"

  // Note: because this parser is meant to be used on a stream of
  // automata, it tries hard to recover from errors, so that we get a
  // chance to reach the end of the current automaton in order to
  // process the next one.  Several variables below are used to keep
  // track of various error conditions.
  struct result_
  {
    spot::hoa_aut_ptr h;
    spot::ltl::environment* env;
    std::vector<int> ap;
    std::vector<bdd> guards;
    std::vector<bdd>::const_iterator cur_guard;
    std::vector<bool> declared_states; // States that have been declared.
    std::unordered_map<std::string, bdd> alias;
    spot::location states_loc;
    spot::location ap_loc;
    spot::location state_label_loc;
    spot::location start_loc;
    spot::location accset_loc;
    spot::location last_loc;
    spot::acc_cond::mark_t acc_state;
    spot::acc_cond::mark_t neg_acc_sets = 0U;
    spot::acc_cond::mark_t pos_acc_sets = 0U;
    unsigned cur_state;
    int start = -1;
    int states = -1;
    int ap_count = -1;
    int accset = -1;
    bdd state_label;
    bdd cur_label;
    bool has_state_label = false;
    bool ignore_more_ap = false; // Set to true after the first "AP:"
				 // line has been read.
    bool ignore_acc = false; // Set to true in case of missing
			     // Acceptance: lines.
    bool ignore_acc_silent = false;
    bool ignore_more_acc = false; // Set to true after the first
				  // "Acceptance:" line has been read.
  };
}

%parse-param {spot::hoa_parse_error_list& error_list}
%parse-param {result_& res}
%parse-param {spot::location initial_loc}

%initial-action { @$ = initial_loc; }

%union
{
  std::string* str;
  unsigned int num;
  int b;
  spot::acc_cond::mark_t mark;
}

%code
{
#include <sstream>
/* hoaparse.hh and parsedecl.hh include each other recursively.
   We must ensure that YYSTYPE is declared (by the above %union)
   before parsedecl.hh uses it. */
#include "parsedecl.hh"

  static void fill_guards(result_& res);
}

%token HOA "HOA:"
%token STATES "States:"
%token START "Start:"
%token AP "AP:"
%token ALIAS "Alias:"
%token ACCEPTANCE "Acceptance:"
%token ACCNAME "acc-name:"
%token TOOL "tool:"
%token NAME "name:"
%token PROPERTIES "properties:"
%token BODY "--BODY--"
%token END "--END--"
%token STATE "State:";
%token <str> IDENTIFIER "identifier";
%token <str> HEADERNAME "header name";
%token <str> ANAME "alias name";
%token <str> STRING "string";
%token <num> INT "integer";
%token ENDOFFILE 0 "end of file"

%left '|'
%left '&'
%nonassoc '!'

%type <num> state-num acc-set
%type <b> label-expr
%type <mark> acc-sig_opt acc-sets

%destructor { delete $$; } <str>
%destructor { bdd_delref($$); } <b>
%printer {
    if ($$)
      debug_stream() << *$$;
    else
      debug_stream() << "\"\""; } <str>
%printer { debug_stream() << $$; } <num>

%%
hoa: header "--BODY--" body "--END--"
     {
       res.last_loc = @$;
       YYACCEPT;
     }
hoa: ENDOFFILE { YYABORT; }

string_opt: | STRING
BOOLEAN: 't' | 'f'

header: format-version header-items
        {
	  if (res.accset < 0)
	    {
	      error(@$, "missing 'Acceptance:' header");
	      res.ignore_acc = true;
	    }
	}

format-version: "HOA:" IDENTIFIER
		{
		  if (*$2 != "v1")
		    error(@$, "unsupported version of the HOA format");
		  delete $2;
		}

header-items: | header-items header-item
header-item: "States:" INT
           {
	     if (res.states >= 0)
	       {
		 error(@$, "redefinition of the number of states...");
		 error(res.states_loc, "... previously defined here.");
	       }
	     else
	       {
		 res.states_loc = @$;
	       }
	     if (((int) $2) < 0)
	       {
		 error(@$, "too many states for this implementation");
		 YYABORT;
	       }
	     res.states = std::max(res.states, (int) $2);
	     if (res.states <= res.start)
	       {
		 error(res.start_loc,
		       "initial state number is larger than state count...");
		 error(@$, "... declared here.");
	       }
	     int missing = std::max(res.states, res.start + 1)
	       - res.h->aut->num_states();
	     assert(missing >= 0);
	     res.h->aut->new_states(missing);
	     res.declared_states.resize(res.declared_states.size() + missing);
	   }
           | "Start:" state-conj-2
	     {
	       res.start_loc = @$;
	       error(@2, "alternation is not yet supported");
	       YYABORT;
	     }
           | "Start:" state-num
	     {
	       if (res.start >= 0)
		 {
		   error(@$, "multiple initial states are not yet supported");
		   YYABORT;
		 }
	       res.start = $2;
	       res.start_loc = @$;
	     }
           | "AP:" INT {
	                 if (res.ignore_more_ap)
			   {
			     error(@1, "ignoring this redeclaration of APs...");
			     error(res.ap_loc, "... previously declared here.");
			   }
			 else
			   {
			     res.ap_count = $2;
			     res.ap.reserve($2);
			   }
	               }
                   ap-names
	     {
	       if (!res.ignore_more_ap)
		 {
		   res.ap_loc = @1 + @2;
		   if ((int) res.ap.size() != res.ap_count)
		     {
		       std::ostringstream out;
		       out << "found " << res.ap.size()
			   << " atomic propositions instead of the "
			   << res.ap_count << " announced";
		       error(@$, out.str());
		     }
		   res.ignore_more_ap = true;
		 }
	     }
           | "Alias:" ANAME label-expr
             {
	       if (!res.alias.emplace(*$2, bdd_from_int($3)).second)
		 {
		   std::ostringstream o;
		   o << "ignoring redefinition of alias @" << *$2;
		   error(@$, o.str());
		 }
	       delete $2;
	       bdd_delref($3);
	     }
           | "Acceptance:" INT
	      {
		if (res.ignore_more_acc)
		  {
		    error(@1 + @2, "ignoring this redefinition of the "
			  "acceptance condition...");
		    error(res.accset_loc, "... previously defined here.");
		  }
		else if ($2 > 8 * sizeof(spot::acc_cond::mark_t::value_t))
		  {
		    error(@1 + @2,
			  "this implementation cannot support such a large "
			  "number of acceptance sets");
		    YYABORT;
		  }
		else
		  {
		    res.h->aut->acc().add_sets($2);
		    res.accset = $2;
		    res.accset_loc = @1 + @2;
		  }
	     }
             acceptance-cond
	     {
	       res.ignore_more_acc = true;
	     }
           | "acc-name:" IDENTIFIER acc-spec
             {
	       delete $2;
	     }
           | "tool:" STRING string_opt
             {
	       delete $2;
	     }
           | "name:" STRING
             {
	       delete $2;
	     }
           | "properties:" properties
           | HEADERNAME header-spec

ap-names: | ap-names ap-name
ap-name: STRING
	 {
	   if (!res.ignore_more_ap)
	     {
	       auto f = res.env->require(*$1);
	       if (f == nullptr)
		 {
		   std::ostringstream out;
		   out << "unknown atomic proposition \"" << *$1 << "\"";
		   delete $1;
		   error(@1, out.str());
		   f = spot::ltl::default_environment::instance()
		     .require("$unknown$");
		 }
	       auto b =
		 res.h->aut->get_dict()->register_proposition(f, res.h->aut);
	       f->destroy();
	       res.ap.push_back(b);
	     }
	   delete $1;
	 }

acc-spec: | acc-spec BOOLEAN
	  | acc-spec INT
	  | acc-spec IDENTIFIER
            {
	      delete $2;
	    }
properties: | properties IDENTIFIER
	      {
		delete $2;
	      }
header-spec: | header-spec BOOLEAN
             | header-spec INT
             | header-spec STRING
	       {
		 delete $2;
	       }
             | header-spec IDENTIFIER
	       {
		 delete $2;
	       }

state-conj-2: state-num '&' state-num | state-conj-2 '&' state-num

label-expr: 't'
	    {
	      $$ = bddtrue.id();
	    }
          | 'f'
	    {
	      $$ = bddfalse.id();
	    }
	  | INT
	    {
	      if ($1 >= res.ap.size())
		{
		  error(@1, "AP number is larger than the number of APs...");
		  error(res.ap_loc, "... declared here");
		  $$ = bddtrue.id();
		}
	      else
		{
		  $$ = bdd_ithvar(res.ap[$1]).id();
		  bdd_addref($$);
		}
	    }
          | ANAME
	    {
	      auto i = res.alias.find(*$1);
	      if (i == res.alias.end())
		{
		  error(@$, "unknown alias @" + *$1);
		  $$ = 1;
		}
	      else
		{
		  $$ = i->second.id();
		  bdd_addref($$);
		}
	      delete $1;
	    }
          | '!' label-expr
	    {
              $$ = bdd_not($2);
              bdd_delref($2);
              bdd_addref($$);
            }
          | label-expr '&' label-expr
	    {
              $$ = bdd_and($1, $3);
              bdd_delref($1);
              bdd_delref($3);
              bdd_addref($$);
            }
          | label-expr '|' label-expr
	    {
              $$ = bdd_or($1, $3);
              bdd_delref($1);
              bdd_delref($3);
              bdd_addref($$);
            }


acc-set: INT
            {
	      if ((int) $1 >= res.accset)
		{
		  if (!res.ignore_acc)
		    {
		      error(@1, "number is larger than the count "
			    "of acceptance sets...");
		      error(res.accset_loc, "... declared here.");
		    }
		  $$ = -1U;
		}
	      else
		{
		  $$ = $1;
		}
	    }

acceptance-cond: IDENTIFIER '(' acc-set ')'
		 {
		   if (!res.ignore_more_acc && *$1 != "Inf")
		     error(@1, "this implementation only supports "
			   "'Inf' acceptance");
		   if ($3 != -1U)
		     res.pos_acc_sets |= res.h->aut->acc().mark($3);
		   delete $1;
		 }
               | IDENTIFIER '(' '!' acc-set ')'
		 {
		   if (!res.ignore_more_acc && *$1 != "Inf")
		     error(@1, "this implementation only supports "
			   "'Inf' acceptance");
		   if ($4 != -1U)
		     res.neg_acc_sets |= res.h->aut->acc().mark($4);
		   delete $1;
		 }
               | '(' acceptance-cond ')'
               | acceptance-cond '&' acceptance-cond
               | acceptance-cond '|' acceptance-cond
	         {
		   if (!res.ignore_more_acc)
		     error(@2, "this implementation does not support "
			   "disjunction in acceptance conditions");
		 }
               | 't'
	       | 'f'
	       {
		 if (!res.ignore_more_acc)
		   error(@$, "this implementation does not support "
			 "false acceptance");
	       }


body: states

state-num: INT
	   {
	     if (((int) $1) < 0)
	       {
		 error(@1, "state number is too large for this implementation");
		 YYABORT;
	       }
	     if ((int) $1 >= res.states)
	       {
		 if (res.states >= 0)
		   {
		     error(@1, "state number is larger than state count...");
		     error(res.states_loc, "... declared here.");
		   }
		 int missing = ((int) $1) - res.h->aut->num_states() + 1;
		 if (missing >= 0)
		   {
		     res.h->aut->new_states(missing);
		     res.declared_states.resize(res.declared_states.size()
						+ missing);
		   }
	       }
	     $$ = $1;
	   }

states: | states state
state: state-name labeled-edges
     | state-name unlabeled-edges
       {
	 if (!res.has_state_label)
	   {
	     if (res.cur_guard != res.guards.end())
	       error(@$, "not enough transitions for this state");
	     res.cur_guard = res.guards.begin();
	   }
       }
state-name: "State:" state-label_opt state-num string_opt acc-sig_opt
	  {
	    res.cur_state = $3;
	    if (res.declared_states[$3])
	      {
		std::ostringstream o;
		o << "redeclaration of state " << $3;
		error(@1 + @3, o.str());
	      }
	    res.declared_states[$3] = true;
	    res.acc_state = $5;
	  }
label: '[' label-expr ']'
	   {
             res.cur_label = bdd_from_int($2);
             bdd_delref($2);
	   }
state-label_opt:       { res.has_state_label = false; }
               | label { res.has_state_label = true;
                         res.state_label_loc = @1;
		         res.state_label = res.cur_label; }
trans-label: label
	         {
		   if (res.has_state_label)
		     {
		       error(@1, "cannot label this transition because...");
		       error(res.state_label_loc,
			     "... the state is already labeled.");
		       res.cur_label = res.state_label;
		     }
		 }

acc-sig_opt:
             {
               $$ = spot::acc_cond::mark_t(0U);
             }
           | '{' acc-sets '}'
	     {
	       $$ = $2;
	       if (res.ignore_acc && !res.ignore_acc_silent)
		 {
		   error(@$, "ignoring acceptance sets because of "
			 "missing acceptance condition");
		   // Emit this message only once.
		   res.ignore_acc_silent = true;
		 }
	     }
acc-sets:
          {
	    $$ = spot::acc_cond::mark_t(0U);
	  }
        | acc-sets acc-set
	  {
	    if (res.ignore_acc || $2 == -1U)
	      $$ = spot::acc_cond::mark_t(0U);
	    else
	      $$ = $1 | res.h->aut->acc().mark($2);
	  }
labeled-edges: | labeled-edges labeled-edge
labeled-edge: trans-label state-num acc-sig_opt
	      {
		res.h->aut->new_transition(res.cur_state, $2,
					   res.cur_label, $3 | res.acc_state);
	      }
	    | trans-label state-conj-2 acc-sig_opt
	      {
		error(@2, "alternation is not yet supported");
		YYABORT;
	      }

/* We never have zero unlabeled edges, these are considered as zero
   labeled edges. */
unlabeled-edges: unlabeled-edge | unlabeled-edges unlabeled-edge
unlabeled-edge: state-num acc-sig_opt
		{
		  bdd cond;
		  if (res.has_state_label)
		    {
		      cond = res.state_label;
		    }
		  else
		    {
		      if (res.guards.empty())
			fill_guards(res);
		      if (res.cur_guard == res.guards.end())
			{
			  error(@$, "too many transition for this state, "
				"ignoring this one");
			  cond = bddfalse;
			}
		      else
			{
			  cond = *res.cur_guard++;
			}
		    }
		  res.h->aut->new_transition(res.cur_state, $1,
					     cond, $2 | res.acc_state);
		}
	      | state-conj-2 acc-sig_opt
		{
		  error(@1, "alternation is not yet supported");
		  YYABORT;
		}

%%

static void fill_guards(result_& r)
{
  spot::bdd_dict_ptr d = r.h->aut->get_dict();
  unsigned nap = r.ap.size();

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
hoayy::parser::error(const location_type& location,
		       const std::string& message)
{
  error_list.emplace_back(location, message);
}

static void fix_acceptance(result_& r)
{
  // If a set x appears only as Inf(!x), we can complement it so that
  // we work with Inf(x) instead.
  auto onlyneg = r.neg_acc_sets - r.pos_acc_sets;
  for (auto& t: r.h->aut->transitions())
    t.acc ^= onlyneg;

  // However if set x is used elsewhere, for instance in
  //   Inf(!x) & Inf(x)
  // complementing x would be wrong.  We need to create a
  // new set, y, that is the complement of x, and rewrite
  // this as Inf(y) & Inf(x).
  auto both = r.neg_acc_sets & r.pos_acc_sets;
  if (both)
    {
      auto& acc = r.h->aut->acc();
      auto v = acc.sets(both);
      auto vs = v.size();
      unsigned base = acc.add_sets(vs);
      for (auto& t: r.h->aut->transitions())
	if ((t.acc & both) != both)
	  for (unsigned i = 0; i < vs; ++i)
	    if (!t.acc.has(i))
	      t.acc |= acc.mark(base + i);
    }
}

namespace spot
{
  hoa_stream_parser::hoa_stream_parser(const std::string& name)
  {
    if (hoayyopen(name))
      throw std::runtime_error(std::string("Cannot open file ") + name);
  }

  hoa_stream_parser::~hoa_stream_parser()
  {
    hoayyclose();
  }


  hoa_aut_ptr
  hoa_stream_parser::parse(hoa_parse_error_list& error_list,
			   const bdd_dict_ptr& dict,
			   ltl::environment& env,
			   bool debug)
  {
    result_ r;
    r.h = std::make_shared<spot::hoa_aut>();
    r.h->aut = make_tgba_digraph(dict);
    r.env = &env;
    hoayy::parser parser(error_list, r, last_loc);
    parser.set_debug_level(debug);
    if (parser.parse())
      r.h->aut = nullptr;
    last_loc = r.last_loc;
    if (!r.h->aut)
      return nullptr;
    if (r.neg_acc_sets)
      fix_acceptance(r);
    if (r.start != -1)
      {
	r.h->aut->set_init_state(r.start);
      }
    else
      {
	// If no initial state has been declared, add one, because
	// Spot will not work without one.
	r.h->aut->set_init_state(r.h->aut->new_state());
      }
    return r.h;
  };
}

// Local Variables:
// mode: c++
// End:
