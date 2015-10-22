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
%language "C++"
%locations
%defines
%expect 0 // No shift/reduce
%name-prefix "hoayy"
%debug
%error-verbose
%lex-param { spot::parse_aut_error_list& error_list }
%define api.location.type "spot::location"

%code requires
{
#include "config.h"
#include "misc/common.hh"
#include <string>
#include <cstring>
#include <sstream>
#include <unordered_map>
#include <algorithm>
#include "twa/formula2bdd.hh"
#include "public.hh"
#include "priv/accmap.hh"
#include "tl/parse.hh"

#ifndef HAVE_STRVERSCMP
// If the libc does not have this, a version is compiled in lib/.
extern "C" int strverscmp(const char *s1, const char *s2);
#endif

  inline namespace hoayy_support
  {
    typedef std::map<int, bdd> map_t;

    /* Cache parsed formulae.  Labels on arcs are frequently identical
       and it would be a waste of time to parse them to formula
       over and over, and to register all their atomic_propositions in
       the bdd_dict.  Keep the bdd result around so we can reuse
       it.  */
    typedef std::map<std::string, bdd> formula_cache;

    typedef std::pair<int, std::string*> pair;
    typedef spot::twa_graph::namer<std::string> named_tgba_t;

    // Note: because this parser is meant to be used on a stream of
    // automata, it tries hard to recover from errors, so that we get a
    // chance to reach the end of the current automaton in order to
    // process the next one.  Several variables below are used to keep
    // track of various error conditions.
    enum label_style_t { Mixed_Labels, State_Labels, Trans_Labels,
			 Implicit_Labels };
    enum acc_style_t { Mixed_Acc, State_Acc, Trans_Acc };

    struct result_
    {
      struct state_info
      {
	bool declared = false;
	bool used = false;
	spot::location used_loc;
      };
      spot::parsed_aut_ptr h;
      std::string format_version;
      spot::location format_version_loc;
      spot::environment* env;
      formula_cache fcache;
      named_tgba_t* namer = nullptr;
      spot::acc_mapper_int* acc_mapper = nullptr;
      std::vector<int> ap;
      std::vector<bdd> guards;
      std::vector<bdd>::const_iterator cur_guard;
      map_t dest_map;
      std::vector<state_info> info_states; // States declared and used.
      std::vector<std::pair<spot::location, unsigned>> start; // Initial states;
      std::unordered_map<std::string, bdd> alias;
      std::unordered_map<std::string, spot::location> props;
      spot::location states_loc;
      spot::location ap_loc;
      spot::location state_label_loc;
      spot::location accset_loc;
      spot::acc_cond::mark_t acc_state;
      spot::acc_cond::mark_t neg_acc_sets = 0U;
      spot::acc_cond::mark_t pos_acc_sets = 0U;
      int plus;
      int minus;
      std::vector<std::string>* state_names = nullptr;
      std::map<unsigned, unsigned> states_map;
      std::set<int> ap_set;
      unsigned cur_state;
      int states = -1;
      int ap_count = -1;
      int accset = -1;
      bdd state_label;
      bdd cur_label;
      bool has_state_label = false;
      bool ignore_more_ap = false; // Set to true after the first "AP:"
      // line has been read.
      bool ignore_acc = false;	// Set to true in case of missing
				// Acceptance: lines.
      bool ignore_acc_silent = false;
      bool ignore_more_acc = false; // Set to true after the first
				// "Acceptance:" line has been read.

      label_style_t label_style = Mixed_Labels;
      acc_style_t acc_style = Mixed_Acc;

      bool accept_all_needed = false;
      bool accept_all_seen = false;
      bool aliased_states = false;

      bool deterministic = false;
      bool complete = false;
      bool trans_acc_seen = false;

      std::map<std::string, spot::location> labels;

      ~result_()
      {
	delete namer;
	delete acc_mapper;
      }
    };
  }
}

%parse-param {spot::parse_aut_error_list& error_list}
%parse-param {result_& res}
%parse-param {spot::location initial_loc}

%initial-action { @$ = res.h->loc = initial_loc; }

%union
{
  std::string* str;
  unsigned int num;
  int b;
  spot::acc_cond::mark_t mark;
  pair* p;
  std::list<pair>* list;
  spot::acc_cond::acc_code* code;
}

%code
{
#include <sstream>

  /* parseaut.hh and parsedecl.hh include each other recursively.
   We must ensure that YYSTYPE is declared (by the above %union)
   before parsedecl.hh uses it. */
#include "parsedecl.hh"

  static void fill_guards(result_& res);
}

/**** HOA tokens ****/
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
%token <str> IDENTIFIER "identifier";  // also used by neverclaim
%token <str> HEADERNAME "header name";
%token <str> ANAME "alias name";
%token <str> STRING "string";
%token <num> INT "integer";
%token ENDOFFILE 0 "end of file"

%token DRA "DRA"
%token DSA "DSA"
%token V2 "v2"
%token EXPLICIT "explicit"
%token ACCPAIRS "Acceptance-Pairs:"
%token ACCSIG "Acc-Sig:";
%token ENDOFHEADER "---";


%left '|'
%left '&'
%nonassoc '!'

%type <num> checked-state-num state-num acc-set sign
%type <b> label-expr
%type <mark> acc-sig acc-sets trans-acc_opt state-acc_opt
             dstar_accsigs dstar_state_accsig
%type <str> string_opt

/**** NEVERCLAIM tokens ****/

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

%type <b> nc-formula
%type <str> nc-opt-dest nc-formula-or-ident
%type <p> nc-transition nc-src-dest
%type <list> nc-transitions nc-transition-block
%type <str> nc-one-ident nc-ident-list
%type <code> acceptance-cond

/**** LBTT tokens *****/
 // Also using INT, STRING
%token ENDAUT "-1"
%token ENDDSTAR "end of DSTAR automaton"
%token <num> LBTT "LBTT header"
%token <num> INT_S "state acceptance"
%token <num> LBTT_EMPTY "acceptance sets for empty automaton"
%token <num> ACC "acceptance set"
%token <num> STATE_NUM "state number"
%token <num> DEST_NUM "destination number"
%type <mark> lbtt-acc

%destructor { delete $$; } <str>
%destructor { bdd_delref($$); } <b>
%destructor { bdd_delref($$->first); delete $$->second; delete $$; } <p>
%destructor { delete $$; } <code>
%destructor {
  for (std::list<pair>::iterator i = $$->begin();
       i != $$->end(); ++i)
  {
    bdd_delref(i->first);
    delete i->second;
  }
  delete $$;
  } <list>
%printer {
    if ($$)
      debug_stream() << *$$;
    else
      debug_stream() << "\"\""; } <str>
%printer { debug_stream() << $$; } <num>

%%
aut: aut-1     { res.h->loc = @$; YYACCEPT; }
   | ENDOFFILE { YYABORT; }
   | error ENDOFFILE { YYABORT; }
   | error aut-1
     {
       error(@1, "leading garbage was ignored");
       res.h->loc = @2;
       YYACCEPT;
     }

aut-1: hoa   { res.h->type = spot::parsed_aut_type::HOA; }
     | never { res.h->type = spot::parsed_aut_type::NeverClaim; }
     | lbtt  { res.h->type = spot::parsed_aut_type::LBTT; }
     | dstar /* will set type as DSA or DRA while parsing first line */

/**********************************************************************/
/*                          Rules for HOA                             */
/**********************************************************************/

hoa: header "--BODY--" body "--END--"
   | "HOA:" error "--END--"

string_opt: { $$ = nullptr; }
          | STRING { $$ = $1; }
BOOLEAN: 't' | 'f'

header: format-version header-items
        {
	  // Preallocate the states if we know their number.
	  if (res.states >= 0)
	    {
	      unsigned states = res.states;
	      for (auto& p : res.start)
		if ((unsigned) res.states <= p.second)
		  {
		    error(p.first,
			  "initial state number is larger than state count...");
		    error(res.states_loc, "... declared here.");
		    states = std::max(states, p.second + 1);
		  }
	      res.h->aut->new_states(states);
	      res.info_states.resize(states);
	    }
	  if (res.accset < 0)
	    {
	      error(@$, "missing 'Acceptance:' header");
	      res.ignore_acc = true;
	    }
	  // Process properties.
	  {
	    auto explicit_labels = res.props.find("explicit-labels");
	    auto implicit_labels = res.props.find("implicit-labels");
	    if (implicit_labels != res.props.end())
	      {
		if (explicit_labels == res.props.end())
		  {
		    res.label_style = Implicit_Labels;
		  }
		else
		  {
		    error(implicit_labels->second,
			  "'property: implicit-labels' is incompatible "
			  "with...");
		    error(explicit_labels->second,
			  "... 'property: explicit-labels'.");
		  }
	      }

	    auto trans_labels = res.props.find("trans-labels");
	    auto state_labels = res.props.find("state-labels");
	    if (trans_labels != res.props.end())
	      {
		if (state_labels == res.props.end())
		  {
		    if (res.label_style != Implicit_Labels)
		      res.label_style = Trans_Labels;
		  }
		else
		  {
		    error(trans_labels->second,
			  "'property: trans-labels' is incompatible with...");
		    error(state_labels->second,
			  "... 'property: state-labels'.");
		  }
	      }
	    else if (state_labels != res.props.end())
	      {
		if (res.label_style != Implicit_Labels)
		  {
		    res.label_style = State_Labels;
		  }
		else
		  {
		    error(state_labels->second,
			  "'property: state-labels' is incompatible with...");
		    error(implicit_labels->second,
			  "... 'property: implicit-labels'.");
		  }
	      }

	    auto state_acc = res.props.find("state-acc");
	    auto trans_acc = res.props.find("trans-acc");
	    if (trans_acc != res.props.end())
	      {
		if (state_acc == res.props.end())
		  {
		    res.acc_style = Trans_Acc;
		  }
		else
		  {
		    error(trans_acc->second,
			  "'property: trans-acc' is incompatible with...");
		    error(state_acc->second,
			  "... 'property: state-acc'.");
		  }
	      }
	    else if (state_acc != res.props.end())
	      {
		res.acc_style = State_Acc;
	      }
	  }
	  {
	    unsigned ss = res.start.size();
	    if (ss > 1)
	      {
		auto det = res.props.find("deterministic");
		if (det != res.props.end())
		  {
		    error(det->second,
			  "deterministic automata should have at most "
			  "one initial state");
		  }
		res.deterministic = false;
	      }
	    else
	      {
		// Assume the automaton is deterministic until proven
		// wrong.
		res.deterministic = true;
	      }
	    if (ss < 1)
	      {
		auto complete = res.props.find("complete");
		if (complete != res.props.end())
		  {
		    error(complete->second,
			  "complete automata should have at least "
			  "one initial state");
		  }
		res.complete = false;
	      }
	    else
	      {
		// Assume the automaton is complete until proven
		// wrong.
		res.complete = true;
	      }
	  }
	}

version: IDENTIFIER
         {
	   res.format_version = *$1;
	   res.format_version_loc = @1;
	   delete $1;
	 }

format-version: "HOA:" { res.h->loc = @1; } version

aps: "AP:" INT {
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
	   }
           | "Start:" init-state-conj-2
	     {
	       error(@2, "alternation is not yet supported");
	       YYABORT;
	     }
           | "Start:" state-num
	     {
	       res.start.emplace_back(@$, $2);
	     }
           | aps
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
	       res.h->aut->set_acceptance($2, *$4);
	       delete $4;
	     }
           | "acc-name:" IDENTIFIER acc-spec
             {
	       delete $2;
	     }
           | "tool:" STRING string_opt
             {
	       delete $2;
	       delete $3;
	     }
           | "name:" STRING
             {
	       res.h->aut->set_named_prop("automaton-name", $2);
	     }
           | "properties:" properties
           | HEADERNAME header-spec
	     {
	       char c = (*$1)[0];
	       if (c >= 'A' && c <= 'Z')
		 error(@$, "ignoring unsupported header \"" + *$1 + ":\"\n\t"
		       "(but the capital indicates information that should not"
		       " be ignored)");
	       delete $1;
	     }
           | error

ap-names: | ap-names ap-name
ap-name: STRING
	 {
	   if (!res.ignore_more_ap)
	     {
	       auto f = res.env->require(*$1);
	       int b = 0;
	       if (f == nullptr)
		 {
		   std::ostringstream out;
		   out << "unknown atomic proposition \"" << *$1 << "\"";
		   error(@1, out.str());
		   b = res.h->aut->register_ap("$unknown$");
		 }
	       else
		 {
		   b = res.h->aut->register_ap(f);
		   if (!res.ap_set.emplace(b).second)
		     {
		       std::ostringstream out;
		       out << "duplicate atomic proposition \"" << *$1 << "\"";
		       error(@1, out.str());
		     }
		 }
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
		res.props.emplace(*$2, @2);
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

state-conj-2: checked-state-num '&' checked-state-num
            | state-conj-2 '&' checked-state-num

	      // Currently we do not check the number of these states
	      // since we do not support alternation.
init-state-conj-2: state-num '&' state-num
            | init-state-conj-2 '&' state-num

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
          | '(' label-expr ')'
	  {
	    $$ = $2;
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
		   if ($3 != -1U)
		     {
		       res.pos_acc_sets |= res.h->aut->acc().mark($3);
		       if (*$1 == "Inf")
			 $$ = new spot::acc_cond::acc_code
			   (res.h->aut->acc().inf({$3}));
		       else
			 $$ = new spot::acc_cond::acc_code
			   (res.h->aut->acc().fin({$3}));
		     }
		   else
		     {
		       $$ = new spot::acc_cond::acc_code;
		     }
		   delete $1;
		 }
               | IDENTIFIER '(' '!' acc-set ')'
		 {
		   if ($4 != -1U)
		     {
		       res.neg_acc_sets |= res.h->aut->acc().mark($4);
		       if (*$1 == "Inf")
			 $$ = new spot::acc_cond::acc_code
			   (res.h->aut->acc().inf_neg({$4}));
		       else
			 $$ = new spot::acc_cond::acc_code
			   (res.h->aut->acc().fin_neg({$4}));
		     }
		   else
		     {
		       $$ = new spot::acc_cond::acc_code;
		     }
		   delete $1;
		 }
               | '(' acceptance-cond ')'
	         {
		   $$ = $2;
		 }
               | acceptance-cond '&' acceptance-cond
	         {
		   $3->append_and(std::move(*$1));
		   $$ = $3;
		   delete $1;
		 }
               | acceptance-cond '|' acceptance-cond
	         {
		   $3->append_or(std::move(*$1));
		   $$ = $3;
		   delete $1;
		 }
               | 't'
	         {
		   $$ = new spot::acc_cond::acc_code;
		 }
	       | 'f'
	       {
	         {
		   $$ = new spot::acc_cond::acc_code(res.h->aut->acc().fin({}));
		 }
	       }


body: states
      {
	for (auto& p: res.start)
	  if (p.second >= res.info_states.size()
	      || !res.info_states[p.second].declared)
	    {
	      error(p.first,
		    "initial state " + std::to_string(p.second) +
		    " has no definition");
	      // Pretend that the state is declared so we do not
	      // mention it in the next loop.
	      if (p.second < res.info_states.size())
		res.info_states[p.second].declared = true;
	    }
	unsigned n = res.info_states.size();
	// States with number above res.states have already caused a
	// diagnostic, so let not add another one.
	if (res.states >= 0)
	  n = res.states;
	for (unsigned i = 0; i < n; ++i)
	  {
	    auto& p = res.info_states[i];
	    if (p.used && !p.declared)
	      error(p.used_loc,
		    "state " + std::to_string(i) + " has no definition");
	  }
      }

state-num: INT
	   {
	     if (((int) $1) < 0)
	       {
		 error(@1, "state number is too large for this implementation");
		 YYABORT;
	       }
	     $$ = $1;
	   }

checked-state-num: state-num
		   {
		     if ((int) $1 >= res.states)
		       {
			 if (res.states >= 0)
			   {
			     error(@1, "state number is larger than state "
				   "count...");
			     error(res.states_loc, "... declared here.");
			   }
			 int missing =
			   ((int) $1) - res.h->aut->num_states() + 1;
			 if (missing >= 0)
			   {
			     res.h->aut->new_states(missing);
			     res.info_states.resize
			       (res.info_states.size() + missing);
			   }
		       }
		     // Remember the first place were a state is the
		     // destination of a transition.
		     if (!res.info_states[$1].used)
		       {
			 res.info_states[$1].used = true;
			 res.info_states[$1].used_loc = @1;
		       }
		     $$ = $1;
		   }

states: | states state
        {
	  if (res.deterministic || res.complete)
	    {
	      bdd available = bddtrue;
	      bool det = true;
	      for (auto& t: res.h->aut->out(res.cur_state))
		{
		  if (det && !bdd_implies(t.cond, available))
		    det = false;
		  available -= t.cond;
		}
	      if (res.deterministic && !det)
		{
		  res.deterministic = false;
		  auto p = res.props.find("deterministic");
		  if (p != res.props.end())
		    {
		      error(@2, "automaton is not deterministic...");
		      error(p->second, "... despite 'property: deterministic'");
		    }
		}
	      if (res.complete && available != bddfalse)
		{
		  res.complete = false;
		  auto p = res.props.find("complete");
		  if (p != res.props.end())
		    {
		      error(@2, "automaton is not complete...");
		      error(p->second, "... despite 'property: complete'");
		    }
		}
	    }
	}
state: state-name labeled-edges
     | state-name unlabeled-edges
       {
	 if (!res.has_state_label) // Implicit labels
	   {
	     if (res.cur_guard != res.guards.end())
	       error(@$, "not enough transitions for this state");

	     if (res.label_style == State_Labels)
	       {
		 error(@2, "these transitions have implicit labels but the"
		       " automaton is...");
		 error(res.props["state-labels"], "... declared with "
		       "'property: state-labels'");
		 // Do not repeat this message.
		 res.label_style = Mixed_Labels;
	       }

	     res.cur_guard = res.guards.begin();
	   }
       }
     | error
       {
	 // Assume the worse.
	 res.deterministic = false;
	 res.complete = false;
       }


state-name: "State:" state-label_opt checked-state-num string_opt state-acc_opt
	  {
	    res.cur_state = $3;
	    if (res.info_states[$3].declared)
	      {
		std::ostringstream o;
		o << "redeclaration of state " << $3;
		error(@1 + @3, o.str());
	      }
	    res.info_states[$3].declared = true;
	    res.acc_state = $5;
	    if ($4)
	      {
		if (!res.state_names)
		  res.state_names =
		    new std::vector<std::string>(res.states > 0 ?
						 res.states : 0);
		if (res.state_names->size() < $3 + 1)
		  res.state_names->resize($3 + 1);
		(*res.state_names)[$3] = std::move(*$4);
		delete $4;
	      }
	  }
label: '[' label-expr ']'
	   {
             res.cur_label = bdd_from_int($2);
             bdd_delref($2);
	   }
     | '[' error ']'
           {
	     error(@$, "ignoring this invalid label");
	     res.cur_label = bddtrue;
	   }
state-label_opt:       { res.has_state_label = false; }
               | label
	       {
		 res.has_state_label = true;
		 res.state_label_loc = @1;
		 res.state_label = res.cur_label;
		 if (res.label_style == Trans_Labels
		     || res.label_style == Implicit_Labels)
		   {
		     error(@$,
			   "state label used although the automaton was...");
		     if (res.label_style == Trans_Labels)
		       error(res.props["trans-labels"],
			     "... declared with 'property: trans-labels' here");
		     else
		       error(res.props["implicit-labels"],
			     "... declared with 'property: implicit-labels' "
			     "here");
		     // Do not show this error anymore.
		     res.label_style = Mixed_Labels;
		   }
	       }
trans-label: label
	         {
		   if (res.has_state_label)
		     {
		       error(@1, "cannot label this edge because...");
		       error(res.state_label_loc,
			     "... the state is already labeled.");
		       res.cur_label = res.state_label;
		     }
		   if (res.label_style == State_Labels
		       || res.label_style == Implicit_Labels)
		     {
		       error(@$, "transition label used although the "
			     "automaton was...");
		       if (res.label_style == State_Labels)
			 error(res.props["state-labels"],
			       "... declared with 'property: state-labels' "
			       "here");
		       else
			 error(res.props["implicit-labels"],
			       "... declared with 'property: implicit-labels' "
			       "here");
		       // Do not show this error anymore.
		       res.label_style = Mixed_Labels;
		     }
		 }

acc-sig: '{' acc-sets '}'
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
           | '{' error '}'
	     {
	       error(@$, "ignoring this invalid acceptance set");
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

state-acc_opt:
               {
                 $$ = spot::acc_cond::mark_t(0U);
               }
             | acc-sig
               {
		 $$ = $1;
		 if (res.acc_style == Trans_Acc)
		   {
		     error(@$, "state-based acceptance used despite...");
		     error(res.props["trans-acc"],
			   "... declaration of transition-based acceptance.");
		     res.acc_style = Mixed_Acc;
		   }
	       }
trans-acc_opt:
               {
                 $$ = spot::acc_cond::mark_t(0U);
               }
             | acc-sig
               {
		 $$ = $1;
		 res.trans_acc_seen = true;
		 if (res.acc_style == State_Acc)
		   {
		     error(@$, "trans-based acceptance used despite...");
		     error(res.props["state-acc"],
			   "... declaration of state-based acceptance.");
		     res.acc_style = Mixed_Acc;
		   }
	       }

/* block of labeled-edges, with occasional (incorrect) unlabeled edge */
labeled-edges: | some-labeled-edges
some-labeled-edges: labeled-edge
                  | some-labeled-edges labeled-edge
                  | some-labeled-edges incorrectly-unlabeled-edge
incorrectly-unlabeled-edge: checked-state-num trans-acc_opt
                            {
			      bdd cond = bddtrue;
			      if (!res.has_state_label)
				error(@$, "missing label for this edge "
				      "(previous edge is labeled)");
			      else
				cond = res.state_label;
			      res.h->aut->new_edge(res.cur_state, $1,
						   cond, $2 | res.acc_state);
			    }
labeled-edge: trans-label checked-state-num trans-acc_opt
	      {
		if (res.cur_label != bddfalse)
		  res.h->aut->new_edge(res.cur_state, $2,
				       res.cur_label, $3 | res.acc_state);
	      }
	    | trans-label state-conj-2 trans-acc_opt
	      {
		error(@2, "alternation is not yet supported");
		YYABORT;
	      }

/* Block of unlabeled edge, with occasional (incorrect) labeled
   edge. We never have zero unlabeled edges, these are considered as
   zero labeled edges. */
unlabeled-edges: unlabeled-edge
               | unlabeled-edges unlabeled-edge
               | unlabeled-edges incorrectly-labeled-edge
unlabeled-edge: checked-state-num trans-acc_opt
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
			  error(@$, "too many transitions for this state, "
				"ignoring this one");
			  cond = bddfalse;
			}
		      else
			{
			  cond = *res.cur_guard++;
			}
		    }
		  if (cond != bddfalse)
		    res.h->aut->new_edge(res.cur_state, $1,
					 cond, $2 | res.acc_state);
		}
	      | state-conj-2 trans-acc_opt
		{
		  error(@1, "alternation is not yet supported");
		  YYABORT;
		}
incorrectly-labeled-edge: trans-label unlabeled-edge
                          {
			    error(@1, "ignoring this label, because previous"
				  " edge has no label");
                          }


/**********************************************************************/
/*                   Rules for LTL2DSTAR's format                     */
/**********************************************************************/

dstar: dstar_type "v2" "explicit" dstar_header "---" dstar_states ENDDSTAR
     | dstar_type error ENDDSTAR
       {
	 error(@$, "failed to parse this as an ltl2dstar automaton");
       }

dstar_type: "DRA"
       {
         res.h->type = spot::parsed_aut_type::DRA;
         res.plus = 1;
         res.minus = 0;
       }
       | "DSA"
       {
	 res.h->type = spot::parsed_aut_type::DSA;
         res.plus = 0;
         res.minus = 1;
       }

dstar_header: dstar_sizes
  {
    if (res.states < 0)
      error(@1, "missing state count");
    if (!res.ignore_more_acc)
      error(@1, "missing acceptance-pair count");
    if (res.start.empty())
      error(@1, "missing start-state number");
    if (!res.ignore_more_ap)
      error(@1, "missing atomic propositions definition");

    if (res.states > 0)
      {
	res.h->aut->new_states(res.states);;
	res.info_states.resize(res.states);
      }
    res.h->aut->prop_state_based_acc();
    res.h->aut->prop_deterministic();
    // res.h->aut->prop_complete();
    fill_guards(res);
    res.cur_guard = res.guards.end();
  }

dstar_sizes:
  | dstar_sizes error
  | dstar_sizes "Acceptance-Pairs:" INT
  {
    if (res.ignore_more_acc)
      {
	error(@1 + @2, "ignoring this redefinition of the "
	      "acceptance pairs...");
	error(res.accset_loc, "... previously defined here.");
      }
    else{
      res.accset = $3;
      res.h->aut->set_acceptance(2 * $3,
				 res.h->type == spot::parsed_aut_type::DRA
				 ? spot::acc_cond::acc_code::rabin($3)
				 : spot::acc_cond::acc_code::streett($3));
      res.accset_loc = @3;
      res.ignore_more_acc = true;
    }
  }
  | dstar_sizes "States:" INT
  {
    if (res.states < 0)
      {
	res.states = $3;
      }
    else
      {
	error(@$, "redeclaration of state count");
	if ((unsigned) res.states < $3)
	  res.states = $3;
      }
  }
  | dstar_sizes "Start:" INT
  {
    res.start.emplace_back(@3, $3);
  }
  | dstar_sizes aps

dstar_state_id: "State:" INT string_opt
  {
    if (res.cur_guard != res.guards.end())
      error(@1, "not enough transitions for previous state");
    if (res.states < 0 || $2 >= (unsigned) res.states)
      {
	std::ostringstream o;
	if (res.states > 0)
	  {
	    o << "state numbers should be in the range [0.."
	      << res.states - 1 << "]";
	  }
	else
	  {
	    o << "no states have been declared";
	  }
	error(@2, o.str());
      }
    else
      {
	res.info_states[$2].declared = true;

	if ($3)
	  {
	    if (!res.state_names)
	      res.state_names =
		new std::vector<std::string>(res.states > 0 ?
					     res.states : 0);
	    if (res.state_names->size() < $2 + 1)
	      res.state_names->resize($2 + 1);
	    (*res.state_names)[$2] = std::move(*$3);
	    delete $3;
	  }
      }

    res.cur_guard = res.guards.begin();
    res.dest_map.clear();
    res.cur_state = $2;
  }

sign: '+' { $$ = res.plus; }
  |   '-' { $$ = res.minus; }

// Membership to a pair is represented as (+NUM,-NUM)
dstar_accsigs:
  {
    $$ = 0U;
  }
  | dstar_accsigs sign INT
  {
    if (res.states < 0 || res.cur_state >= (unsigned) res.states)
      break;
    if (res.accset > 0 && $3 < (unsigned) res.accset)
      {
	$$ = $1;
	$$.set($3 * 2 + $2);
      }
    else
      {
	std::ostringstream o;
	if (res.accset > 0)
	  {
	    o << "acceptance pairs should be in the range [0.."
	      << res.accset - 1 << "]";
	  }
	else
	  {
	    o << "no acceptance pairs have been declared";
	  }
	error(@3, o.str());
      }
  }

dstar_state_accsig: "Acc-Sig:" dstar_accsigs { $$ = $2; }

dstar_transitions:
  | dstar_transitions INT
  {
    std::pair<map_t::iterator, bool> i =
      res.dest_map.emplace($2, *res.cur_guard);
    if (!i.second)
      i.first->second |= *res.cur_guard;
    ++res.cur_guard;
  }

dstar_states:
  | dstar_states error
  | dstar_states dstar_state_id dstar_state_accsig dstar_transitions
  {
    for (auto i: res.dest_map)
      res.h->aut->new_edge(res.cur_state, i.first, i.second, $3);
  }

/**********************************************************************/
/*                      Rules for neverclaims                         */
/**********************************************************************/

never: "never" { res.namer = res.h->aut->create_namer<std::string>();
	         res.h->aut->set_buchi();
		 res.h->aut->prop_state_based_acc();
		 res.acc_state = State_Acc;
		 res.pos_acc_sets = res.h->aut->acc().all_sets();
	       }
       '{' nc-states '}'
       {
	 // Add an accept_all state if needed.
	 if (res.accept_all_needed && !res.accept_all_seen)
	   {
	     unsigned n = res.namer->new_state("accept_all");
	     res.h->aut->new_acc_edge(n, n, bddtrue);
	   }
	 // If we aliased existing state, we have some unreachable
	 // states to remove.
	 if (res.aliased_states)
	   res.h->aut->purge_unreachable_states();
	 res.info_states.resize(res.h->aut->num_states());
	 // Pretend that we have declared all states.
	 for (auto& p: res.info_states)
	   p.declared = true;
       }

nc-states:
  /* empty */
  | nc-state
  | nc-states ';' nc-state
  | nc-states ';'

nc-one-ident: IDENTIFIER ':'
    {
      auto r = res.labels.insert(std::make_pair(*$1, @1));
      if (!r.second)
	{
	  error(@1, std::string("redefinition of ") + *$1 + "...");
	  error(r.first->second, std::string("... ")  + *$1
		+ " previously defined here");
	}
      $$ = $1;
    }

nc-ident-list: nc-one-ident
    {
      unsigned n = res.namer->new_state(*$1);
      if (res.start.empty())
	{
	  // The first state is initial.
	  res.start.emplace_back(@$, n);
	}
      $$ = $1;
    }
  | nc-ident-list nc-one-ident
    {
      res.aliased_states |=
	res.namer->alias_state(res.namer->get_state(*$1), *$2);
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

nc-transition-block:
  "if" nc-transitions "fi"
    {
      $$ = $2;
    }
  | "do" nc-transitions "od"
    {
      $$ = $2;
    }

nc-state:
  nc-ident-list "skip"
    {
      if (*$1 == "accept_all")
	res.accept_all_seen = true;

      auto acc = !strncmp("accept", $1->c_str(), 6) ?
	res.h->aut->acc().all_sets() : spot::acc_cond::mark_t(0U);
      res.namer->new_edge(*$1, *$1, bddtrue, acc);
      delete $1;
    }
  | nc-ident-list { delete $1; }
  | nc-ident-list "false" { delete $1; }
  | nc-ident-list nc-transition-block
    {
      auto acc = !strncmp("accept", $1->c_str(), 6) ?
	res.h->aut->acc().all_sets() : spot::acc_cond::mark_t(0U);
      for (auto& p: *$2)
	{
	  bdd c = bdd_from_int(p.first);
	  bdd_delref(p.first);
	  res.namer->new_edge(*$1, *p.second, c, acc);
	  delete p.second;
	}
      delete $1;
      delete $2;
    }

nc-transitions:
  /* empty */ { $$ = new std::list<pair>; }
  | nc-transitions nc-transition
    {
      if ($2)
	{
	  $1->push_back(*$2);
	  delete $2;
	}
      $$ = $1;
    }

nc-formula-or-ident: FORMULA | IDENTIFIER

nc-formula: nc-formula-or-ident
     {
       auto i = res.fcache.find(*$1);
       if (i == res.fcache.end())
	 {
	   spot::parse_error_list pel;
	   auto f = spot::parse_infix_boolean(*$1, pel, *res.env,
						   debug_level(), true);
	   for (auto& j: pel)
	     {
	       // Adjust the diagnostic to the current position.
	       spot::location here = @1;
	       here.end.line = here.begin.line + j.first.end.line - 1;
	       here.end.column = here.begin.column + j.first.end.column - 1;
	       here.begin.line += j.first.begin.line - 1;
	       here.begin.column += j.first.begin.column - 1;
	       error_list.emplace_back(here, j.second);
	     }
           bdd cond = bddfalse;
	   if (f)
	     cond = spot::formula_to_bdd(f, res.h->aut->get_dict(), res.h->aut);
	   $$ = (res.fcache[*$1] = cond).id();
	 }
       else
	 {
	   $$ = i->second.id();
	 }
       bdd_addref($$);
       delete $1;
     }
   | "false"
     {
       $$ = 0;
     }

nc-opt-dest:
  /* empty */
    {
      $$ = nullptr;
    }
  | "->" "goto" IDENTIFIER
    {
      $$ = $3;
    }
  | "->" "assert" FORMULA
    {
      delete $3;
      $$ = new std::string("accept_all");
      res.accept_all_needed = true;
    }

nc-src-dest: nc-formula nc-opt-dest
    {
      // If there is no destination, do ignore the transition.
      // This happens for instance with
      //   if
      //   :: false
      //   fi
      if (!$2)
	{
	  $$ = nullptr;
	}
      else
	{
	  $$ = new pair($1, $2);
	  res.namer->new_state(*$2);
	}
    }

nc-transition:
  ':' ':' "atomic" '{' nc-src-dest '}'
    {
      $$ = $5;
    }
  | ':' ':' nc-src-dest
    {
      $$ = $3;
    }

/**********************************************************************/
/*                         Rules for LBTT                             */
/**********************************************************************/

lbtt: lbtt-header lbtt-body ENDAUT
      {
	auto& acc = res.h->aut->acc();
	unsigned num = acc.num_sets();
	res.h->aut->set_generalized_buchi(num);
	res.pos_acc_sets = acc.all_sets();
	assert(!res.states_map.empty());
	auto n = res.states_map.size();
	if (n != (unsigned) res.states)
	  {
	    std::ostringstream err;
	    err << res.states << " states have been declared, but "
		<< n << " different state numbers have been used";
	    error(@$, err.str());
	  }
	if (res.states_map.rbegin()->first > (unsigned) res.states)
	  {
	    // We have seen numbers larger that the total number of
	    // states in the automaton.  Usually this happens when the
	    // states are numbered from 1 instead of 0, but the LBTT
	    // documentation actually allow any number to be used.
	    // What we have done is to map all input state numbers 0
	    // <= .. < n to the digraph states with the same number,
	    // and any time we saw a number larger than n, we mapped
	    // it to a new state.  The correspondence is given by
	    // res.states_map.  Now we just need to remove the useless
	    // states we allocated.
	    std::vector<unsigned> rename(res.h->aut->num_states(), -1U);
	    unsigned s = 0;
	    for (auto& i: res.states_map)
	      rename[i.second] = s++;
	    assert(s == (unsigned) res.states);
	    for (auto& i: res.start)
	      i.second = rename[i.second];
	    res.h->aut->get_graph().defrag_states(std::move(rename), s);
	  }
	 res.info_states.resize(res.h->aut->num_states());
	 for (auto& s: res.info_states)
	   s.declared = true;
      }
    | lbtt-header-states LBTT_EMPTY
      {
        res.h->aut->set_generalized_buchi($2);
	res.pos_acc_sets = res.h->aut->acc().all_sets();
      }

lbtt-header-states: LBTT
                  {
		    res.states = $1;
		    res.states_loc = @1;
		    res.h->aut->new_states($1);
		  }
lbtt-header: lbtt-header-states INT_S
           {
	     res.acc_mapper = new spot::acc_mapper_int(res.h->aut, $2);
	     res.h->aut->prop_state_based_acc();
	     res.acc_state = State_Acc;
	   }
           | lbtt-header-states INT
           {
	     res.acc_mapper = new spot::acc_mapper_int(res.h->aut, $2);
	     res.trans_acc_seen = true;
	   }
lbtt-body: lbtt-states
lbtt-states:
           | lbtt-states lbtt-state lbtt-transitions

lbtt-state: STATE_NUM INT lbtt-acc
          {
	    if ($1 >= (unsigned) res.states)
	      {
		auto p = res.states_map.emplace($1, 0);
		if (p.second)
		  p.first->second = res.h->aut->new_state();
		res.cur_state = p.first->second;
	      }
	    else
	      {
		res.states_map.emplace($1, $1);
		res.cur_state = $1;
	      }
	    if ($2)
	      res.start.emplace_back(@1 + @2, res.cur_state);
	    res.acc_state = $3;
	  }
lbtt-acc:               { $$ = 0U; }
        | lbtt-acc ACC
	{
	  $$  = $1;
	  auto p = res.acc_mapper->lookup($2);
	  if (p.first)
	    $$ |= p.second;
	  else
	    error(@2, "more acceptance sets used than declared");
	}
lbtt-guard: STRING
          {
	    spot::parse_error_list pel;
	    auto f = spot::parse_prefix_ltl(*$1, pel, *res.env);
	    if (!f || !pel.empty())
	      {
		std::string s = "failed to parse guard: ";
		s += *$1;
		error(@$, s);
	      }
	    if (!pel.empty())
	      for (auto& j: pel)
		{
		  // Adjust the diagnostic to the current position.
		  spot::location here = @1;
		  here.end.line = here.begin.line + j.first.end.line - 1;
		  here.end.column = here.begin.column + j.first.end.column - 1;
		  here.begin.line += j.first.begin.line - 1;
		  here.begin.column += j.first.begin.column - 1;
		  error_list.emplace_back(here, j.second);
		}
	    if (!f)
	      {
		res.cur_label = bddtrue;
	      }
	    else
	      {
		if (!f.is_boolean())
		  {
		    error(@$,
			  "non-Boolean transition label (replaced by true)");
		    res.cur_label = bddtrue;
		  }
		else
		  {
		    res.cur_label =
		      formula_to_bdd(f, res.h->aut->get_dict(), res.h->aut);
		  }
	      }
	    delete $1;
	  }
lbtt-transitions:
                | lbtt-transitions DEST_NUM lbtt-acc lbtt-guard
                {
		  unsigned dst = $2;
		  if (dst >= (unsigned) res.states)
		    {
		      auto p = res.states_map.emplace(dst, 0);
		      if (p.second)
			p.first->second = res.h->aut->new_state();
		      dst = p.first->second;
		    }
		  else
		    {
		      res.states_map.emplace(dst, dst);
	            }
		  res.h->aut->new_edge(res.cur_state, dst,
				       res.cur_label,
				       res.acc_state | $3);
		}

%%

static void fill_guards(result_& r)
{
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

static spot::acc_cond::acc_code
fix_acceptance_aux(spot::acc_cond& acc,
		   spot::acc_cond::acc_code in, unsigned pos,
		   spot::acc_cond::mark_t onlyneg,
		   spot::acc_cond::mark_t both,
		   unsigned base)
{
  auto& w = in[pos];
  switch (w.op)
    {
    case spot::acc_cond::acc_op::And:
      {
	unsigned sub = pos - w.size;
	--pos;
	auto c = fix_acceptance_aux(acc, in, pos, onlyneg, both, base);
	pos -= in[pos].size;
	while (sub < pos)
	  {
	    --pos;
	    c.append_and(fix_acceptance_aux(acc, in, pos, onlyneg, both, base));
	    pos -= in[pos].size;
	  }
	return c;
      }
    case spot::acc_cond::acc_op::Or:
      {
	unsigned sub = pos - w.size;
	--pos;
	auto c = fix_acceptance_aux(acc, in, pos, onlyneg, both, base);
	pos -= in[pos].size;
	while (sub < pos)
	  {
	    --pos;
	    c.append_or(fix_acceptance_aux(acc, in, pos, onlyneg, both, base));
	    pos -= in[pos].size;
	  }
	return c;
      }
    case spot::acc_cond::acc_op::Inf:
      return acc.inf(in[pos - 1].mark);
    case spot::acc_cond::acc_op::Fin:
      return acc.fin(in[pos - 1].mark);
    case spot::acc_cond::acc_op::FinNeg:
      {
	auto m = in[pos - 1].mark;
	auto c = acc.fin(onlyneg & m);
	spot::acc_cond::mark_t tmp = 0U;
	for (auto i: both.sets())
	  {
	    if (m.has(i))
	      tmp.set(base);
	    ++base;
	  }
	if (tmp)
	  c.append_or(acc.fin(tmp));
	return c;
      }
    case spot::acc_cond::acc_op::InfNeg:
      {
	auto m = in[pos - 1].mark;
	auto c = acc.inf(onlyneg & m);
	spot::acc_cond::mark_t tmp = 0U;
	for (auto i: both.sets())
	  {
	    if (m.has(i))
	      tmp.set(base);
	    ++base;
	  }
	if (tmp)
	  c.append_and(acc.inf(tmp));
	return c;
      }
    }
  SPOT_UNREACHABLE();
  return {};
}

static void fix_acceptance(result_& r)
{
  auto& acc = r.h->aut->acc();

  // If a set x appears only as Inf(!x), we can complement it so that
  // we work with Inf(x) instead.
  auto onlyneg = r.neg_acc_sets - r.pos_acc_sets;
  if (onlyneg)
    {
      for (auto& t: r.h->aut->edge_vector())
	t.acc ^= onlyneg;
    }

  // However if set x is used elsewhere, for instance in
  //   Inf(!x) & Inf(x)
  // complementing x would be wrong.  We need to create a
  // new set, y, that is the complement of x, and rewrite
  // this as Inf(y) & Inf(x).
  auto both = r.neg_acc_sets & r.pos_acc_sets;
  unsigned base = 0;
  if (both)
    {
      auto v = acc.sets(both);
      auto vs = v.size();
      base = acc.add_sets(vs);
      for (auto& t: r.h->aut->edge_vector())
	if ((t.acc & both) != both)
	  for (unsigned i = 0; i < vs; ++i)
	    if (!t.acc.has(v[i]))
	      t.acc |= acc.mark(base + i);
    }

  if (onlyneg || both)
    {
      auto& acc = r.h->aut->acc();
      auto code = acc.get_acceptance();
      r.h->aut->set_acceptance(acc.num_sets(),
			       fix_acceptance_aux(acc, code, code.size() - 1,
						  onlyneg, both, base));
    }
}

static void fix_initial_state(result_& r)
{

  std::vector<unsigned> start;
  start.reserve(r.start.size());
  for (auto& p : r.start)
    // Ignore initial states without declaration
    if (p.second < r.info_states.size()
	&& r.info_states[p.second].declared)
      start.push_back(p.second);

  if (start.empty())
    {
      // If no initial state has been declared, add one, because
      // Spot will not work without one.
      r.h->aut->set_init_state(r.h->aut->new_state());
      return;
    }

  // Remove any duplicate initial state.
  std::sort(start.begin(), start.end());
  auto res = std::unique(start.begin(), start.end());
  start.resize(std::distance(start.begin(), res));

  assert(start.size() >= 1);
  if (start.size() == 1)
    {
      r.h->aut->set_init_state(start.front());
    }
  else
    {
      // Multiple initial states.  We might need to add a fake one,
      // unless one of the actual initial state has no incoming edge.
      auto& aut = r.h->aut;
      std::vector<unsigned> has_incoming(aut->num_states(), 0);
      for (auto& t: aut->edges())
	has_incoming[t.dst] = true;

      bool found = false;
      unsigned init = 0;
      for (auto p: start)
	if (!has_incoming[p])
	  {
	    init = p;
	    found = true;
	  }
      if (!found)
	// We do need a fake initial state
	init = aut->new_state();
      aut->set_init_state(init);
      for (auto p: start)
	if (p != init)
	  for (auto& t: aut->out(p))
	    aut->new_edge(init, t.dst, t.cond);
    }
}

static void fix_properties(result_& r)
{
  r.h->aut->prop_deterministic(r.deterministic);
  //r.h->aut->prop_complete(r.complete);
  if (r.acc_style == State_Acc ||
      (r.acc_style == Mixed_Acc && !r.trans_acc_seen))
    r.h->aut->prop_state_based_acc();
}

static void check_version(const result_& r,
			  spot::parse_aut_error_list& error_list)
{
  if (r.h->type != spot::parsed_aut_type::HOA)
    return;
  auto& v = r.format_version;
  if (v.size() < 2 || v[0] != 'v' || v[1] < '1' || v[1] > '9')
    {
      error_list.emplace_front(r.format_version_loc, "unknown HOA version");
      return;
    }
  const char* beg = &v[1];
  char* end = nullptr;
  long int vers = strtol(beg, &end, 10);
  if (vers != 1)
    {
      error_list.emplace_front(r.format_version_loc, "unsupported HOA version");
      return;
    }
  constexpr const char supported[] = "1";
  if (strverscmp(supported, beg) < 0 && !error_list.empty())
    {
      std::ostringstream s;
      s << "we can read HOA v" << supported
	<< " but this file uses " << v << "; this might "
	<< "cause the following errors";
      error_list.emplace_front(r.format_version_loc, s.str());
      return;
    }
}

namespace spot
{
  automaton_stream_parser::automaton_stream_parser(const std::string& name,
						   automaton_parser_options opt)
    : filename_(name), opts_(opt)
  {
    if (hoayyopen(name))
      throw std::runtime_error(std::string("Cannot open file ") + name);
  }

  automaton_stream_parser::automaton_stream_parser(int fd,
						   const std::string& name,
						   automaton_parser_options opt)
    : filename_(name), opts_(opt)
  {
    if (hoayyopen(fd))
      throw std::runtime_error(std::string("Cannot open file ") + name);
  }

  automaton_stream_parser::automaton_stream_parser(const char* data,
						   const std::string& filename,
						   automaton_parser_options opt)
    : filename_(filename), opts_(opt)
  {
    hoayystring(data);
  }

  automaton_stream_parser::~automaton_stream_parser()
  {
    hoayyclose();
  }


  parsed_aut_ptr
  automaton_stream_parser::parse(parse_aut_error_list& error_list,
				 const bdd_dict_ptr& dict,
				 environment& env)
  {
  restart:
    result_ r;
    r.h = std::make_shared<spot::parsed_aut>();
    r.h->aut = make_twa_graph(dict);
    r.env = &env;
    hoayy::parser parser(error_list, r, last_loc);
    static bool env_debug = !!getenv("SPOT_DEBUG_PARSER");
    parser.set_debug_level(opts_.debug || env_debug);
    hoayyreset();
    try
      {
	if (parser.parse())
	  r.h->aut = nullptr;
      }
    catch (const spot::hoa_abort& e)
      {
	r.h->aborted = true;
	// Bison 3.0.2 lacks a += operator for locations.
	r.h->loc = r.h->loc + e.pos;
      }
    check_version(r, error_list);
    last_loc = r.h->loc;
    last_loc.step();
    if (r.h->aborted)
      {
	if (opts_.ignore_abort)
	  goto restart;
	return r.h;
      }
    if (!r.h->aut)
      return nullptr;
    if (r.state_names)
      r.h->aut->set_named_prop("state-names", r.state_names);
    fix_acceptance(r);
    fix_initial_state(r);
    fix_properties(r);
    return r.h;
  };

  twa_graph_ptr
  automaton_stream_parser::parse_strict(const bdd_dict_ptr& dict,
					environment& env)
  {
    parse_aut_error_list pel;
    auto a = parse(pel, dict, env);

    if (!pel.empty())
      {
	std::ostringstream s;
	if (format_parse_aut_errors(s, filename_, pel))
	  throw parse_error(s.str());
      }
    if (!a)
      return nullptr;

    if (a->aborted)
      throw parse_error("parsing aborted");

    return a->aut;
  }
}

// Local Variables:
// mode: c++
// End:
