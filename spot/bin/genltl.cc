// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2015 Laboratoire de Recherche et Développement
// de l'Epita (LRDE).
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// Families defined here come from the following papers:
//
// @InProceedings{cichon.09.depcos,
//   author = {Jacek Cicho{\'n} and Adam Czubak and Andrzej Jasi{\'n}ski},
//   title = {Minimal {B\"uchi} Automata for Certain Classes of {LTL} Formulas},
//   booktitle = {Proceedings of the Fourth International Conference on
//                Dependability of Computer Systems},
//   pages = {17--24},
//   year = 2009,
//   publisher = {IEEE Computer Society},
// }
//
// @InProceedings{geldenhuys.06.spin,
//   author = {Jaco Geldenhuys and Henri Hansen},
//   title = {Larger Automata and Less Work for LTL Model Checking},
//   booktitle = {Proceedings of the 13th International SPIN Workshop},
//   year = {2006},
//   pages = {53--70},
//   series = {Lecture Notes in Computer Science},
//   volume = {3925},
//   publisher = {Springer}
// }
//
// @InProceedings{gastin.01.cav,
//   author = {Paul Gastin and Denis Oddoux},
//   title = {Fast {LTL} to {B\"u}chi Automata Translation},
//   booktitle	= {Proceedings of the 13th International Conference on
// 		  Computer Aided Verification (CAV'01)},
//   pages = {53--65},
//   year = 2001,
//   editor = {G. Berry and H. Comon and A. Finkel},
//   volume = {2102},
//   series = {Lecture Notes in Computer Science},
//   address = {Paris, France},
//   publisher = {Springer-Verlag}
// }
//
// @InProceedings{rozier.07.spin,
//   author = {Kristin Y. Rozier and Moshe Y. Vardi},
//   title = {LTL Satisfiability Checking},
//   booktitle = {Proceedings of the 12th International SPIN Workshop on
// 		  Model Checking of Software (SPIN'07)},
//   pages = {149--167},
//   year = {2007},
//   volume = {4595},
//   series = {Lecture Notes in Computer Science},
//   publisher = {Springer-Verlag}
// }

#include "common_sys.hh"

#include <iostream>
#include <fstream>
#include <argp.h>
#include <cstdlib>
#include "error.h"
#include <vector>

#include "common_setup.hh"
#include "common_output.hh"
#include "common_range.hh"

#include <cassert>
#include <iostream>
#include <sstream>
#include <set>
#include <string>
#include <cstdlib>
#include <cstring>
#include <spot/tl/formula.hh>
#include <spot/tl/relabel.hh>

using namespace spot;

const char argp_program_doc[] ="\
Generate temporal logic formulas from predefined scalable patterns.";

enum {
  OPT_AND_F = 1,
  OPT_AND_FG,
  OPT_AND_GF,
  OPT_CCJ_ALPHA,
  OPT_CCJ_BETA,
  OPT_CCJ_BETA_PRIME,
  OPT_GH_Q,
  OPT_GH_R,
  OPT_GO_THETA,
  OPT_OR_FG,
  OPT_OR_G,
  OPT_OR_GF,
  OPT_R_LEFT,
  OPT_R_RIGHT,
  OPT_RV_COUNTER,
  OPT_RV_COUNTER_CARRY,
  OPT_RV_COUNTER_CARRY_LINEAR,
  OPT_RV_COUNTER_LINEAR,
  OPT_U_LEFT,
  OPT_U_RIGHT,
  LAST_CLASS,
};

const char* const class_name[LAST_CLASS] =
  {
    "and-f",
    "and-fg",
    "and-gf",
    "ccj-alpha",
    "ccj-beta",
    "ccj-beta-prime",
    "gh-q",
    "gh-r",
    "go-theta",
    "or-fg",
    "or-g",
    "or-gf",
    "or-r-left",
    "or-r-right",
    "rv-counter",
    "rv-counter-carry",
    "rv-counter-carry-linear",
    "rv-counter-linear",
    "u-left",
    "u-right",
  };


#define OPT_ALIAS(o) { #o, 0, nullptr, OPTION_ALIAS, nullptr, 0 }

static const argp_option options[] =
  {
    /**************************************************/
    // Keep this alphabetically sorted (expect for aliases).
    { nullptr, 0, nullptr, 0, "Pattern selection:", 1},
    // J. Geldenhuys and H. Hansen (Spin'06): Larger automata and less
    // work for LTL model checking.
    { "and-f", OPT_AND_F, "RANGE", 0, "F(p1)&F(p2)&...&F(pn)", 0 },
    OPT_ALIAS(gh-e),
    { "and-fg", OPT_AND_FG, "RANGE", 0, "FG(p1)&FG(p2)&...&FG(pn)", 0 },
    { "and-gf", OPT_AND_GF, "RANGE", 0, "GF(p1)&GF(p2)&...&GF(pn)", 0 },
    OPT_ALIAS(ccj-phi),
    OPT_ALIAS(gh-c2),
    { "ccj-alpha", OPT_CCJ_ALPHA, "RANGE", 0,
      "F(p1&F(p2&F(p3&...F(pn)))) & F(q1&F(q2&F(q3&...F(qn))))", 0 },
    { "ccj-beta", OPT_CCJ_BETA, "RANGE", 0,
      "F(p&X(p&X(p&...X(p)))) & F(q&X(q&X(q&...X(q))))", 0 },
    { "ccj-beta-prime", OPT_CCJ_BETA_PRIME, "RANGE", 0,
      "F(p&(Xp)&(XXp)&...(X...X(p))) & F(q&(Xq)&(XXq)&...(X...X(q)))", 0 },
    { "gh-q", OPT_GH_Q, "RANGE", 0,
      "(F(p1)|G(p2))&(F(p2)|G(p3))&... &(F(pn)|G(p{n+1}))", 0 },
    { "gh-r", OPT_GH_R, "RANGE", 0,
      "(GF(p1)|FG(p2))&(GF(p2)|FG(p3))&... &(GF(pn)|FG(p{n+1}))", 0},
    { "go-theta", OPT_GO_THETA, "RANGE", 0,
      "!((GF(p1)&GF(p2)&...&GF(pn)) -> G(q->F(r)))", 0 },
    { "or-fg", OPT_OR_FG, "RANGE", 0, "FG(p1)|FG(p2)|...|FG(pn)", 0 },
    OPT_ALIAS(ccj-xi),
    { "or-g", OPT_OR_G, "RANGE", 0, "G(p1)|G(p2)|...|G(pn)", 0 },
    OPT_ALIAS(gh-s),
    { "or-gf", OPT_OR_GF, "RANGE", 0, "GF(p1)|GF(p2)|...|GF(pn)", 0 },
    OPT_ALIAS(gh-c1),
    { "r-left", OPT_R_LEFT, "RANGE", 0, "(((p1 R p2) R p3) ... R pn)", 0 },
    { "r-right", OPT_R_RIGHT, "RANGE", 0, "(p1 R (p2 R (... R pn)))", 0 },
    { "rv-counter", OPT_RV_COUNTER, "RANGE", 0,
      "n-bit counter", 0 },
    { "rv-counter-carry", OPT_RV_COUNTER_CARRY, "RANGE", 0,
      "n-bit counter w/ carry", 0 },
    { "rv-counter-carry-linear", OPT_RV_COUNTER_CARRY_LINEAR, "RANGE", 0,
      "n-bit counter w/ carry (linear size)", 0 },
    { "rv-counter-linear", OPT_RV_COUNTER_LINEAR, "RANGE", 0,
      "n-bit counter (linear size)", 0 },
    { "u-left", OPT_U_LEFT, "RANGE", 0, "(((p1 U p2) U p3) ... U pn)", 0 },
    OPT_ALIAS(gh-u),
    { "u-right", OPT_U_RIGHT, "RANGE", 0, "(p1 U (p2 U (... U pn)))", 0 },
    OPT_ALIAS(gh-u2),
    OPT_ALIAS(go-phi),
    RANGE_DOC,
  /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", -20 },
    { nullptr, 0, nullptr, 0, "The FORMAT string passed to --format may use "
      "the following interpreted sequences:", -19 },
    { "%f", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the formula (in the selected syntax)", 0 },
    { "%F", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the name of the pattern", 0 },
    { "%L", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the argument of the pattern", 0 },
    { "%%", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "a single %", 0 },
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

struct job
{
  int pattern;
  struct range range;
};

typedef std::vector<job> jobs_t;
static jobs_t jobs;


const struct argp_child children[] =
  {
    { &output_argp, 0, nullptr, -20 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

static void
enqueue_job(int pattern, const char* range_str)
{
  job j;
  j.pattern = pattern;
  j.range = parse_range(range_str);
  jobs.push_back(j);
}

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // This switch is alphabetically-ordered.
  switch (key)
    {
    case OPT_AND_F:
    case OPT_AND_FG:
    case OPT_AND_GF:
    case OPT_CCJ_ALPHA:
    case OPT_CCJ_BETA:
    case OPT_CCJ_BETA_PRIME:
    case OPT_GH_Q:
    case OPT_GH_R:
    case OPT_GO_THETA:
    case OPT_OR_FG:
    case OPT_OR_G:
    case OPT_OR_GF:
    case OPT_R_LEFT:
    case OPT_R_RIGHT:
    case OPT_RV_COUNTER:
    case OPT_RV_COUNTER_CARRY:
    case OPT_RV_COUNTER_CARRY_LINEAR:
    case OPT_RV_COUNTER_LINEAR:
    case OPT_U_LEFT:
    case OPT_U_RIGHT:
      enqueue_job(key, arg);
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

#define G_(x) formula::G(x)
#define F_(x) formula::F(x)
#define X_(x) formula::X(x)
#define Not_(x) formula::Not(x)

#define Implies_(x, y) formula::Implies((x), (y))
#define Equiv_(x, y) formula::Equiv((x), (y))
#define And_(x, y) formula::And({(x), (y)})
#define Or_(x, y) formula::Or({(x), (y)})
#define U_(x, y) formula::U((x), (y))

// F(p_1 & F(p_2 & F(p_3 & ... F(p_n))))
static formula
E_n(std::string name, int n)
{
  if (n <= 0)
    return formula::tt();

  formula result = nullptr;

  for (; n > 0; --n)
    {
      std::ostringstream p;
      p << name << n;
      formula f = formula::ap(p.str());
      if (result)
	result = And_(f, result);
      else
	result = f;
      result = F_(result);
    }
  return result;
}

// p & X(p & X(p & ... X(p)))
static formula
phi_n(std::string name, int n)
{
  if (n <= 0)
    return formula::tt();

  formula result = nullptr;
  formula p = formula::ap(name);
  for (; n > 0; --n)
    {
      if (result)
	result = And_(p, X_(result));
      else
	result = p;
    }
  return result;
}

static formula
N_n(std::string name, int n)
{
  return formula::F(phi_n(name, n));
}

// p & X(p) & XX(p) & XXX(p) & ... X^n(p)
static formula
phi_prime_n(std::string name, int n)
{
  if (n <= 0)
    return formula::tt();

  formula result = nullptr;
  formula p = formula::ap(name);
  for (; n > 0; --n)
    {
      if (result)
	{
	  p = X_(p);
	  result = And_(result, p);
	}
      else
	{
	  result = p;
	}
    }
  return result;
}

static formula
N_prime_n(std::string name, int n)
{
  return F_(phi_prime_n(name, n));
}


// GF(p_1) & GF(p_2) & ... & GF(p_n)   if conj == true
// GF(p_1) | GF(p_2) | ... | GF(p_n)   if conj == false
static formula
GF_n(std::string name, int n, bool conj = true)
{
  if (n <= 0)
    return conj ? formula::tt() : formula::ff();

  formula result = nullptr;

  op o = conj ? op::And : op::Or;

  for (int i = 1; i <= n; ++i)
    {
      std::ostringstream p;
      p << name << i;
      formula f = G_(F_(formula::ap(p.str())));

      if (result)
	result = formula::multop(o, {f, result});
      else
	result = f;
    }
  return result;
}

// FG(p_1) | FG(p_2) | ... | FG(p_n)   if conj == false
// FG(p_1) & FG(p_2) & ... & FG(p_n)   if conj == true
static formula
FG_n(std::string name, int n, bool conj = false)
{
  if (n <= 0)
    return conj ? formula::tt() : formula::ff();

  formula result = nullptr;

  op o = conj ? op::And : op::Or;

  for (int i = 1; i <= n; ++i)
    {
      std::ostringstream p;
      p << name << i;
      formula f = F_(G_(formula::ap(p.str())));

      if (result)
	result = formula::multop(o, {f, result});
      else
	result = f;
    }
  return result;
}

//  (((p1 OP p2) OP p3)...OP pn)   if right_assoc == false
//  (p1 OP (p2 OP (p3 OP (... pn)  if right_assoc == true
static formula
bin_n(std::string name, int n, op o, bool right_assoc = false)
{
  if (n <= 0)
    n = 1;

  formula result = nullptr;

  for (int i = 1; i <= n; ++i)
    {
      std::ostringstream p;
      p << name << (right_assoc ? (n + 1 - i) : i);
      formula f = formula::ap(p.str());
      if (!result)
	result = f;
      else if (right_assoc)
	result = formula::binop(o, f, result);
      else
	result = formula::binop(o, result, f);
    }
  return result;
}

// (GF(p1)|FG(p2))&(GF(p2)|FG(p3))&...&(GF(pn)|FG(p{n+1}))"
static formula
R_n(std::string name, int n)
{
  if (n <= 0)
    return formula::tt();

  formula pi;

  {
    std::ostringstream p;
    p << name << 1;
    pi = formula::ap(p.str());
  }

  formula result = nullptr;

  for (int i = 1; i <= n; ++i)
    {
      formula gf = G_(F_(pi));
      std::ostringstream p;
      p << name << i + 1;
      pi = formula::ap(p.str());

      formula fg = F_(G_(pi));

      formula f = Or_(gf, fg);

      if (result)
	result = And_(f, result);
      else
	result = f;
    }
  return result;
}

// (F(p1)|G(p2))&(F(p2)|G(p3))&...&(F(pn)|G(p{n+1}))"
static formula
Q_n(std::string name, int n)
{
  if (n <= 0)
    return formula::tt();

  formula pi;

  {
    std::ostringstream p;
    p << name << 1;
    pi = formula::ap(p.str());
  }

  formula result = nullptr;

  for (int i = 1; i <= n; ++i)
    {
      formula f = F_(pi);

      std::ostringstream p;
      p << name << i + 1;
      pi = formula::ap(p.str());

      formula g = G_(pi);

      f = Or_(f, g);

      if (result)
	result = And_(f, result);
      else
	result = f;
    }
  return result;
}

//  OP(p1) | OP(p2) | ... | OP(Pn) if conj == false
//  OP(p1) & OP(p2) & ... & OP(Pn) if conj == true
static formula
combunop_n(std::string name, int n, op o, bool conj = false)
{
  if (n <= 0)
    return conj ? formula::tt() : formula::ff();

  formula result = nullptr;

  op cop = conj ? op::And : op::Or;

  for (int i = 1; i <= n; ++i)
    {
      std::ostringstream p;
      p << name << i;
      formula f = formula::unop(o, formula::ap(p.str()));

      if (result)
	result = formula::multop(cop, {f, result});
      else
	result = f;
    }
  return result;
}

// !((GF(p1)&GF(p2)&...&GF(pn))->G(q -> F(r)))
// From "Fast LTL to Büchi Automata Translation" [gastin.01.cav]
static formula
fair_response(std::string p, std::string q, std::string r, int n)
{
  formula fair = GF_n(p, n);
  formula resp = G_(Implies_(formula::ap(q), F_(formula::ap(r))));
  return Not_(Implies_(fair, resp));
}


// Builds X(X(...X(p))) with n occurrences of X.
static formula
X_n(formula p, int n)
{
  assert(n >= 0);
  formula res = p;
  while (n--)
    res = X_(res);
  return res;
}

// Based on LTLcounter.pl from Kristin Rozier.
// http://shemesh.larc.nasa.gov/people/kyr/benchmarking_scripts/
static formula
ltl_counter(std::string bit, std::string marker, int n, bool linear)
{
  formula b = formula::ap(bit);
  formula neg_b = Not_(b);
  formula m = formula::ap(marker);
  formula neg_m = Not_(m);

  std::vector<formula> res(4);

  // The marker starts with "1", followed by n-1 "0", then "1" again,
  // n-1 "0", etc.
  if (!linear)
    {
      // G(m -> X(!m)&XX(!m)&XXX(m))          [if n = 3]
      std::vector<formula> v(n);
      for (int i = 0; i + 1 < n; ++i)
	v[i] = X_n(neg_m, i + 1);
      v[n - 1] = X_n(m, n);
      res[0] = And_(m, G_(Implies_(m, formula::And(std::move(v)))));
    }
  else
    {
      // G(m -> X(!m & X(!m X(m))))          [if n = 3]
      formula p = m;
      for (int i = n - 1; i > 0; --i)
	p = And_(neg_m, X_(p));
      res[0] = And_(m, G_(Implies_(m, X_(p))));
    }

  // All bits are initially zero.
  if (!linear)
    {
      // !b & X(!b) & XX(!b)    [if n = 3]
      std::vector<formula> v2(n);
      for (int i = 0; i < n; ++i)
	v2[i] = X_n(neg_b, i);
      res[1] = formula::And(std::move(v2));
    }
  else
    {
      // !b & X(!b & X(!b))     [if n = 3]
      formula p = neg_b;
      for (int i = n - 1; i > 0; --i)
	p = And_(neg_b, X_(p));
      res[1] = p;
    }

#define AndX_(x, y) (linear ? X_(And_((x), (y))) : And_(X_(x), X_(y)))

  // If the least significant bit is 0, it will be 1 at the next time,
  // and other bits stay the same.
  formula Xnm1_b = X_n(b, n - 1);
  formula Xn_b = X_(Xnm1_b);
  res[2] = G_(Implies_(And_(m, neg_b),
		       AndX_(Xnm1_b, U_(And_(Not_(m), Equiv_(b, Xn_b)), m))));

  // From the least significant bit to the first 0, all the bits
  // are flipped on the next value.  Remaining bits are identical.
  formula Xnm1_negb = X_n(neg_b, n - 1);
  formula Xn_negb = X_(Xnm1_negb);
  res[3] = G_(Implies_(And_(m, b),
		       AndX_(Xnm1_negb,
			     U_(And_(And_(b, neg_m), Xn_negb),
				Or_(m, And_(And_(neg_m, neg_b),
					    AndX_(Xnm1_b,
						  U_(And_(neg_m,
							  Equiv_(b, Xn_b)),
						     m))))))));
  return formula::And(std::move(res));
}

static formula
ltl_counter_carry(std::string bit, std::string marker,
		  std::string carry, int n, bool linear)
{
  formula b = formula::ap(bit);
  formula neg_b = Not_(b);
  formula m = formula::ap(marker);
  formula neg_m = Not_(m);
  formula c = formula::ap(carry);
  formula neg_c = Not_(c);

  std::vector<formula> res(6);

  // The marker starts with "1", followed by n-1 "0", then "1" again,
  // n-1 "0", etc.
  if (!linear)
    {
      // G(m -> X(!m)&XX(!m)&XXX(m))          [if n = 3]
      std::vector<formula> v(n);
      for (int i = 0; i + 1 < n; ++i)
	v[i] = X_n(neg_m, i + 1);
      v[n - 1] = X_n(m, n);
      res[0] = And_(m, G_(Implies_(m, formula::And(std::move(v)))));
    }
  else
    {
      // G(m -> X(!m & X(!m X(m))))          [if n = 3]
      formula p = m;
      for (int i = n - 1; i > 0; --i)
	p = And_(neg_m, X_(p));
      res[0] = And_(m, G_(Implies_(m, X_(p))));
    }

  // All bits are initially zero.
  if (!linear)
    {
      // !b & X(!b) & XX(!b)    [if n = 3]
      std::vector<formula> v2(n);
      for (int i = 0; i < n; ++i)
	v2[i] = X_n(neg_b, i);
      res[1] = formula::And(std::move(v2));
    }
  else
    {
      // !b & X(!b & X(!b))     [if n = 3]
      formula p = neg_b;
      for (int i = n - 1; i > 0; --i)
	p = And_(neg_b, X_(p));
      res[1] = p;
    }

  formula Xn_b = X_n(b, n);
  formula Xn_negb = X_n(neg_b, n);

  // If m is 1 and b is 0 then c is 0 and n steps later b is 1.
  res[2] = G_(Implies_(And_(m, neg_b), And_(neg_c, Xn_b)));

  // If m is 1 and b is 1 then c is 1 and n steps later b is 0.
  res[3] = G_(Implies_(And_(m, b), And_(c, Xn_negb)));

  if (!linear)
    {
      // If there's no carry, then all of the bits stay the same n steps later.
      res[4] = G_(Implies_(And_(neg_c, X_(neg_m)),
			   And_(X_(Not_(c)), Equiv_(X_(b), X_(Xn_b)))));

      // If there's a carry, then add one: flip the bits of b and
      // adjust the carry.
      res[5] = G_(Implies_(c, And_(Implies_(X_(neg_b),
					    And_(X_(neg_c), X_(Xn_b))),
				   Implies_(X_(b),
					    And_(X_(c), X_(Xn_negb))))));
    }
  else
    {
      // If there's no carry, then all of the bits stay the same n steps later.
      res[4] = G_(Implies_(And_(neg_c, X_(neg_m)),
			   X_(And_(Not_(c), Equiv_(b, Xn_b)))));
      // If there's a carry, then add one: flip the bits of b and
      // adjust the carry.
      res[5] = G_(Implies_(c, X_(And_(Implies_(neg_b, And_(neg_c, Xn_b)),
				      Implies_(b, And_(c, Xn_negb))))));
    }
  return formula::And(std::move(res));
}


static void
output_pattern(int pattern, int n)
{
  formula f = nullptr;
  switch (pattern)
    {
      // Keep this alphabetically-ordered!
    case OPT_AND_F:
      f = combunop_n("p", n, op::F, true);
      break;
    case OPT_AND_FG:
      f = FG_n("p", n, true);
      break;
    case OPT_AND_GF:
      f = GF_n("p", n, true);
      break;
    case OPT_CCJ_ALPHA:
      f = formula::And({E_n("p", n), E_n("q", n)});
      break;
    case OPT_CCJ_BETA:
      f = formula::And({N_n("p", n), N_n("q", n)});
      break;
    case OPT_CCJ_BETA_PRIME:
      f = formula::And({N_prime_n("p", n), N_prime_n("q", n)});
      break;
    case OPT_GH_Q:
      f = Q_n("p", n);
      break;
    case OPT_GH_R:
      f = R_n("p", n);
      break;
    case OPT_GO_THETA:
      f = fair_response("p", "q", "r", n);
      break;
    case OPT_OR_FG:
      f = FG_n("p", n, false);
      break;
    case OPT_OR_G:
      f = combunop_n("p", n, op::G, false);
      break;
    case OPT_OR_GF:
      f = GF_n("p", n, false);
      break;
    case OPT_R_LEFT:
      f = bin_n("p", n, op::R, false);
      break;
    case OPT_R_RIGHT:
      f = bin_n("p", n, op::R, true);
      break;
    case OPT_RV_COUNTER_CARRY:
      f = ltl_counter_carry("b", "m", "c", n, false);
      break;
    case OPT_RV_COUNTER_CARRY_LINEAR:
      f = ltl_counter_carry("b", "m", "c", n, true);
      break;
    case OPT_RV_COUNTER:
      f = ltl_counter("b", "m", n, false);
      break;
    case OPT_RV_COUNTER_LINEAR:
      f = ltl_counter("b", "m", n, true);
      break;
    case OPT_U_LEFT:
      f = bin_n("p", n, op::U, false);
      break;
    case OPT_U_RIGHT:
      f = bin_n("p", n, op::U, true);
      break;
    default:
      error(100, 0, "internal error: pattern not implemented");
    }

  // Make sure we use only "p42"-style of atomic propositions
  // in lbt's output.
  if (output_format == lbt_output && !f.has_lbt_atomic_props())
    f = relabel(f, Pnn);

  output_formula_checked(f, class_name[pattern - 1], n);
}

static void
run_jobs()
{
  for (auto& j: jobs)
    {
      int inc = (j.range.max < j.range.min) ? -1 : 1;
      int n = j.range.min;
      for (;;)
	{
	  output_pattern(j.pattern, n);
	  if (n == j.range.max)
	    break;
	  n += inc;
	}
    }
}


int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { options, parse_opt, nullptr, argp_program_doc,
		    children, nullptr, nullptr };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
    exit(err);

  if (jobs.empty())
    error(1, 0, "Nothing to do.  Try '%s --help' for more information.",
	  program_name);

  run_jobs();
  return 0;
}
