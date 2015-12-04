// -*- coding: utf-8 -*-
// Copyright (C) 2015 Laboratoire de Recherche et Développement de
// l'Epita (LRDE).
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

#include "common_trans.hh"
#include <cstring>
#include <cstdlib>
#include <cassert>
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>
#include <iomanip>

#include "error.h"

#include <spot/tl/print.hh>
#include "common_conv.hh"
#include <spot/misc/escape.hh>

// A set of tools for which we know the correct output
static struct shorthands_t
{
  const char* prefix;
  const char* suffix;
}
  shorthands[] = {
    { "lbt", " <%L>%O" },
    { "ltl2ba", " -f %s>%O" },
    { "ltl2dstar", " --output-format=hoa %L %O"},
    { "ltl2tgba", " -H %f>%O" },
    { "ltl3ba", " -f %s>%O" },
    { "ltl3dra", " -f %s>%O" },
    { "modella", " %L %O" },
    { "spin", " -f %s>%O" },
  };

static void show_shorthands()
{
  std::cout
    << ("If a COMMANDFMT does not use any %-sequence, and starts with one of\n"
	"the following words, then the string on the right is appended.\n\n");
  for (auto& s: shorthands)
    std::cout << "  "
	      << std::left << std::setw(12) << s.prefix
	      << s.suffix << '\n';
  std::cout
    << ("\nAny {name} and directory component is skipped for the purpose of\n"
	"matching those prefixes.  So for instance\n"
	"  '{DRA} ~/mytools/ltl2dstar-0.5.2'\n"
	"will changed into\n"
	"  '{DRA} ~/mytools/ltl2dstar-0.5.2 --output-format=hoa %L %O'\n");
}


translator_spec::translator_spec(const char* spec)
  : spec(spec), cmd(spec), name(spec)
{
  if (*cmd == '{')
    {
      // Match the closing '}'
      const char* pos = cmd;
      unsigned count = 1;
      while (*++pos)
	{
	  if (*pos == '{')
	    ++count;
	  else if (*pos == '}')
	    if (!--count)
	      {
		name = strndup(cmd + 1, pos - cmd - 1);
		cmd = pos + 1;
		while (*cmd == ' ' || *cmd == '\t')
		  ++cmd;
		break;
	      }
	}
    }
  // If there is no % in the string, look for a known
  // command from our shorthand list.  If we find it,
  // add the suffix.
  bool allocated = false;
  if (!strchr(cmd, '%'))
    {
      // Skip any leading directory name.
      auto basename = cmd;
      auto pos = cmd;
      while (*pos)
	{
	  if (*pos == '/')
	    basename = pos + 1;
	  else if (*pos == ' ')
	    break;
	  ++pos;
	}
      // Match a shorthand.
      for (auto& p: shorthands)
	{
	  int n = strlen(p.prefix);
	  if (strncmp(basename, p.prefix, n) == 0)
	    {
	      int m = strlen(p.suffix);
	      int q = strlen(cmd);
	      char* tmp = static_cast<char*>(malloc(q + m + 1));
	      strcpy(tmp, cmd);
	      strcpy(tmp + q, p.suffix);
	      cmd = tmp;
	      allocated = true;
	      break;
	    }
	}
    }
  if (!allocated)
    cmd = strdup(cmd);
}

translator_spec::translator_spec(const translator_spec& other)
  : spec(other.spec), cmd(other.cmd), name(other.name)
{
  if (name != spec)
    name = strdup(name);
  if (cmd != spec)
    cmd = strdup(cmd);
}

translator_spec::~translator_spec()
{
  if (name != spec)
    free(const_cast<char*>(name));
  if (cmd != spec)
    free(const_cast<char*>(cmd));
}

std::vector<translator_spec> translators;

void
quoted_string::print(std::ostream& os, const char*) const
{
  spot::quote_shell_string(os, val().c_str());
}

printable_result_filename::printable_result_filename()
{
  val_ = nullptr;
}

printable_result_filename::~printable_result_filename()
{
  delete val_;
}

void printable_result_filename::reset(unsigned n)
{
  translator_num = n;
}

void printable_result_filename::cleanup()
{
  delete val_;
  val_ = nullptr;
}

void
printable_result_filename::print(std::ostream& os, const char*) const
{
  char prefix[30];
  snprintf(prefix, sizeof prefix, "lcr-o%u-", translator_num);
  const_cast<printable_result_filename*>(this)->val_ =
    spot::create_tmpfile(prefix);
  spot::quote_shell_string(os, val()->name());
}


translator_runner::translator_runner(spot::bdd_dict_ptr dict,
				     bool no_output_allowed)
  : dict(dict)
{
  declare('f', &string_ltl_spot);
  declare('s', &string_ltl_spin);
  declare('l', &string_ltl_lbt);
  declare('w', &string_ltl_wring);
  declare('F', &filename_ltl_spot);
  declare('S', &filename_ltl_spin);
  declare('L', &filename_ltl_lbt);
  declare('W', &filename_ltl_wring);
  declare('D', &output);
  declare('H', &output);
  declare('N', &output);
  declare('T', &output);
  declare('O', &output);

  size_t s = translators.size();
  assert(s);
  for (size_t n = 0; n < s; ++n)
    {
      // Check that each translator uses at least one input and
      // one output.
      std::vector<bool> has(256);
      const translator_spec& t = translators[n];
      scan(t.cmd, has);
      if (!(has['f'] || has['s'] || has['l'] || has['w']
	    || has['F'] || has['S'] || has['L'] || has['W']))
	error(2, 0, "no input %%-sequence in '%s'.\n       Use "
	      "one of %%f,%%s,%%l,%%w,%%F,%%S,%%L,%%W to indicate how "
	      "to pass the formula.", t.spec);
      if (!no_output_allowed
	  && !(has['O'] ||
	       // backward-compatibility
	       has['D'] || has['N'] || has['T'] || has['H']))
	error(2, 0, "no output %%-sequence in '%s'.\n      Use  "
	      "%%O to indicate where the automaton is output.",
	      t.spec);
      // Remember the %-sequences used by all translators.
      prime(t.cmd);
    }
}

void
translator_runner::string_to_tmp(std::string& str, unsigned n,
				 std::string& tmpname)
{
  char prefix[30];
  snprintf(prefix, sizeof prefix, "lcr-i%u-", n);
  spot::open_temporary_file* tmpfile = spot::create_open_tmpfile(prefix);
  tmpname = tmpfile->name();
  int fd = tmpfile->fd();
  ssize_t s = str.size();
  if (write(fd, str.c_str(), s) != s
      || write(fd, "\n", 1) != 1)
    error(2, errno, "failed to write into %s", tmpname.c_str());
  tmpfile->close();
}

const std::string&
translator_runner::formula() const
{
  // Pick the most readable format we have...
  if (!string_ltl_spot.val().empty())
    return string_ltl_spot;
  if (!string_ltl_spin.val().empty())
    return string_ltl_spin;
  if (!string_ltl_wring.val().empty())
    return string_ltl_wring;
  if (!string_ltl_lbt.val().empty())
    return string_ltl_lbt;
  SPOT_UNREACHABLE();
  return string_ltl_spot;
}

void
translator_runner::round_formula(spot::formula f, unsigned serial)
{
  if (has('f') || has('F'))
    string_ltl_spot = spot::str_psl(f, true);
  if (has('s') || has('S'))
    string_ltl_spin = spot::str_spin_ltl(f, true);
  if (has('l') || has('L'))
    string_ltl_lbt = spot::str_lbt_ltl(f);
  if (has('w') || has('W'))
    string_ltl_wring = spot::str_wring_ltl(f);
  if (has('F'))
    string_to_tmp(string_ltl_spot, serial, filename_ltl_spot);
  if (has('S'))
    string_to_tmp(string_ltl_spin, serial, filename_ltl_spin);
  if (has('L'))
    string_to_tmp(string_ltl_lbt, serial, filename_ltl_lbt);
  if (has('W'))
    string_to_tmp(string_ltl_wring, serial, filename_ltl_wring);
}



volatile bool timed_out = false;
unsigned timeout_count = 0;

static unsigned timeout = 0;
#if ENABLE_TIMEOUT
static volatile int alarm_on = 0;
static int child_pid = -1;

static void
sig_handler(int sig)
{
  if (child_pid == 0)
    error(2, 0, "received signal %d before starting child", sig);

  if (sig == SIGALRM && alarm_on)
    {
      timed_out = true;
      if (--alarm_on)
	{
	  // Send SIGTERM to children.
	  kill(-child_pid, SIGTERM);
	  // Try again later if it didn't work.  (alarm() will be reset
	  // if it did work and the call to wait() returns)
	  alarm(2);
	}
      else
	{
	  // After a few gentle tries, really kill that child.
	  kill(-child_pid, SIGKILL);
	}
    }
  else
    {
      // forward signal
      kill(-child_pid, sig);
      // cleanup files
      spot::cleanup_tmpfiles();
      // and die verbosely
      error(2, 0, "received signal %d", sig);
    }
}

void
setup_sig_handler()
{
  struct sigaction sa;
  sa.sa_handler = sig_handler;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_RESTART; // So that wait() doesn't get aborted by SIGALRM.
  sigaction(SIGALRM, &sa, nullptr);
  // Catch termination signals, so we can kill the subprocess.
  sigaction(SIGHUP, &sa, nullptr);
  sigaction(SIGINT, &sa, nullptr);
  sigaction(SIGQUIT, &sa, nullptr);
  sigaction(SIGTERM, &sa, nullptr);
}

int
exec_with_timeout(const char* cmd)
{
  int status;

  timed_out = false;

  child_pid = fork();
  if (child_pid == -1)
    error(2, errno, "failed to fork()");

  if (child_pid == 0)
    {
      setpgid(0, 0);
      execlp("sh", "sh", "-c", cmd, nullptr);
      error(2, errno, "failed to run 'sh'");
      // never reached
      return -1;
    }
  else
    {
      alarm(timeout);
      // Upon SIGALRM, the child will receive up to 3
      // signals: SIGTERM, SIGTERM, SIGKILL.
      alarm_on = 3;
      int w = waitpid(child_pid, &status, 0);
      alarm_on = 0;

      if (w == -1)
	error(2, errno, "error during wait()");

      alarm(0);
    }
  return status;
}
#endif // ENABLE_TIMEOUT

enum {
  OPT_LIST = 1,
};
static const argp_option options[] =
{
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Specifying translators to call:", 2 },
    { "translator", 't', "COMMANDFMT", 0,
      "register one translator to call", 0 },
    { "timeout", 'T', "NUMBER", 0, "kill translators after NUMBER seconds", 0 },
    { "list-shorthands", OPT_LIST, nullptr, 0,
      "list availabled shorthands to use in COMMANDFMT", 0},
    /**************************************************/
    { nullptr, 0, nullptr, 0,
      "COMMANDFMT should specify input and output arguments using the "
      "following character sequences:", 3 },
    { "%f,%s,%l,%w", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the formula as a (quoted) string in Spot, Spin, LBT, or Wring's syntax",
      0 },
    { "%F,%S,%L,%W", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the formula as a file in Spot, Spin, LBT, or Wring's syntax", 0 },
    { "%O", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the automaton is output in HOA, never claim, LBTT, or ltl2dstar's "
      "format", 0 },
    { "%%", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE, "a single %", 0 },
    { nullptr, 0, nullptr, 0,
      "If either %l, %L, or %T are used, any input formula that does "
      "not use LBT-style atomic propositions (i.e. p0, p1, ...) will be "
      "relabeled automatically.\n"
      "Furthermore, if COMMANDFMT has the form \"{NAME}CMD\", then only CMD "
      "will be passed to the shell, and NAME will be used to name the tool "
      "in the output.", 4 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
};

static int parse_opt_trans(int key, char* arg, struct argp_state*)
{
  switch (key)
    {
    case 't':
      translators.push_back(arg);
      break;
    case 'T':
      timeout = to_pos_int(arg);
#if !ENABLE_TIMEOUT
      std::cerr << "warning: setting a timeout is not supported "
		<< "on your platform" << std::endl;
#endif
      break;
    case OPT_LIST:
      show_shorthands();
      exit(0);
    default:
      return ARGP_ERR_UNKNOWN;
    }
  return 0;
}

const struct argp trans_argp = { options, parse_opt_trans, nullptr, nullptr,
				 nullptr, nullptr, nullptr };
