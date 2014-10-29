// -*- coding: utf-8 -*-
// Copyright (C) 2014 Laboratoire de Recherche et
// Développement de l'Epita (LRDE).
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

#include "bin/common_sys.hh"
#include "bin/common_setup.hh"
#include "bin/common_finput.hh"
#include "bin/common_output.hh"
#include "tgbaalgos/translate.hh"
#include "tgbaalgos/stutter_invariance.hh"
#include "tgbaalgos/dupexp.hh"
#include "ltlast/allnodes.hh"
#include "ltlvisit/apcollect.hh"
#include "ltlvisit/length.hh"
#include "misc/timer.hh"
#include <argp.h>
#include "error.h"

const char argp_program_doc[] ="";

const struct argp_child children[] =
  {
    { &finput_argp, 0, 0, 1 },
    { &output_argp, 0, 0, -20 },
    { &misc_argp, 0, 0, -1 },
    { 0, 0, 0, 0 }
  };

namespace
{
  class stut_processor: public job_processor
  {
  public:
    spot::translator& trans;
    std::string formula;

    stut_processor(spot::translator& trans) : trans(trans)
    {
    }

    int
    process_string(const std::string& input,
                   const char* filename, int linenum)
    {
      formula = input;
      return job_processor::process_string(input, filename, linenum);
    }

    int
    process_formula(const spot::ltl::formula* f,
                    const char*, int)
    {
      const spot::ltl::formula* nf =
	spot::ltl::unop::instance(spot::ltl::unop::Not,
				  f->clone());
      spot::tgba_digraph_ptr a = trans.run(f);
      spot::tgba_digraph_ptr na = trans.run(nf);
      unsigned num_states = a->num_states();
      spot::ltl::atomic_prop_set* ap = spot::ltl::atomic_prop_collect(f);
      bdd apdict = spot::ltl::atomic_prop_collect_as_bdd(f, a);
      bool res;
      bool prev = true;
      for (char algo = '1'; algo <= '8'; ++algo)
        {
          // set SPOT_STUTTER_CHECK environment variable
          char algostr[2] = { 0 };
          algostr[0] = algo;
          setenv("SPOT_STUTTER_CHECK", algostr, true);

          spot::stopwatch sw;
          auto dup_a = std::make_shared<spot::tgba_digraph>(a);
          auto dup_na = std::make_shared<spot::tgba_digraph>(na);

          sw.start();
          res = spot::is_stutter_invariant(std::move(dup_a),
                                           std::move(dup_na), apdict);
          const double time = sw.stop();

          std::cout << formula << ", " << algo << ", " << ap->size() << ", "
		    << num_states << ", " << res << ", " << time * 1000000 << std::endl;

          if (algo > '1')
            assert(res == prev);
          prev = res;
        }
      f->destroy();
      nf->destroy();
      delete(ap);
      return 0;
    }
  };
}

int
main(int argc, char** argv)
{
  setup(argv);

  const argp ap = { 0, 0, "[FILENAME[/COL]...]",
                    argp_program_doc, children, 0, 0 };

  if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, 0, 0))
    exit(err);

  spot::translator trans;
  stut_processor processor(trans);
  if (processor.run())
    return 2;

  return 0;
}
