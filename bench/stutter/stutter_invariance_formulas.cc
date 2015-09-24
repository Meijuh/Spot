// -*- coding: utf-8 -*-
// Copyright (C) 2014, 2015 Laboratoire de Recherche et
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
#include "twaalgos/translate.hh"
#include "twaalgos/stutter.hh"
#include "twaalgos/dupexp.hh"
#include "twaalgos/stats.hh"
#include "ltlvisit/apcollect.hh"
#include "ltlvisit/length.hh"
#include "misc/timer.hh"
#include <argp.h>

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
    spot::stat_printer stats;

    stut_processor(spot::translator& trans) :
      trans(trans), stats(std::cout, "%s,%t,%e,%S,%n,")
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
    process_formula(spot::ltl::formula f, const char*, int)
    {
      spot::twa_graph_ptr a = trans.run(f);
      spot::twa_graph_ptr na = trans.run(spot::ltl::formula::Not(f));
      spot::ltl::atomic_prop_set* ap = spot::ltl::atomic_prop_collect(f);
      bdd apdict = spot::ltl::atomic_prop_collect_as_bdd(f, a);

      std::cout << formula << ',' << ap->size() << ',';
      stats.print(a);
      stats.print(na);

      bool prev = true;
      for (int algo = 1; algo <= 8; ++algo)
        {
          auto dup_a = spot::make_twa_graph(a, spot::twa::prop_set::all());
          auto dup_na = spot::make_twa_graph(na, spot::twa::prop_set::all());

          spot::stopwatch sw;
          sw.start();
          bool res = spot::is_stutter_invariant(std::move(dup_a),
						std::move(dup_na),
						apdict, algo);
          auto time = sw.stop();
	  std::cout<< time << ',';

          if (algo > 1 && prev != res)
	    {
	      std::cerr << "\nerror: algorithms " << algo - 1
			<< " and " << algo << " disagree on formula "
			<< formula << "\n";
	      exit(2);
	    }
          prev = res;
        }
      std::cout << prev << '\n';
      delete ap;
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
