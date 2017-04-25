// -*- coding: utf-8 -*-
// Copyright (C) 2017 Laboratoire de Recherche et Developpement de
// l'EPITA (LRDE).
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

#pragma once

#include <spot/tl/formula.hh>


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
//   booktitle        = {Proceedings of the 13th International Conference on
//                   Computer Aided Verification (CAV'01)},
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
//                   Model Checking of Software (SPIN'07)},
//   pages = {149--167},
//   year = {2007},
//   volume = {4595},
//   series = {Lecture Notes in Computer Science},
//   publisher = {Springer-Verlag}
// }
//
// @InProceedings{dwyer.98.fmsp,
//   author = {Matthew B. Dwyer and George S. Avrunin and James C. Corbett},
//   title         = {Property Specification Patterns for Finite-state
//                   Verification},
//   booktitle     = {Proceedings of the 2nd Workshop on Formal Methods in
//                   Software Practice (FMSP'98)},
//   publisher     = {ACM Press},
//   address       = {New York},
//   editor        = {Mark Ardis},
//   month         = mar,
//   year          = {1998},
//   pages         = {7--15}
// }
//
// @InProceedings{etessami.00.concur,
//   author = {Kousha Etessami and Gerard J. Holzmann},
//   title = {Optimizing {B\"u}chi Automata},
//   booktitle = {Proceedings of the 11th International Conference on
//                Concurrency Theory (Concur'00)},
//   pages = {153--167},
//   year = {2000},
//   editor = {C. Palamidessi},
//   volume = {1877},
//   series = {Lecture Notes in Computer Science},
//   address = {Pennsylvania, USA},
//   publisher = {Springer-Verlag}
// }
//
// @InProceedings{somenzi.00.cav,
//   author = {Fabio Somenzi and Roderick Bloem},
//   title = {Efficient {B\"u}chi Automata for {LTL} Formul{\ae}},
//   booktitle = {Proceedings of the 12th International Conference on
//                Computer Aided Verification (CAV'00)},
//   pages = {247--263},
//   year = {2000},
//   volume = {1855},
//   series = {Lecture Notes in Computer Science},
//   address = {Chicago, Illinois, USA},
//   publisher = {Springer-Verlag}
// }
//
// @InProceedings{tabakov.10.rv,
//   author = {Deian Tabakov and Moshe Y. Vardi},
//   title = {Optimized Temporal Monitors for {SystemC}},
//   booktitle = {Proceedings of the 1st International Conference on Runtime
//		  Verification (RV'10)},
//   pages = {436--451},
//   year = 2010,
//   volume = {6418},
//   series = {Lecture Notes in Computer Science},
//   month = nov,
//   publisher = {Springer}
// }
//
// @InProceedings{kupferman.10.mochart,
//   author = {Orna Kupferman and And Rosenberg},
//   title = {The Blow-Up in Translating LTL do Deterministic Automata},
//   booktitle = {Proceedings of the 6th International Workshop on Model
//                Checking and Artificial Intelligence (MoChArt 2010)},
//   pages = {85--94},
//   year = 2011,
//   volume = {6572},
//   series = {Lecture Notes in Artificial Intelligence},
//   month = nov,
//   publisher = {Springer}
// }
//
// @techreport{holevek.04.tr,
//    title = {Verification Results in {Liberouter} Project},
//    author = {J. Hole\v{c}ek and T. Kratochv\'ila and V. \v{R}eh\'ak
//              and D. \v{S}afr\'anek and P. \v{S}ime\v{c}ek},
//    month = {September},
//    year = 2004,
//    number = 03,
//    institution = {CESNET}
// }
//
// @InProceedings{pelanek.07.spin,
//   author = {Radek Pel\'{a}nek},
//   title = {{BEEM}: benchmarks for explicit model checkers},
//   booktitle = {Proceedings of the 14th international SPIN conference on
//     Model checking software},
//   year = 2007,
//   pages = {263--267},
//   numpages = {5},
//   volume = {4595},
//   series = {Lecture Notes in Computer Science},
//   publisher = {Springer-Verlag}
// }

namespace spot
{
  namespace gen
  {
    enum ltl_pattern {
      FIRST_CLASS = 256,
      AND_F = FIRST_CLASS,
      AND_FG,
      AND_GF,
      CCJ_ALPHA,
      CCJ_BETA,
      CCJ_BETA_PRIME,
      DAC_PATTERNS,
      EH_PATTERNS,
      GH_Q,
      GH_R,
      GO_THETA,
      HKRSS_PATTERNS,
      KR_N,
      KR_NLOGN,
      KV_PSI,
      OR_FG,
      OR_G,
      OR_GF,
      P_PATTERNS,
      R_LEFT,
      R_RIGHT,
      RV_COUNTER,
      RV_COUNTER_CARRY,
      RV_COUNTER_CARRY_LINEAR,
      RV_COUNTER_LINEAR,
      SB_PATTERNS,
      TV_F1,
      TV_F2,
      TV_G1,
      TV_G2,
      TV_UU,
      U_LEFT,
      U_RIGHT,
      LAST_CLASS,
    };

    /// \brief generate an LTL from a known pattern
    ///
    /// The pattern is specified using one value from the ltl_pattern
    /// enum.  See the man page of the `genltl` binary for a
    /// description of those pattern, and bibliographic references.
    SPOT_API formula genltl(ltl_pattern pattern, int n);

    /// \brief convert an ltl_pattern value into a name
    ///
    /// The returned name is suitable to be used as an option
    /// key for the genltl binary.
    SPOT_API const char* ltl_pattern_name(ltl_pattern pattern);
  }
}
