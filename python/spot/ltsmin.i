// -*- coding: utf-8 -*-
// Copyright (C) 2016 Laboratoire de Recherche et Développement de
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

%{
  // Workaround for SWIG 2.0.2 using ptrdiff_t but not including cstddef.
  // It matters with g++ 4.6.
#include <cstddef>
%}

%module(package="spot", director="1") ltsmin

%include "std_string.i"
%include "std_set.i"
%include "std_shared_ptr.i"

%shared_ptr(spot::bdd_dict)
%shared_ptr(spot::twa)
%shared_ptr(spot::kripke)
%shared_ptr(spot::fair_kripke)

%{
#include <spot/ltsmin/ltsmin.hh>
using namespace spot;
%}

%import(module="spot.impl") <spot/misc/common.hh>
%import(module="spot.impl") <spot/twa/bdddict.hh>
%import(module="spot.impl") <spot/twa/twa.hh>
%import(module="spot.impl") <spot/tl/formula.hh>
%import(module="spot.impl") <spot/tl/apcollect.hh>
%import(module="spot.impl") <spot/kripke/fairkripke.hh>
%import(module="spot.impl") <spot/kripke/kripke.hh>

%exception {
  try {
    $action
  }
  catch (const std::runtime_error& e)
  {
    SWIG_exception(SWIG_RuntimeError, e.what());
  }
}

namespace std {
  %template(atomic_prop_set) set<spot::formula>;
}

%rename(model) spot::ltsmin_model;
%rename(kripke_raw) spot::ltsmin_model::kripke;
%include <spot/ltsmin/ltsmin.hh>

%pythoncode %{
import spot

def load(filename):
  return model.load(filename)

@spot._extend(model)
class model:
  def kripke(self, ap_set, dict=spot._bdd_dict,
	      dead=spot.formula_ap('dead'),
	      compress=2):
    s = spot.atomic_prop_set()
    for ap in ap_set:
      s.insert(spot.formula_ap(ap))
    return self.kripke_raw(s, dict, dead, compress)

  def info(self):
    res = {}
    ss = self.state_size()
    res['state_size'] = ss
    res['variables'] = [(self.state_variable_name(i),
			 self.state_variable_type(i)) for i in range(ss)]
    tc = self.type_count()
    res['types'] = [(self.type_name(i),
		     [self.type_value_name(i, j)
		      for j in range(self.type_value_count(i))])
		     for i in range(tc)]
    return res

  def __repr__(self):
    res = "ltsmin model with the following variables:\n";
    info = self.info()
    for (var, t) in info['variables']:
      res += '  ' + var + ': ';
      type, vals = info['types'][t]
      if vals:
        res += str(vals)
      else:
        res += type
      res += '\n';
    return res

# Load IPython specific support if we can.
try:
    # Load only if we are running IPython.
    __IPYTHON__

    from IPython.core.magic import (Magics, magics_class, line_cell_magic)
    from IPython.core.magic_arguments \
        import (argument, magic_arguments, parse_argstring)
    import os
    import tempfile
    import sys
    import shutil
    try:
        import ipywidgets as widgets
    except ImportError:
        pass

    # This class provides support for %%dve model description
    @magics_class
    class EditDVE(Magics):

        @line_cell_magic
        def dve(self, line, cell=None):
            try:
                # DiViNe prefers when files are in the current directory
                # so write cell into local file
                t = tempfile.NamedTemporaryFile(dir=os.getcwd())
                filename = t.name + '.dve'
                f = open(filename,"w")
                f.write(cell)
                f.close()

                # Then compile and unlink temporary files
                import subprocess
                out=""
                self.shell.user_ns[line] = None
                out = subprocess.check_call(['divine', 'compile',
                                       '--ltsmin', filename])
                os.unlink(filename)
                os.unlink(filename + '.cpp')
                self.shell.user_ns[line] = load(filename + '2C')
                os.unlink(filename + '2C')
            except Exception as error:
                try:
                    os.unlink(filename)
                    os.unlink(filename + '.cpp')
                finally:
                    if out != "":
                        raise RuntimeError(out) from error
                    raise error

        @line_cell_magic
        def require(self, line, cell=None):
            if line != "divine":
                print ("Unknown" + line, file=sys.stderr)
                sys.exit(77)
            if cell != None:
                print ("No support for Cell magic command")
                sys.exit(77)
            if shutil.which("divine") == None:
                print ("divine not available", file=sys.stderr)
                sys.exit(77)
            import subprocess
            out = subprocess.check_output(['divine', 'compile',
                                           '--help'], stderr=subprocess.STDOUT)
            if b'LTSmin' not in out:
                print ("divine available but no support for LTSmin",
		       file=sys.stderr)
                sys.exit(77)

    ip = get_ipython()
    ip.register_magics(EditDVE)

except (ImportError, NameError):
    pass
%}
