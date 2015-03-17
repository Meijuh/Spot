# -*- coding: utf-8 -*-
# Copyright (C) 2014, 2015  Laboratoire de
# Recherche et Développement de l'Epita (LRDE).
#
# This file is part of Spot, a model checking library.
#
# Spot is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# Spot is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

from spot_impl import *
import subprocess
import sys

_bdd_dict = make_bdd_dict()

def _ostream_to_svg(ostr):
    dotty = subprocess.Popen(['dot', '-Tsvg'],
                             stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE)
    dotty.stdin.write(ostr.str().encode('utf-8'))
    res = dotty.communicate()
    return res[0].decode('utf-8')

def _render_automaton_as_svg(a, opt=None):
    ostr = ostringstream()
    dotty_reachable(ostr, a, opt)
    return _ostream_to_svg(ostr)

tgba._repr_svg_ = _render_automaton_as_svg

def _render_formula_as_svg(a):
    # Load the SVG function only if we need it. This way the bindings
    # can still be used outside of IPython if IPython is not
    # installed.
    from IPython.display import SVG
    ostr = ostringstream()
    dotty(ostr, a)
    return SVG(_ostream_to_svg(ostr))

def _render_tgba_as_svg(a, opt=None):
    # Load the SVG function only if we need it. This way the bindings
    # can still be used outside of IPython if IPython is not
    # installed.
    from IPython.display import SVG
    return SVG(_render_automaton_as_svg(a, opt))
tgba.show = _render_tgba_as_svg

def _formula_str_ctor(self, str):
    self.this = parse_formula(str)

def _formula_to_str(self, format = 'spot'):
    if format == 'spot':
        return to_string(self)
    elif format == 'spin':
        return to_spin_string(self)
    elif format == 'utf8':
        return to_utf8_string(self)
    elif format == 'lbt':
        return to_lbt_string(self)
    elif format == 'wring':
        return to_wring_string(self)
    elif format == 'latex':
        return to_latex_string(self)
    elif format == 'sclatex':
        return to_sclatex_string(self)
    else:
        raise ValueError("unknown string format: " + format)

formula.__init__ = _formula_str_ctor
formula.to_str = _formula_to_str
formula.show_ast = _render_formula_as_svg

def translate(formula, output='tgba', pref='small', level='high',
              complete=False):
    """Translate a formula into an automaton.

    Keep in mind that pref expresses just a preference that may not be
    satisfied.

    Keyword arguments:
    output -- the type of automaton to build ('tgba', 'ba', 'monitor')
    pref -- prefered characteristic of the produced automaton
            ('small', 'deterministic', 'any')
    level -- level of optimizations ('low', 'medium', 'high')
    complete -- whether to produce a complete automaton (True, False)
    """
    if type(formula) == str:
        formula = parse_formula(formula)

    a = translator()

    if type(output) == str:
        output_ = output.lower()
        if output_ == 'tgba':
            output = postprocessor.TGBA
        elif output_ == 'ba':
            output = postprocessor.BA
        elif output_.startswith('mon'):
            output = postprocessor.Monitor
        else:
            raise ValueError("unknown output type: " + output)
    a.set_type(output)

    if complete:
        complete = postprocessor.Complete
    else:
        complete = 0

    if type(pref) == str:
        pref_ = pref.lower()
        if pref_.startswith('sm'):
            pref = postprocessor.Small
        elif pref_.startswith('det'):
            pref = postprocessor.Deterministic
        elif pref_ == 'any':
            pref = postprocessor.Any
        else:
            raise ValueError("unknown output preference: " + pref)
    a.set_pref(pref | complete)

    if type(level) == str:
        level_ = level.lower()
        if level_ == 'high':
            level = postprocessor.High
        elif level_.startswith('med'):
            level = postprocessor.Medium
        elif level_ == 'low':
            level = postprocessor.Low
        else:
            raise ValueError("unknown optimization level: " + level)
    a.set_level(level)

    return a.run(formula)

formula.translate = translate

# Wrapper around a formula iterator to which we add some methods of formula
# (using _addfilter and _addmap), so that we can write things like
# formulas.simplify().is_X_free().
class formulaiterator:
    def __init__(self, formulas):
        self._formulas = formulas

    def __iter__(self):
        return self

    def __next__(self):
        return next(self._formulas)

# fun shoud be a predicate and should be a method of formula.
# _addfilter adds this predicate as a filter whith the same name in
# formulaiterator.
def _addfilter(fun):
    def filtf(self, *args, **kwargs):
        it = filter(lambda f: getattr(f, fun)(*args, **kwargs), self)
        return formulaiterator(it)
    def nfiltf(self, *args, **kwargs):
        it = filter(lambda f: not getattr(f, fun)(*args, **kwargs), self)
        return formulaiterator(it)
    setattr(formulaiterator, fun, filtf)
    if fun[:3] == 'is_':
        notfun = fun[:3] + 'not_' + fun[3:]
    elif fun[:4] == 'has_':
        notfun = fun[:4] + 'no_' + fun[4:]
    else:
        notfun = 'not_' + fun
    setattr(formulaiterator, fun, filtf)
    setattr(formulaiterator, notfun, nfiltf)

# fun should be a function taking a formula as its first parameter and returning
# a formula.
# _addmap adds this function as a method of formula and formulaiterator.
def _addmap(fun):
    def mapf(self, *args, **kwargs):
        return formulaiterator(map(lambda f: getattr(f, fun)(*args, **kwargs),
self))
    setattr(formula, fun, lambda self, *args, **kwargs: globals()[fun](self,
    *args, **kwargs))
    setattr(formulaiterator, fun, mapf)

def randltl(ap, n = -1, **kwargs):
    """Generate random formulas.

    Returns a random formula iterator.

    ap: the number of atomic propositions used to generate random formulas.

    n: number of formulas to generate, or unbounded if n < 0.

    **kwargs:
    seed: seed for the random number generator (0).
    output: can be 'ltl', 'psl', 'bool' or 'sere' ('ltl').
    allow_dups: allow duplicate formulas (False).
    tree_size: tree size of the formulas generated, before mandatory
    simplifications (15)
    boolean_priorities: set priorities for Boolean formulas.
    ltl_priorities: set priorities for LTL formulas.
    sere_priorities: set priorities for SERE formulas.
    dump_priorities: show current priorities, do not generate any formula.
    simplify:
      0           No rewriting
      1           basic rewritings and eventual/universal rules
      2           additional syntactic implication rules
      3 (default) better implications using containment
    """
    opts = option_map()
    output_map = {
        "ltl" : OUTPUTLTL,
        "psl" : OUTPUTPSL,
        "bool" : OUTPUTBOOL,
        "sere" : OUTPUTSERE
    }

    if isinstance(ap, list):
        aprops = atomic_prop_set()
        e = default_environment.instance()
        for elt in ap:
            aprops.insert(is_atomic_prop(e.require(elt)))
        ap = aprops
    ltl_priorities = kwargs.get("ltl_priorities", None)
    sere_priorities = kwargs.get("sere_priorities", None)
    boolean_priorities = kwargs.get("boolean_priorities", None)
    output = output_map[kwargs.get("output", "ltl")]
    opts.set("output", output)
    opts.set("seed", kwargs.get("seed", 0))
    tree_size = kwargs.get("tree_size", 15)
    if isinstance(tree_size, tuple):
        tree_size_min, tree_size_max = tree_size
    else:
        tree_size_min = tree_size_max = tree_size
    opts.set("tree_size_min", tree_size_min)
    opts.set("tree_size_max", tree_size_max)
    opts.set("unique", not kwargs.get("allow_dups", False))
    opts.set("wf", kwargs.get("weak_fairness", False))
    simpl_level = kwargs.get("simplify", 0)
    if simpl_level > 3 or simpl_level < 0:
        sys.stderr.write('invalid simplification level: ' + simpl_level)
        return
    opts.set("simplification_level", simpl_level)

    rg = randltlgenerator(ap, opts, ltl_priorities, sere_priorities,
        boolean_priorities)

    dump_priorities = kwargs.get("dump_priorities", False)
    if dump_priorities:
        dumpstream = ostringstream()
        if output == OUTPUTLTL:
            print('Use argument ltl_priorities=STRING to set the following ' \
                    'LTL priorities:\n')
            rg.dump_ltl_priorities(dumpstream)
            print(dumpstream.str())
        elif output == OUTPUTBOOL:
            print('Use argument boolean_priorities=STRING to set the ' \
                    'following Boolean formula priorities:\n')
            rg.dump_bool_priorities(dumpstream)
            print(dumpstream.str())
        elif output == OUTPUTPSL or output == OUTPUTSERE:
            if output != OUTPUTSERE:
                print('Use argument ltl_priorities=STRING to set the following ' \
                        'LTL priorities:\n')
                rg.dump_psl_priorities(dumpstream)
                print(dumpstream.str())
            print('Use argument sere_priorities=STRING to set the following ' \
                    'SERE priorities:\n')
            rg.dump_sere_priorities(dumpstream)
            print(dumpstream.str())
            print('Use argument boolean_priorities=STRING to set the ' \
                    'following Boolean formula priorities:\n')
            rg.dump_sere_bool_priorities(dumpstream)
            print(dumpstream.str())
        else:
            sys.stderr.write("internal error: unknown type of output")
        return

    def _randltlgenerator(rg):
        i = 0
        while i != n:
            f = rg.next()
            if f is None:
                sys.stderr.write("Warning: could not generate a new unique formula " \
                "after " + str(MAX_TRIALS) + " trials.\n")
                yield None
            else:
                yield f
                i += 1
    return formulaiterator(_randltlgenerator(rg))

def simplify(f, **kwargs):
    level = kwargs.get('level', None)
    if level is not None:
        return ltl_simplifier(ltl_simplifier_options(level)).simplify(f)

    basics = kwargs.get('basics', True)
    synt_impl = kwargs.get('synt_impl', True)
    event_univ = kwargs.get('event_univ', True)
    containment_checks = kwargs.get('containment_checks', False)
    containment_checks_stronger = kwargs.get('containment_checks_stronger', False)
    nenoform_stop_on_boolean = kwargs.get('nenoform_stop_on_boolean', False)
    reduce_size_strictly = kwargs.get('reduce_size_strictly', False)
    boolean_to_isop = kwargs.get('boolean_to_isop', False)
    favor_event_univ = kwargs.get('favor_event_univ', False)

    simp_opts = ltl_simplifier_options(basics,
                                       synt_impl,
                                       event_univ,
                                       containment_checks,
                                       containment_checks_stronger,
                                       nenoform_stop_on_boolean,
                                       reduce_size_strictly,
                                       boolean_to_isop,
                                       favor_event_univ)
    return ltl_simplifier(simp_opts).simplify(f)

for fun in dir(formula):
    if (callable(getattr(formula, fun)) and
        (fun[:3] == 'is_' or fun[:4] == 'has_')):
        _addfilter(fun)

for fun in ['remove_x', 'get_literal', 'relabel', 'relabel_bse',
            'simplify', 'unabbreviate_ltl']:
    _addmap(fun)
