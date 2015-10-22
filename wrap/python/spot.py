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


import sys


if sys.hexversion < 0x03030000:
    sys.exit("This module requires Python 3.3 or newer")


from spot_impl import *
import subprocess
import os
import signal
from functools import lru_cache


def _extend(*classes):
    """
    Decorator that extends all the given classes with the contents
    of the class currently being defined.
    """
    def wrap(this):
        for cls in classes:
            for (name, val) in this.__dict__.items():
                if name not in ('__dict__', '__weakref__') \
                   and not (name == '__doc__' and val is None):
                    setattr(cls, name, val)
        return classes[0]
    return wrap


def setup(**kwargs):
    """Configure Spot for fancy display.

    This is manly useful in Jupyter/IPython.

    Note that this function needs to be called before any automaton is
    displayed.  Afterwards it will have no effect (you should restart
    Python, or the Jupyter/IPython Kernel).

    Parameters
    ----------
    bullets : bool
        whether to display acceptance conditions as UTF8 bullets
        (default: True)
    fillcolor : str
        the color to use for states (default: '#ffffaa')
    size : str
        the width and height of the GraphViz output in inches
        (default: '10.2,5')
    font : str
        the font to use in the GraphViz output (default: 'Lato')
    """
    import os

    s = ('size="{}" node[style=filled,fillcolor="{}"] '
         'edge[arrowhead=vee, arrowsize=.7]')
    os.environ['SPOT_DOTEXTRA'] = s.format(kwargs.get('size', '10.2,5'),
                                           kwargs.get('fillcolor', '#ffffaa'))

    bullets = 'B' if kwargs.get('bullets', True) else ''
    d = 'rf({})'.format(kwargs.get('font', 'Lato')) + bullets
    os.environ['SPOT_DOTDEFAULT'] = d


# In version 3.0.2, Swig puts strongly typed enum in the main
# namespace without prefixing them.  Latter versions fix this.  So we
# can remove for following hack once 3.0.2 is no longer used in our
# build farm.
if 'op_ff' not in globals():
    for i in ('ff', 'tt', 'eword', 'ap', 'Not', 'X', 'F', 'G',
              'Closure', 'NegClosure', 'NegClosureMarked',
              'Xor', 'Implies', 'Equiv', 'U', 'R', 'W', 'M',
              'EConcat', 'EConcatMarked', 'UConcat', 'Or',
              'OrRat', 'And', 'AndRat', 'AndNLM', 'Concat',
              'Fusion', 'Star', 'FStar'):
        globals()['op_' + i] = globals()[i]
        del globals()[i]


# Global BDD dict so that we do not have to create one in user code.
_bdd_dict = make_bdd_dict()


# Add a small LRU cache so that when we display automata into a
# interactive widget, we avoid some repeated calls to dot for
# identical inputs.
@lru_cache(maxsize=64)
def _str_to_svg(str):
    dotty = subprocess.Popen(['dot', '-Tsvg'],
                             stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE)
    dotty.stdin.write(str)
    res = dotty.communicate()
    return res[0].decode('utf-8')


def _ostream_to_svg(ostr):
    return _str_to_svg(ostr.str().encode('utf-8'))


@_extend(twa, ta)
class twa:
    def _repr_svg_(self, opt=None):
        """Output the automaton as SVG"""
        ostr = ostringstream()
        print_dot(ostr, self, opt)
        return _ostream_to_svg(ostr)

    def show(self, opt=None):
        """Display the automaton as SVG, in the IPython/Jupyter notebook"""
        # Load the SVG function only if we need it. This way the
        # bindings can still be used outside of IPython if IPython is
        # not installed.
        from IPython.display import SVG
        return SVG(self._repr_svg_(opt))


@_extend(twa)
class twa:
    def to_str(a, format='hoa', opt=None):
        format = format.lower()
        if format == 'hoa':
            ostr = ostringstream()
            print_hoa(ostr, a, opt)
            return ostr.str()
        if format == 'dot':
            ostr = ostringstream()
            print_dot(ostr, a, opt)
            return ostr.str()
        if format == 'spin':
            ostr = ostringstream()
            print_never_claim(ostr, a, opt)
            return ostr.str()
        if format == 'lbtt':
            ostr = ostringstream()
            print_lbtt(ostr, a, opt)
            return ostr.str()
        raise ValueError("unknown string format: " + format)

    def save(a, filename, format='hoa', opt=None, append=False):
        with open(filename, 'a' if append else 'w') as f:
            s = a.to_str(format, opt)
            f.write(s)
            if s[-1] != '\n':
                f.write('\n')
        return a


@_extend(formula)
class formula:
    def __init__(self, str):
        """Parse the given string to create a formula."""
        self.this = parse_formula(str)

    def show_ast(self):
        """Display the syntax tree of the formula."""
        # Load the SVG function only if we need it. This way the bindings
        # can still be used outside of IPython if IPython is not
        # installed.
        from IPython.display import SVG
        ostr = ostringstream()
        print_dot_psl(ostr, self)
        return SVG(_ostream_to_svg(ostr))

    def to_str(self, format='spot', parenth=False):
        if format == 'spot' or format == 'f':
            return str_psl(self, parenth)
        elif format == 'spin' or format == 's':
            return str_spin_ltl(self, parenth)
        elif format == 'utf8' or format == '8':
            return str_utf8_psl(self, parenth)
        elif format == 'lbt' or format == 'l':
            return str_lbt_ltl(self)
        elif format == 'wring' or format == 'w':
            return str_wring_ltl(self)
        elif format == 'latex' or format == 'x':
            return str_latex_psl(self, parenth)
        elif format == 'sclatex' or format == 'X':
            return str_sclatex_psl(self, parenth)
        else:
            raise ValueError("unknown string format: " + format)

    def __format__(self, spec):
        """Format the formula according to `spec`.

        Parameters
        ----------
        spec : str, optional
            a list of letters that specify how the formula
            should be formatted.

        Supported specifiers
        --------------------

        - 'f': use Spot's syntax (default)
        - '8': use Spot's syntax in UTF-8 mode
        - 's': use Spin's syntax
        - 'l': use LBT's syntax
        - 'w': use Wring's syntax
        - 'x': use LaTeX output
        - 'X': use self-contained LaTeX output

        Add some of those letters for additional options:

        - 'p': use full parentheses
        - 'c': escape the formula for CSV output (this will
               enclose the formula in double quotes, and escape
               any included double quotes)
        - 'h': escape the formula for HTML output
        - 'd': escape double quotes and backslash,
               for use in C-strings (the outermost double
               quotes are *not* added)
        - 'q': quote and escape for shell output, using single
               quotes or double quotes depending on the contents.

        - ':spec': pass the remaining specification to the
                   formating function for strings.

        """

        syntax = 'f'
        parent = False
        escape = None

        while spec:
            c, spec = spec[0], spec[1:]
            if c in ('f', 's', '8', 'l', 'w', 'x', 'X'):
                syntax = c
            elif c == 'p':
                parent = True
            elif c in ('c', 'd', 'h', 'q'):
                escape = c
            elif c == ':':
                break
            else:
                raise ValueError("unknown format specification: " + c + spec)

        s = self.to_str(syntax, parent)

        if escape == 'c':
            o = ostringstream()
            escape_rfc4180(o, s)
            s = '"' + o.str() + '"'
        elif escape == 'd':
            s = escape_str(s)
        elif escape == 'h':
            o = ostringstream()
            escape_html(o, s)
            s = o.str()
        elif escape == 'q':
            o = ostringstream()
            quote_shell_string(o, s)
            s = o.str()

        return s.__format__(spec)

    def traverse(self, func):
        if func(self):
            return
        for f in self:
            f.traverse(func)

    def map(self, func):
        k = self.kind()
        if k in (op_ff, op_tt, op_eword, op_ap):
            return self
        if k in (op_Not, op_X, op_F, op_G, op_Closure,
                 op_NegClosure, op_NegClosureMarked):
            return formula.unop(k, func(self[0]))
        if k in (op_Xor, op_Implies, op_Equiv, op_U, op_R, op_W,
                 op_M, op_EConcat, op_EConcatMarked, op_UConcat):
            return formula.binop(k, func(self[0]), func(self[1]))
        if k in (op_Or, op_OrRat, op_And, op_AndRat, op_AndNLM,
                 op_Concat, op_Fusion):
            return formula.multop(k, [func(x) for x in self])
        if k in (op_Star, op_FStar):
            return formula.bunop(k, func(self[0]), self.min(), self.max())
        raise ValueError("unknown type of formula")


def automata(*sources, timeout=None, ignore_abort=True, debug=False):
    """Read automata from a list of sources.

    Parameters
    ----------
    *sources : list of str
        These sources can be either commands (end with `|`),
        textual represantations of automata (contain `\n`),
        or filenames (else).
    timeout_error : int, optional
        Number of seconds to wait for the result of a command.
        If None (the default), not limit is used.
    ignore_abort : bool, optional
        If True (the default), skip HOA atomata that ends with
        `--ABORT--`, and return the next automaton in the stream.
        If False, aborted automata are reported as syntax errors.
    debug : bool, optional
        Whether to run the parser in debug mode.

    Notes
    -----

    The automata can be written in the `HOA format`_, as `never
    claims`_, in `LBTT's format`_, or in `ltl2dstar's format`_.

    .. _HOA format: http://adl.github.io/hoaf/
    .. _never claims: http://spinroot.com/spin/Man/never.html
    .. _LBTT's format:
       http://www.tcs.hut.fi/Software/lbtt/doc/html/Format-for-automata.html
    .. _ltl2dstar's format:
       http://www.ltl2dstar.de/docs/ltl2dstar.html#output-format-dstar

    If an argument ends with a `|`, then this argument is interpreted as
    a shell command, and the output of that command (without the `|`)
    is parsed.

    If an argument contains a newline, then it is interpreted as
    actual contents to be parsed.

    Otherwise, the argument is assumed to be a filename.

    The result of this function is a generator on all the automata
    objects read from these sources.  The typical usage is::

        for aut in spot.automata(filename, command, ...):
            # do something with aut

    When the source is a command, and no `timeout` is specified,
    parsing is done straight out of the pipe connecting the
    command.  So

        for aut in spot.automata('randaut -H -n 10 2 |'):
            process(aut)

    will call `process(aut)` on each automaton as soon as it is output by
    `randaut`, and without waiting for `randaut` to terminate.

    However if `timeout` is passed, then `automata()` will wait for
    the entire command to terminate before parsing its entire output.
    If one command takes more than `timeout` seconds,
    `subprocess.TimeoutExpired` is raised.

    If any command terminates with a non-zero error,
    `subprocess.CalledProcessError` is raised.
    """

    o = automaton_parser_options()
    o.debug = debug
    o.ignore_abort = ignore_abort
    for filename in sources:
        try:
            p = None
            proc = None
            if filename[-1] == '|':
                # universal_newlines for str output instead of bytes
                # when the pipe is read from Python (which happens
                # when timeout is set).
                proc = subprocess.Popen(filename[:-1], shell=True,
                                        preexec_fn=os.setsid,
                                        universal_newlines=True,
                                        stdout=subprocess.PIPE)
                if timeout is None:
                    p = automaton_stream_parser(proc.stdout.fileno(),
                                                filename, o)
                else:
                    try:
                        out, err = proc.communicate(timeout=timeout)
                    except subprocess.TimeoutExpired:
                        # Using subprocess.check_output() with timeout
                        # would just kill the shell, not its children.
                        os.killpg(proc.pid, signal.SIGKILL)
                        raise
                    else:
                        ret = proc.wait()
                        if ret:
                            raise subprocess.CalledProcessError(ret,
                                                                filename[:-1])
                    finally:
                        proc = None
                    p = automaton_stream_parser(out, filename, o)
            elif '\n' in filename:
                p = automaton_stream_parser(filename, "<string>", o)
            else:
                p = automaton_stream_parser(filename, o)
            a = True
            while a:
                # This returns None when we reach the end of the file.
                a = p.parse_strict(_bdd_dict)
                if a:
                    yield a
        finally:
            # Make sure we destroy the parser (p) and the subprocess
            # (prop) in the correct order...
            del p
            if proc is not None:
                if not a:
                    # We reached the end of the stream.  Wait for the
                    # process to finish, so that we get its exit code.
                    ret = proc.wait()
                else:
                    # if a != None, we probably got there through an
                    # exception, and the subprocess might still be
                    # running.  Check if an exit status is available
                    # just in case.
                    ret = proc.poll()
                del proc
                if ret:
                    raise subprocess.CalledProcessError(ret, filename[:-1])
    # deleting o explicitely now prevents Python 3.5 from
    # reporting the following error: "<built-in function
    # delete_automaton_parser_options> returned a result with
    # an error set".  It's not clear to me if the bug is in Python
    # or Swig.  At least it's related to the use of generators.
    del o
    return


def automaton(filename, **kwargs):
    """Read a single automaton from a file.

    See `spot.automata` for a list of supported formats."""
    try:
        return next(automata(filename, **kwargs))
    except StopIteration:
        raise RuntimeError("Failed to read automaton from {}".format(filename))


def _postproc_translate_options(obj, default_type, *args):
    type_ = None
    pref_ = None
    optm_ = None
    comp_ = 0
    unam_ = 0
    sbac_ = 0

    def type_set(val):
        nonlocal type_
        if type_ is not None and type_ != val:
            raise ValueError("type cannot be both {} and {}"
                             .format(type_, val))
        elif val == 'generic':
            type_ = postprocessor.Generic
        elif val == 'tgba':
            type_ = postprocessor.TGBA
        elif val == 'ba':
            type_ = postprocessor.BA
        else:
            assert(val == 'monitor')
            type_ = postprocessor.Monitor

    def pref_set(val):
        nonlocal pref_
        if pref_ is not None and pref_ != val:
            raise ValueError("preference cannot be both {} and {}"
                             .format(pref_, val))
        elif val == 'small':
            pref_ = postprocessor.Small
        elif val == 'deterministic':
            pref_ = postprocessor.Deterministic
        else:
            assert(val == 'any')
            pref_ = postprocessor.Any

    def optm_set(val):
        nonlocal optm_
        if optm_ is not None and optm_ != val:
            raise ValueError("optimization level cannot be both {} and {}"
                             .format(optm_, val))
        if val == 'high':
            optm_ = postprocessor.High
        elif val.startswith('med'):
            optm_ = postprocessor.Medium
        else:
            assert(val == 'low')
            optm_ = postprocessor.Low

    def misc_set(val):
        nonlocal comp_, unam_, sbac_
        if val == 'complete':
            comp_ = postprocessor.Complete
        elif val == 'sbacc' or val == 'state-based-acceptance':
            sbac_ = postprocessor.SBAcc
        else:
            assert(val == 'unambiguous')
            unam_ = postprocessor.Unambiguous

    options = {
        'tgba': type_set,
        'ba': type_set,
        'monitor': type_set,
        'generic': type_set,
        'small': pref_set,
        'deterministic': pref_set,
        'any': pref_set,
        'high': optm_set,
        'medium': optm_set,
        'low': optm_set,
        'complete': misc_set,
        'unambiguous': misc_set,
        'statebasedacceptance': misc_set,
        'sbacc': misc_set,
    }

    for arg in args:
        arg = arg.lower()
        fn = options.get(arg)
        if fn:
            fn(arg)
        else:
            # arg is not an know option, but maybe it is a prefix of
            # one of them
            compat = []
            f = None
            for key, fn in options.items():
                if key.startswith(arg):
                    compat.append(key)
                    f = fn
            lc = len(compat)
            if lc == 1:
                f(compat[0])
            elif lc < 1:
                raise ValueError("unknown option '{}'".format(arg))
            else:
                raise ValueError("ambiguous option '{}' is prefix of {}"
                                 .format(arg, str(compat)))

    if type_ is None:
        type_ = default_type
    if pref_ is None:
        pref_ = postprocessor.Small
    if optm_ is None:
        optm_ = postprocessor.High

    obj.set_type(type_)
    obj.set_pref(pref_ | comp_ | unam_ | sbac_)
    obj.set_level(optm_)


def translate(formula, *args):
    """Translate a formula into an automaton.

    Keep in mind that 'Deterministic' expresses just a preference that
    may not be satisfied.

    The optional arguments should be strings among the following:
    - at most one in 'TGBA', 'BA', or 'Monitor'
      (type of automaton to build)
    - at most one in 'Small', 'Deterministic', 'Any'
      (preferred characteristics of the produced automaton)
    - at most one in 'Low', 'Medium', 'High'
      (optimization level)
    - any combination of 'Complete', 'Unambiguous', and
      'StateBasedAcceptance' (or 'SBAcc' for short)

    The default corresponds to 'tgba', 'small' and 'high'.
    """
    a = translator(_bdd_dict)
    _postproc_translate_options(a, postprocessor.TGBA, *args)
    if type(formula) == str:
        formula = parse_formula(formula)
    return a.run(formula)


formula.translate = translate


def postprocess(automaton, *args):
    """Post process an automaton.

    This applies a number of simlification algorithms, depending on
    the options supplied. Keep in mind that 'Deterministic' expresses
    just a preference that may not be satisfied if the input is
    not already 'Deterministic'.

    The optional arguments should be strings among the following:
    - at most one in 'Generic', 'TGBA', 'BA', or 'Monitor'
      (type of automaton to build)
    - at most one in 'Small', 'Deterministic', 'Any'
      (preferred characteristics of the produced automaton)
    - at most one in 'Low', 'Medium', 'High'
      (optimization level)
    - any combination of 'Complete' and 'StateBasedAcceptance'
      (or 'SBAcc' for short)

    The default corresponds to 'generic', 'small' and 'high'.
    """
    p = postprocessor()
    if type(automaton) == str:
        automaton = globals()['automaton'](automaton)
    _postproc_translate_options(p, postprocessor.Generic, *args)
    return p.run(automaton)


twa.postprocess = postprocess

# Wrap C++-functions into lambdas so that they get converted into
# instance methods (i.e., self passed as first argument
# automatically), because only used-defined functions are converted as
# instance methods.
for meth in ('scc_filter', 'scc_filter_states'):
    setattr(twa_graph, meth, (lambda self, *args, **kwargs:
                              globals()[meth](self, *args, **kwargs)))

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

    if fun[:3] == 'is_':
        notfun = 'is_not_' + fun[3:]
    elif fun[:4] == 'has_':
        notfun = 'has_no_' + fun[4:]
    else:
        notfun = 'not_' + fun
    setattr(formulaiterator, fun, filtf)
    setattr(formulaiterator, notfun, nfiltf)


# fun should be a function taking a formula as its first parameter and
# returning a formula.  _addmap adds this function as a method of
# formula and formulaiterator.
def _addmap(fun):
    def mapf(self, *args, **kwargs):
        return formulaiterator(map(lambda f: getattr(f, fun)(*args, **kwargs),
                                   self))
    setattr(formula, fun,
            lambda self, *args, **kwargs:
            globals()[fun](self, *args, **kwargs))
    setattr(formulaiterator, fun, mapf)


def randltl(ap, n=-1, **kwargs):
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
        "ltl": OUTPUTLTL,
        "psl": OUTPUTPSL,
        "bool": OUTPUTBOOL,
        "sere": OUTPUTSERE
    }

    if isinstance(ap, list):
        aprops = atomic_prop_set()
        for elt in ap:
            aprops.insert(formula.ap(elt))
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
            print('Use argument ltl_priorities=STRING to set the following '
                  'LTL priorities:\n')
            rg.dump_ltl_priorities(dumpstream)
            print(dumpstream.str())
        elif output == OUTPUTBOOL:
            print('Use argument boolean_priorities=STRING to set the '
                  'following Boolean formula priorities:\n')
            rg.dump_bool_priorities(dumpstream)
            print(dumpstream.str())
        elif output == OUTPUTPSL or output == OUTPUTSERE:
            if output != OUTPUTSERE:
                print('Use argument ltl_priorities=STRING to set the '
                      'following LTL priorities:\n')
                rg.dump_psl_priorities(dumpstream)
                print(dumpstream.str())
            print('Use argument sere_priorities=STRING to set the '
                  'following SERE priorities:\n')
            rg.dump_sere_priorities(dumpstream)
            print(dumpstream.str())
            print('Use argument boolean_priorities=STRING to set the '
                  'following Boolean formula priorities:\n')
            rg.dump_sere_bool_priorities(dumpstream)
            print(dumpstream.str())
        else:
            sys.stderr.write("internal error: unknown type of output")
        return

    class _randltliterator:
        def __init__(self, rg, n):
            self.rg = rg
            self.i = 0
            self.n = n

        def __iter__(self):
            return self

        def __next__(self):
            if self.i == self.n:
                raise StopIteration
            f = self.rg.next()
            if f is None:
                sys.stderr.write("Warning: could not generate a new "
                                 "unique formula after {} trials.\n"
                                 .format(MAX_TRIALS))
                raise StopIteration
            self.i += 1
            return f

    return formulaiterator(_randltliterator(rg, n))


def simplify(f, **kwargs):
    level = kwargs.get('level', None)
    if level is not None:
        return tl_simplifier(tl_simplifier_options(level)).simplify(f)

    basics = kwargs.get('basics', True)
    synt_impl = kwargs.get('synt_impl', True)
    event_univ = kwargs.get('event_univ', True)
    cont_checks = kwargs.get('containment_checks', False)
    cont_checks_stronger = kwargs.get('containment_checks_stronger', False)
    nenoform_stop_on_boolean = kwargs.get('nenoform_stop_on_boolean', False)
    reduce_size_strictly = kwargs.get('reduce_size_strictly', False)
    boolean_to_isop = kwargs.get('boolean_to_isop', False)
    favor_event_univ = kwargs.get('favor_event_univ', False)

    simp_opts = tl_simplifier_options(basics,
                                       synt_impl,
                                       event_univ,
                                       cont_checks,
                                       cont_checks_stronger,
                                       nenoform_stop_on_boolean,
                                       reduce_size_strictly,
                                       boolean_to_isop,
                                       favor_event_univ)
    return tl_simplifier(simp_opts).simplify(f)


for fun in dir(formula):
    if (callable(getattr(formula, fun)) and (fun[:3] == 'is_' or
                                             fun[:4] == 'has_')):
        _addfilter(fun)

for fun in ['remove_x', 'relabel', 'relabel_bse',
            'simplify', 'unabbreviate']:
    _addmap(fun)
