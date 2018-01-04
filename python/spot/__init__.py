# -*- coding: utf-8 -*-
# Copyright (C) 2014-2018  Laboratoire de
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


from spot.impl import *
from spot.aux import \
     extend as _extend, \
     str_to_svg as _str_to_svg, \
     ostream_to_svg as _ostream_to_svg
import subprocess
import os
import signal


# The parrameters used by default when show() is called on an automaton.
_show_default = None


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
    show_default : str
        default options for show()
    max_states : int
        maximum number of states in GraphViz output (default: 50)
    """
    import os

    s = ('size="{}" edge[arrowhead=vee, arrowsize=.7]')
    os.environ['SPOT_DOTEXTRA'] = s.format(kwargs.get('size', '10.2,5'))

    bullets = 'B' if kwargs.get('bullets', True) else ''
    max_states = '<' + str(kwargs.get('max_states', 50))
    d = 'rf({})C({}){}'.format(kwargs.get('font', 'Lato'),
                               kwargs.get('fillcolor', '#ffffaa'),
                               bullets + max_states)
    global _show_default
    _show_default = kwargs.get('show_default', None)
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


@_extend(twa, ta)
class twa:
    def _repr_svg_(self, opt=None):
        """Output the automaton as SVG"""
        ostr = ostringstream()
        if opt is None:
            global _show_default
            opt = _show_default
        print_dot(ostr, self, opt)
        return _ostream_to_svg(ostr)

    def show(self, opt=None):
        """Display the automaton as SVG, in the IPython/Jupyter notebook"""
        if opt is None:
            global _show_default
            opt = _show_default
        # Load the SVG function only if we need it. This way the
        # bindings can still be used outside of IPython if IPython is
        # not installed.
        from IPython.display import SVG
        return SVG(self._repr_svg_(opt))

    def highlight_states(self, states, color):
        """Highlight a list of states.  This can be a list of
        state numbers, or a list of Booleans."""
        for idx, val in enumerate(states):
            if type(val) is bool:
                if val:
                    self.highlight_state(idx, color)
            else:
                self.highlight_state(val, color)
        return self

    def highlight_edges(self, edges, color):
        """Highlight a list of edges.  This can be a list of
        edge numbers, or a list of Booleans."""
        for idx, val in enumerate(edges):
            if type(val) is bool:
                if val:
                    self.highlight_edge(idx, color)
            else:
                self.highlight_edge(val, color)
        return self

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
        if type(str) == formula:
            self.this = str
        else:
            self.this = parse_formula(str)

    def show_ast(self):
        """Display the syntax tree of the formula."""
        # Load the SVG function only if we need it. This way the bindings
        # can still be used outside of IPython if IPython is not
        # installed.
        from IPython.display import SVG
        return SVG(_str_to_svg(self.to_str('d')))

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
        elif format == 'dot' or format == 'd':
            ostr = ostringstream()
            print_dot_psl(ostr, self)
            return ostr.str().encode('utf-8')
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
        - '[...]': rewrite away all the operators specified in brackets,
               using spot.unabbreviate().

        - ':spec': pass the remaining specification to the
                   formating function for strings.

        """

        syntax = 'f'
        parent = False
        escape = None

        form = self

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
            elif c == '[':
                pos = spec.find(']')
                if pos < 0:
                    raise ValueError("unclosed bracket: [" + spec)
                form = form.unabbreviate(spec[0:pos])
                spec = spec[pos+1:]
            else:
                raise ValueError("unknown format specification: " + c + spec)

        s = form.to_str(syntax, parent)

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

    def traverse(self, func, *args):
        if func(self, *args):
            return
        for f in self:
            f.traverse(func, *args)

    def map(self, func, *args):
        k = self.kind()
        if k in (op_ff, op_tt, op_eword, op_ap):
            return self
        if k in (op_Not, op_X, op_F, op_G, op_Closure,
                 op_NegClosure, op_NegClosureMarked):
            return formula.unop(k, func(self[0], *args))
        if k in (op_Xor, op_Implies, op_Equiv, op_U, op_R, op_W,
                 op_M, op_EConcat, op_EConcatMarked, op_UConcat):
            return formula.binop(k, func(self[0], *args), func(self[1], *args))
        if k in (op_Or, op_OrRat, op_And, op_AndRat, op_AndNLM,
                 op_Concat, op_Fusion):
            return formula.multop(k, [func(x, *args) for x in self])
        if k in (op_Star, op_FStar):
            return formula.bunop(k, func(self[0], *args),
                                 self.min(), self.max())
        raise ValueError("unknown type of formula")


def automata(*sources, timeout=None, ignore_abort=True,
             trust_hoa=True, no_sid=False, debug=False):
    """Read automata from a list of sources.

    Parameters
    ----------
    *sources : list of str
        These sources can be either commands (end with `|`),
        textual representations of automata (contain `\n`),
        or filenames (else).
    timeout : int, optional
        Number of seconds to wait for the result of a command.
        If None (the default), not limit is used.
    ignore_abort : bool, optional
        If True (the default), skip HOA atomata that ends with
        `--ABORT--`, and return the next automaton in the stream.
        If False, aborted automata are reported as syntax errors.
    trust_hoa : bool, optional
        If True (the default), supported HOA properies that
        cannot be easily verified are trusted.
    no_sid : bool, optional
        When an automaton is obtained from a subprocess, this
        subprocess is started from a shell with its own session
        group (the default) unless no_sid is set to True.
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
    o.trust_hoa = trust_hoa
    o.raise_errors = True
    for filename in sources:
        try:
            p = None
            proc = None
            if filename[-1] == '|':
                setsid_maybe = None
                if not no_sid:
                    setsid_maybe = os.setsid
                # universal_newlines for str output instead of bytes
                # when the pipe is read from Python (which happens
                # when timeout is set).
                proc = subprocess.Popen(filename[:-1], shell=True,
                                        preexec_fn=
                                        None if no_sid else os.setsid,
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
                a = p.parse(_bdd_dict).aut
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
        elif val == 'parity min odd':
            type_ = postprocessor.ParityMinOdd
        elif val == 'parity min even':
            type_ = postprocessor.ParityMinEven
        elif val == 'parity max odd':
            type_ = postprocessor.ParityMaxOdd
        elif val == 'parity max even':
            type_ = postprocessor.ParityMaxEven
        elif val == 'parity min':
            type_ = postprocessor.ParityMin
        elif val == 'parity max':
            type_ = postprocessor.ParityMax
        elif val == 'parity odd':
            type_ = postprocessor.ParityOdd
        elif val == 'parity even':
            type_ = postprocessor.ParityEven
        elif val == 'parity':
            type_ = postprocessor.Parity
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
        'any': pref_set,
        'ba': type_set,
        'complete': misc_set,
        'deterministic': pref_set,
        'generic': type_set,
        'high': optm_set,
        'low': optm_set,
        'medium': optm_set,
        'monitor': type_set,
        'parity even': type_set,
        'parity max even': type_set,
        'parity max odd': type_set,
        'parity max': type_set,
        'parity min even': type_set,
        'parity min odd': type_set,
        'parity min': type_set,
        'parity odd': type_set,
        'parity': type_set,
        'sbacc': misc_set,
        'small': pref_set,
        'statebasedacceptance': misc_set,
        'tgba': type_set,
        'unambiguous': misc_set,
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


def translate(formula, *args, dict=_bdd_dict):
    """Translate a formula into an automaton.

    Keep in mind that 'Deterministic' expresses just a preference that
    may not be satisfied.

    The optional arguments should be strings among the following:
    - at most one in 'TGBA', 'BA', or 'Monitor', 'generic',
      'parity', 'parity min odd', 'parity min even',
      'parity max odd', 'parity max even' (type of automaton to
      build)
    - at most one in 'Small', 'Deterministic', 'Any'
      (preferred characteristics of the produced automaton)
    - at most one in 'Low', 'Medium', 'High'
      (optimization level)
    - any combination of 'Complete', 'Unambiguous', and
      'StateBasedAcceptance' (or 'SBAcc' for short)

    The default corresponds to 'tgba', 'small' and 'high'.
    """
    a = translator(dict)
    _postproc_translate_options(a, postprocessor.TGBA, *args)
    if type(formula) == str:
        formula = parse_formula(formula)
    return a.run(formula)


formula.translate = translate


def postprocess(automaton, *args, formula=None):
    """Post process an automaton.

    This applies a number of simlification algorithms, depending on
    the options supplied. Keep in mind that 'Deterministic' expresses
    just a preference that may not be satisfied if the input is
    not already 'Deterministic'.

    The optional arguments should be strings among the following:
    - at most one in 'Generic', 'TGBA', 'BA', or 'Monitor',
      'parity', 'parity min odd', 'parity min even',
      'parity max odd', 'parity max even' (type of automaton to
      build)
    - at most one in 'Small', 'Deterministic', 'Any'
      (preferred characteristics of the produced automaton)
    - at most one in 'Low', 'Medium', 'High'
      (optimization level)
    - any combination of 'Complete' and 'StateBasedAcceptance'
      (or 'SBAcc' for short)

    The default corresponds to 'generic', 'small' and 'high'.

    If a formula denoted by this automaton is known, pass it to as the
    optional `formula` argument; it can help some algorithms by
    providing an easy way to complement the automaton.
    """
    p = postprocessor()
    if type(automaton) == str:
        automaton = globals()['automaton'](automaton)
    _postproc_translate_options(p, postprocessor.Generic, *args)
    return p.run(automaton, formula)


twa.postprocess = postprocess

# Wrap C++-functions into lambdas so that they get converted into
# instance methods (i.e., self passed as first argument
# automatically), because only used-defined functions are converted as
# instance methods.
def _add_twa_graph(meth):
    setattr(twa_graph, meth, (lambda self, *args, **kwargs:
                              globals()[meth](self, *args, **kwargs)))

for meth in ('scc_filter', 'scc_filter_states',
             'is_deterministic', 'is_unambiguous'):
    _add_twa_graph(meth)

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
            'simplify', 'unabbreviate', 'negative_normal_form',
            'mp_class', 'nesting_depth']:
    _addmap(fun)



# Better interface to the corresponding C++ function.
def sat_minimize(aut, acc=None, colored=False,
                 state_based=False, states=0,
                 max_states=0, sat_naive=False, sat_langmap=False,
                 sat_incr=0, sat_incr_steps=0):
    args=''
    if acc is not None:
        if type(acc) is not str:
            raise ValueError("argument 'acc' should be a string")
        args += ',acc="' + acc + '"'
    if colored:
        args += ',colored'
    if states:
        if type(states) is not int or states < 0:
            raise ValueError("argument 'states' should be a positive integer")
        args += ',states=' + str(states)
    if max_states:
        if type(max_states) is not int or max_states < 0:
            raise ValueError("argument 'states' should be a positive integer")
        args += ',max-states=' + str(max_states)
    if sat_naive:
        args += ',sat-naive'
    if sat_langmap:
        args += ',sat-langmap'
    if sat_incr:
        args += ',sat-incr=' + str(sat_incr)
        args += ',sat-incr-steps=' + str(sat_incr_steps)

    from spot.impl import sat_minimize as sm
    return sm(aut, args, state_based)


def parse_word(word, dic=_bdd_dict):
    from spot.impl import parse_word as pw
    return pw(word, dic)

def bdd_to_formula(b, dic=_bdd_dict):
    from spot.impl import bdd_to_formula as bf
    return bf(b, dic)

def language_containment_checker(dic=_bdd_dict):
    from spot.impl import language_containment_checker as c
    return c(dic)


def mp_hierarchy_svg(cl=None):
    """
    Return an some string containing an SVG picture of the Manna &
    Pnueli hierarchy, highlighting class `cl` if given.

    If not None, `cl` should be one of 'TPROGSB'.  For convenience,
    if `cl` is an instance of `spot.formula`, it is replaced by
    `mp_class(cl)`.

    """
    if type(cl)==formula:
        cl = mp_class(cl)
    ch = None
    coords = {
        'T': '110,35',
        'R': '40,80',
        'P': '175,80',
        'O': '110,140',
        'S': '40,160',
        'G': '175,160',
        'B': '110,198',
    }
    if cl in coords:
        highlight='''<g transform="translate({})">
    <line x1="-10" y1="-10" x2="10" y2="10" stroke="red" stroke-width="5" />
    <line x1="-10" y1="10" x2="10" y2="-10" stroke="red" stroke-width="5" />
    </g>'''.format(coords[cl])
    else:
        highlight=''
    return '''
<svg height="210" width="220" xmlns="http://www.w3.org/2000/svg" version="1.1">
<polygon points="20,0 200,120 200,210 20,210" fill="cyan" opacity=".2" />
<polygon points="20,120 155,210 20,210" fill="cyan" opacity=".2" />
<polygon points="200,0 20,120 20,210 200,210" fill="magenta" opacity=".15" />
<polygon points="200,120 65,210 200,210" fill="magenta" opacity=".15" />
''' + highlight + '''
<g text-anchor="middle" font-size="14">
<text x="110" y="20">Reactivity</text>
<text x="60" y="65">Recurrence</text>
<text x="160" y="65">Persistence</text>
<text x="110" y="125">Obligation</text>
<text x="60" y="185">Safety</text>
<text x="160" y="185">Guarantee</text>
</g>
<g font-size="14">
<text text-anchor="begin" transform="rotate(-90,18,210)" x="18" y="210" fill="gray">Monitor</text>
<text text-anchor="end" transform="rotate(-90,18,0)" x="18" y="0" fill="gray">Deterministic Büchi</text>
<text text-anchor="begin" transform="rotate(-90,214,210)" x="214" y="210" fill="gray">Terminal Büchi</text>
<text text-anchor="end" transform="rotate(-90,214,0)" x="214" y="0" fill="gray">Weak Büchi</text>
</g>
</svg>'''


def show_mp_hierarchy(cl):
    """
    Return a picture of the Manna & Pnueli hierarchy as an SVG object
    in the IPython/Jupyter.
    """
    from IPython.display import SVG
    return SVG(mp_hierarchy_svg(cl))

formula.show_mp_hierarchy = show_mp_hierarchy

@_extend(twa_word)
class twa_word:
    def as_svg(self):
        """
        Build an SVG picture representing the word as a collection of
        signals for each atomic proposition.
        """
        # Get the list of atomic proposition used
        sup = buddy.bddtrue
        for cond in list(self.prefix) + list(self.cycle):
            sup = sup & buddy.bdd_support(cond)
        ap = []
        while sup != buddy.bddtrue:
            a = buddy.bdd_var(sup)
            ap.append(a)
            sup = buddy.bdd_high(sup)

        # Prepare canvas
        psize = len(self.prefix)
        csize = len(self.cycle)
        d = {
            'endprefix': 50 * psize,
            'endcycle': 50 * (psize + csize),
            'w': 50 * (psize + csize * 2),
            'height': 50 * len(ap),
            'height2': 50 * len(ap) + 10,
            'h3': 50 * len(ap) + 12,
            'bgcolor': '#f4f4f4',
            'bgl': 'stroke="white" stroke-width="4"',
            'bgt': 'stroke="white" stroke-width="1"',
            'txt': 'text-anchor="start" font-size="20"',
            'red': 'stroke="#ff0000" stroke-width="2"',
            'sml': 'text-anchor="start" font-size="10"'
            }
        txt = '''
<svg height="{h3}" width="{w}" xmlns="http://www.w3.org/2000/svg" version="1.1">
<rect x="0" y="0" width="{w}" height="{height}" fill="{bgcolor}"/>
<line x1="{endprefix}" y1="0" x2="{endprefix}" y2="{height}"
      stroke="white" stroke-width="4"/>
<line x1="{endcycle}" y1="0" x2="{endcycle}" y2="{height}"
      stroke="white" stroke-width="4"/>
'''.format(**d)

        # Iterate over all used atomic propositions, and fill each line
        l = list(self.prefix) + list(self.cycle) + list(self.cycle)
        bd = self.get_dict()
        for ypos, a in enumerate(ap):
            pa = buddy.bdd_ithvar(a)
            na = buddy.bdd_nithvar(a)
            name = bdd_format_formula(bd, pa)
            # Whether the last state was down (-1), up (1), or unknown (0)
            last = 0
            txt += ('<line x1="0" y1="{y}" x2="{w}" y2="{y}" {bgl}/>'
                    .format(y=ypos*50, **d))
            txt += ('<text x="{x}" y="{y}" {txt}>{name}</text>'
                    .format(x=3, y=ypos*50+30, name=name, **d))
            for xpos, step in enumerate(l):
                if buddy.bdd_implies(step, pa):
                    cur = 1
                elif buddy.bdd_implies(step, na):
                    cur = -1
                else:
                    cur = 0
                txt += ('<line x1="{x}" y1="{y1}" x2="{x}" y2="{y2}" {bgt}/>'
                        .format(x=(xpos+1)*50, y1=ypos*50, y2=ypos*50+50, **d))
                if cur != 0:
                    if last == -cur:
                        txt += \
                        ('<line x1="{x}" y1="{y1}" x2="{x}" y2="{y2}" {red}/>'
                             .format(x=xpos*50, y1=ypos*50+5,
                                     y2=ypos*50+45, **d))
                    txt += \
                    ('<line x1="{x1}" y1="{y}" x2="{x2}" y2="{y}" {red}/>'
                         .format(x1=xpos*50, x2=(xpos+1)*50,
                                 y=ypos*50+25-20*cur, **d))
                last = cur
        if psize > 0:
            txt += '<text x="0" y="{height2}" {sml}>prefix</text>'.format(**d)
        txt += '''<text x="{endprefix}" y="{height2}" {sml}>cycle</text>
<text x="{endcycle}" y="{height2}" {sml}>cycle</text>'''.format(**d)
        return txt + '</svg>'

    def show(self):
        """
        Display the word as an SVG picture of signals.
        """
        from IPython.display import SVG
        return SVG(self.as_svg())
