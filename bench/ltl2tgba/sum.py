#!/usr/bin/env python3
import json
import argparse

def latex_escape_char(ch):
  if ch in '#$%&_{}':
    return '\\' + ch
  elif ch in '~^':
    return '\\' + ch + '{}'
  elif ch == '\\':
    return '\\textbackslash'
  else:
    return ch

def latex_escape(x):
  if type(x) == str:
    return ''.join(latex_escape_char(ch) for ch in x)
  return map(latex_escape, x)

def rot(x):
  if type(x) == str:
    return '\\rot{' + x + '}'
  return map(rot, x)


def process_file(filename):
  data = json.load(open(filename))

  ncols = len(data['fields'])
  ntools = len(data['tools'])
  datacols = range(2, ncols)
  fields = { name:index for index,name in enumerate(data["fields"]) }
  toolcol = fields['tool']
  inputcol = fields['input']

  # Index results by tool, then input
  results = { t:{} for t in range(0, ntools) }
  for l in data["results"]:
    results[l[toolcol]][l[inputcol]] = l

  for i in range(0, ntools):
    # Remove any leading directory, and trailing %...
    name = data["tools"][i]
    name = name[name.rfind('/', 0, name.find(' ')) + 1:]
    data["tools"][i] = latex_escape(name[0:name.find('%')])

  print(r'''
\section*{\texttt{%s}}
\subsection*{Cumulative summary}''' % filename)

  print('\\begin{tabular}{l' + ('r' * (ncols - 1)) + '}\n',
        " & ".join(rot(latex_escape(["tool", "count"] + data["fields"][2:]))),
        "\\\\")
  for i in range(0, ntools):
    # Compute sums over each column.
    sums = [("%6.2f" if j == 9 else "%6d") %
            (sum([x[j] for x in results[i].values()]))
            for j in datacols]
    print("\\texttt{%-18s} & %3d & "
          % (data["tools"][i], len(results[i])), " & ".join(sums), "\\\\")
  print(r'\end{tabular}')

  print(r'''\subsection*{Cross comparison}

How many times did the left tool produce an automaton strictly bigger
than the top tool?  Bigger means more states, or equal number of
states and more transitions.

''')

  header = '\\begin{tabular}{l'
  for i in data["tools"]:
    header += 'c'
  header += '}'

  statescol = fields['states']
  transcol = fields['transitions']

  print(header)
  for left in data["tools"]:
    print("&", rot("\\texttt{%s}" % left), end=' ')
  print(r'\\')
  for left in range(0, ntools):
    print("\\texttt{%-18s}" % data["tools"][left], end=' ')
    for top in range(0, ntools):
      x = 0
      for k,ct in results[top].items():
        if k in results[left]:
          cl = results[left][k]
          if (cl[statescol] > ct[statescol]
              or (cl[statescol] == ct[statescol]
                  and cl[transcol] > ct[transcol])):
            x += 1
      print("&", x, end=' ')
    print(r"\\")
  print(r'\end{tabular}')


def main():
  p = argparse.ArgumentParser(description="Process ltlcross' output",
                              epilog="Report bugs to <spot@lrde.epita.fr>.")
  p.add_argument('filenames',
                 help="name of the JSON file to read",
                 nargs='+')
  p.add_argument('--intro',
                 help="introductory text for the LaTeX output",
                 default='')
  args = p.parse_args()

  print(r'''\documentclass{article}
\usepackage[a4paper,landscape,margin=2cm]{geometry}
\usepackage{adjustbox}
\usepackage{array}

\newcolumntype{R}[2]{%
    >{\adjustbox{angle=#1,lap=\width-(#2)}\bgroup}%
    l%
    <{\egroup}%
}
\newcommand*\rot{\multicolumn{1}{R{45}{1em}}}% no optional argument here, please!

\begin{document}
''')
  print(args.intro)
  for filename in args.filenames:
    process_file(filename)
  print(r'\end{document}')


main()