// -*- coding: utf-8 -*-
// Copyright (C) 2012, 2013, 2014, 2015, 2016 Laboratoire de Recherche
// et Développement de l'Epita (LRDE).
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

#include <spot/tl/relabel.hh>
#include <sstream>
#include <spot/misc/hash.hh>
#include <map>
#include <set>
#include <stack>
#include <iostream>

namespace spot
{
  //////////////////////////////////////////////////////////////////////
  // Basic relabeler
  //////////////////////////////////////////////////////////////////////

  namespace
  {
    struct ap_generator
    {
      virtual formula next() = 0;
      virtual ~ap_generator() {}
    };

    struct pnn_generator final: ap_generator
    {
      unsigned nn;
      pnn_generator()
        : nn(0)
        {
        }

      virtual formula next() override
      {
        std::ostringstream s;
        s << 'p' << nn++;
        return formula::ap(s.str());
      }
    };

    struct abc_generator final: ap_generator
    {
    public:
      abc_generator()
        : nn(0)
        {
        }

      unsigned nn;

      virtual formula next() override
      {
        std::string s;
        unsigned n = nn++;
        do
          {
            s.push_back('a' + (n % 26));
            n /= 26;
          }
        while (n);
        return formula::ap(s);
      }
    };


    class relabeler
    {
    public:
      typedef std::unordered_map<formula, formula> map;
      map newname;
      ap_generator* gen;
      relabeling_map* oldnames;

      relabeler(ap_generator* gen, relabeling_map* m)
        : gen(gen), oldnames(m)
      {
      }

      ~relabeler()
      {
        delete gen;
      }

      formula rename(formula old)
      {
        auto r = newname.emplace(old, nullptr);
        if (!r.second)
          {
            return r.first->second;
          }
        else
          {
            formula res = gen->next();
            r.first->second = res;
            if (oldnames)
              (*oldnames)[res] = old;
            return res;
          }
      }

      formula
      visit(formula f)
      {
        if (f.is(op::ap))
          return rename(f);
        else
          return f.map([this](formula f)
                       {
                         return this->visit(f);
                       });
      }

    };

  }


  formula
  relabel(formula f, relabeling_style style, relabeling_map* m)
  {
    ap_generator* gen = nullptr;
    switch (style)
      {
      case Pnn:
        gen = new pnn_generator;
        break;
      case Abc:
        gen = new abc_generator;
        break;
      }

    relabeler r(gen, m);
    return r.visit(f);
  }

  //////////////////////////////////////////////////////////////////////
  // Boolean-subexpression relabeler
  //////////////////////////////////////////////////////////////////////

  // Here we want to rewrite a formula such as
  //   "a & b & X(c & d) & GF(c & d)" into "p0 & Xp1 & GFp1"
  // where Boolean subexpressions are replaced by fresh propositions.
  //
  // Detecting Boolean subexpressions is not a problem.
  // Furthermore, because we are already representing LTL formulas
  // with sharing of identical sub-expressions we can easily rename
  // a subexpression (such as c&d above) only once.  However this
  // scheme has two problems:
  //
  //   1. It will not detect inter-dependent Boolean subexpressions.
  //      For instance it will mistakenly relabel "(a & b) U (a & !b)"
  //      as "p0 U p1", hiding the dependency between a&b and a&!b.
  //
  //   2. Because of our n-ary operators, it will fail to
  //      notice that (a & b) is a sub-expression of (a & b & c).
  //
  // The code below only addresses point 1 so that interdependent
  // subexpressions are not relabeled.  Point 2 could be improved in
  // a future version of somebody feels inclined to do so.
  //
  // The way we compute the subexpressions that can be relabeled is
  // by transforming the formula syntax tree into an undirected
  // graph, and computing the cut points of this graph.  The cut
  // points (or articulation points) are the nodes whose removal
  // would split the graph in two components.  To ensure that a
  // Boolean operator is only considered as a cut point if it would
  // separate all of its children from the rest of the graph, we
  // connect all the children of Boolean operators.
  //
  // For instance (a & b) U (c & d) has two (Boolean) cut points
  // corresponding to the two AND operators:
  //
  //             (a&b)U(c&d)
  //             ╱         ╲
  //           a&b         c&d
  //          ╱   ╲       ╱   ╲
  //         a─────b     c─────d
  //
  // (The root node is also a cut-point, but we only consider Boolean
  // cut-points for relabeling.)
  //
  // On the other hand, (a & b) U (b & !c) has only one Boolean
  // cut-point which corresponds to the NOT operator:
  //
  //             (a&b)U(b&!c)
  //                ╱   ╲
  //              a&b   b&c
  //             ╱   ╲ ╱   ╲
  //            a─────b────!c
  //                        │
  //                        c
  //
  // Note that if the children of a&b and b&c were not connected,
  // a&b and b&c would be considered as cut points because they
  // separate "a" or "!c" from the rest of the graph.
  //
  // The relabeling of a formula is therefore done in 3 passes:
  //  1. convert the formula's syntax tree into an undirected graph,
  //     adding links between children of Boolean operators
  //  2. compute the (Boolean) cut points of that graph, using the
  //     Hopcroft-Tarjan algorithm (see below for a reference)
  //  3. recursively scan the formula's tree until we reach
  //     either a (Boolean) cut point or an atomic proposition, and
  //     replace that node by a fresh atomic proposition.
  //
  // In the example above (a&b)U(b&!c), the last recursion
  // stop a, b, and !c, producing (p0&p1)U(p1&p2).
  namespace
  {
    typedef std::vector<formula> succ_vec;
    typedef std::map<formula, succ_vec> fgraph;

    // Convert the formula's syntax tree into an undirected graph
    // labeled by subformulas.
    class formula_to_fgraph
    {
    public:
      fgraph& g;
      std::stack<formula> s;

      formula_to_fgraph(fgraph& g):
        g(g)
        {
        }

      ~formula_to_fgraph()
        {
        }

      void
        visit(formula f)
      {
        {
          // Connect to parent
          auto in = g.emplace(f, succ_vec());
          if (!s.empty())
            {
              formula top = s.top();
              in.first->second.emplace_back(top);
              g[top].emplace_back(f);
              if (!in.second)
                return;
            }
          else
            {
              assert(in.second);
            }
        }
        s.push(f);

        unsigned sz = f.size();
        unsigned i = 0;
        if (sz > 2 && !f.is_boolean())
          {
            /// If we have a formula like (a & b & Xc), consider
            /// it as ((a & b) & Xc) in the graph to isolate the
            /// Boolean operands as a single node.
            formula b = f.boolean_operands(&i);
            if (b)
              visit(b);
          }
        for (; i < sz; ++i)
          visit(f[i]);
        if (sz > 1 && f.is_boolean())
          {
            // For Boolean nodes, connect all children in a
            // loop.  This way the node can only be a cut-point
            // if it separates all children from the reset of
            // the graph (not only one).
            formula pred = f[0];
            for (i = 1; i < sz; ++i)
              {
                formula next = f[i];
                // Note that we only add an edge in one
                // direction, because we are building a cycle
                // between all children anyway.
                g[pred].emplace_back(next);
                pred = next;
              }
            g[pred].emplace_back(f[0]);
          }
        s.pop();
      }
    };


    typedef std::set<formula> fset;
    struct data_entry // for each node of the graph
    {
      unsigned num; // serial number, in pre-order
      unsigned low; // lowest number accessible via unstacked descendants
      data_entry(unsigned num = 0, unsigned low = 0)
        : num(num), low(low)
      {
      }
    };
    typedef std::unordered_map<formula, data_entry> fmap_t;
    struct stack_entry
    {
      formula grand_parent;
      formula parent;        // current node
      succ_vec::const_iterator current_child;
      succ_vec::const_iterator last_child;
    };
    typedef std::stack<stack_entry> stack_t;

    // Fill c with the Boolean cutpoints of g, starting from start.
    //
    // This is based no "Efficient Algorithms for Graph
    // Manipulation", J. Hopcroft & R. Tarjan, in Communications of
    // the ACM, 16 (6), June 1973.
    //
    // It differs from the original algorithm by returning only the
    // Boolean cutpoints, and not dealing with the initial state
    // properly (our initial state will always be considered as a
    // cut-point, but since we only return Boolean cut-points it's
    // OK: if the top-most formula is Boolean we want to replace it
    // as a whole).
    void cut_points(const fgraph& g, fset& c, formula start)
    {
      stack_t s;

      unsigned num = 0;
      fmap_t data;
      data_entry d = { num, num };
      data[start] = d;
      ++num;
      const succ_vec& children = g.find(start)->second;
      stack_entry e = { start, start, children.begin(), children.end() };
      s.push(e);

      while (!s.empty())
        {
          stack_entry& e  = s.top();
          if (e.current_child != e.last_child)
            {
              // Skip the edge if it is just the reverse of the one
              // we took.
              formula child = *e.current_child;
              if (child == e.grand_parent)
                {
                  ++e.current_child;
                  continue;
                }
              auto i = data.emplace(std::piecewise_construct,
                                    std::forward_as_tuple(child),
                                    std::forward_as_tuple(num, num));
              if (i.second)        // New destination.
                {
                  ++num;
                  const succ_vec& children = g.find(child)->second;
                  stack_entry newe = { e.parent, child,
                                       children.begin(), children.end() };
                  s.push(newe);
                }
              else           // Destination exists.
                {
                  data_entry& dparent = data[e.parent];
                  data_entry& dchild = i.first->second;
                  // If this is a back-edge, update
                  // the low field of the parent.
                  if (dchild.num <= dparent.num)
                    if (dparent.low > dchild.num)
                      dparent.low = dchild.num;
                }
              ++e.current_child;
            }
          else
            {
              formula grand_parent = e.grand_parent;
              formula parent = e.parent;
              s.pop();
              if (!s.empty())
                {
                  data_entry& dparent = data[parent];
                  data_entry& dgrand_parent = data[grand_parent];
                  if (dparent.low >= dgrand_parent.num // cut-point
                      && grand_parent.is_boolean())
                    c.insert(grand_parent);
                  if (dparent.low < dgrand_parent.low)
                    dgrand_parent.low = dparent.low;
                }
            }
        }
    }


    class bse_relabeler final: public relabeler
    {
    public:
      fset& c;
      bse_relabeler(ap_generator* gen, fset& c,
                    relabeling_map* m)
        : relabeler(gen, m), c(c)
      {
      }

      using relabeler::visit;

      formula
        visit(formula f)
      {
        if (f.is(op::ap) || (c.find(f) != c.end()))
          return rename(f);

        unsigned sz = f.size();
        if (sz <= 2)
          return f.map([this](formula f)
                       {
                         return visit(f);
                       });

        unsigned i = 0;
        std::vector<formula> res;
        /// If we have a formula like (a & b & Xc), consider
        /// it as ((a & b) & Xc) in the graph to isolate the
        /// Boolean operands as a single node.
        formula b = f.boolean_operands(&i);
        if (b && b != f)
          {
            res.reserve(sz - i + 1);
            res.emplace_back(visit(b));
          }
        else
          {
            i = 0;
            res.reserve(sz);
          }
        for (; i < sz; ++i)
          res.emplace_back(visit(f[i]));
        return formula::multop(f.kind(), res);
      }
    };
  }


  formula
  relabel_bse(formula f, relabeling_style style, relabeling_map* m)
  {
    fgraph g;

    // Build the graph g from the formula f.
    {
      formula_to_fgraph conv(g);
      conv.visit(f);
    }

    // Compute its cut-points
    fset c;
    cut_points(g, c, f);

    // Relabel the formula recursively, stopping
    // at cut-points or atomic propositions.
    ap_generator* gen = nullptr;
    switch (style)
      {
      case Pnn:
        gen = new pnn_generator;
        break;
      case Abc:
        gen = new abc_generator;
        break;
      }
    bse_relabeler rel(gen, c, m);
    return rel.visit(f);
  }
}
