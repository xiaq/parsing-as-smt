package main

import (
	"bytes"
	"fmt"
)

/*
var ps1 = []production{
	{"E", []string{"a", "b"}},
	{"E", []string{"a", "E", "b"}},
}

var ps2 = []production{
	{"E", []string{"a", "F"}},
	{"F", []string{"b"}},
	{"F", []string{"a", "F", "b"}},
}
*/

var ps1 = []production{
	{"E", []string{"num"}},
	{"E", []string{"E", "add", "E"}},
	{"E", []string{"E", "sub", "E"}},
	{"E", []string{"E", "mul", "E"}},
	{"E", []string{"E", "div", "E"}},
}

var ps2 = []production{
	{"E", []string{"E", "add", "M"}},
	{"E", []string{"E", "sub", "M"}},
	{"E", []string{"M"}},
	{"M", []string{"M", "mul", "F"}},
	{"M", []string{"M", "div", "F"}},
	{"M", []string{"F"}},
	{"F", []string{"num"}},
}

const benchmark = `(benchmark q.smt
:logic QF_UF
:extrapreds
(
%s
)
:formula
(and
%s
)
)
`

type generator struct {
	g1, g2          *grammar
	n               int
	preds, formulas *bytes.Buffer
	isTerminal      map[string]bool
}

func newGenerator(g1, g2 *grammar, n int) *generator {
	g := &generator{
		g1, g2, n,
		new(bytes.Buffer), new(bytes.Buffer),
		make(map[string]bool),
	}
	for t := range g1.isTerminal {
		g.isTerminal[t] = true
	}
	for t := range g2.isTerminal {
		g.isTerminal[t] = true
	}
	return g
}

func (g *generator) addPred(s string, a ...interface{}) {
	fmt.Fprintf(g.preds, s, a...)
}

func (g *generator) addFormula(s string, a ...interface{}) {
	fmt.Fprintf(g.formulas, s, a...)
}

func (g *generator) put() string {
	return fmt.Sprintf(benchmark, g.preds.String(), g.formulas.String())
}

func (g *generator) generateIs() {
	n := g.n
	// Introduce the "is" family of variables
	for i := 0; i < n; i++ {
		for t := range g.isTerminal {
			g.addPred(" (is_%d_%s)", i, t)
		}
	}
	g.addPred("\n")

	// Encode that at most one of is_i_t for a fixed i is true
	for i := 0; i < n; i++ {
		for j := 0; j <= len(g.isTerminal); j++ {
			g.addPred(" (y_%d_%d)", i, j)
		}
		j := 0
		for t := range g.isTerminal {
			g.addFormula("(or (not is_%d_%s) (and (not y_%d_%d) y_%d_%d))\n",
				i, t, i, j, i, j+1)
			g.addFormula("(or (not y_%d_%d) y_%d_%d)\n", i, j, i, j+1)
			j++
		}
	}
	// Encode that at least one of is_i_t for a fixed i is true
	for i := 0; i < n; i++ {
		g.addFormula("(or")
		for t := range g.isTerminal {
			g.addFormula(" is_%d_%s", i, t)
		}
		g.addFormula(")\n")
	}
}

func (g *generator) generateParses(gr *grammar, k int) {
	n := g.n
	for i := 0; i <= n; i++ {
		for j := i + 1; j <= n; j++ {
			for nt := range gr.isNonterminal {
				g.addPred(" (parses%d_%d_%d_%s)", k, i, j, nt)
				// Encode production rules
				g.addFormula("(= parses%d_%d_%d_%s (or\n", k, i, j, nt)
				anyProduction := false
				for _, p := range gr.productions {
					if p.lhs != nt || j-i < len(p.rhs) {
						continue
					}
					var f func(acc string, i int, rhs []string)
					f = func(acc string, i int, rhs []string) {
						if len(rhs) == 0 {
							if i == j {
								g.addFormula(acc + ")\n")
							}
							return
						}
						for i2 := i + 1; j-i2 >= len(rhs)-1; i2++ {
							term := fmt.Sprintf(" parses%d_%d_%d_%s",
								k, i, i2, rhs[0])
							f(acc+term, i2, rhs[1:])
						}
					}
					f("(and", i, p.rhs)
				}
				if !anyProduction {
					g.addFormula("false")
				}
				g.addFormula("))\n")
			}
			for t := range gr.isTerminal {
				g.addPred(" (parses%d_%d_%d_%s)", k, i, j, t)
				if j == i+1 {
					g.addFormula("(= parses%d_%d_%d_%s is_%d_%s)\n",
						k, i, j, t, i, t)
				} else {
					g.addFormula("(not parses%d_%d_%d_%s\n)", k, i, j, t)
				}
			}
		}
	}
	g.addPred("\n")
}

func (g *generator) generate1() {
	g.generateIs()
	g.generateParses(g.g1, 1)
}

func (g *generator) generate12() {
	g.generate1()
	g.generateParses(g.g2, 2)
}

func (g *generator) generateInclusion() {
	g.generate12()

	// Encode that the input is in L(g1) but not in L(g2)
	g.addFormula("(and parses1_%d_%d_%s (not parses2_%d_%d_%s))",
		0, g.n, g.g1.start, 0, g.n, g.g2.start)
	// If the solver yields unsat, inclusion is proved
}

func (g *generator) generateEquivalence() {
	g.generate12()

	// Encode that the input is in L(g1) but not in L(g2) or vice versa
	g.addFormula("(xor parses1_%d_%d_%s parses2_%d_%d_%s)",
		0, g.n, g.g1.start, 0, g.n, g.g2.start)
	// If the solver yields unsat, equivalence is proved
}

func (g *generator) generateIntersection() {
	g.generate12()

	// Encode that the input is in L(g1) and in L(g2)
	g.addFormula("(and parses1_%d_%d_%s parses2_%d_%d_%s)",
		0, g.n, g.g1.start, 0, g.n, g.g2.start)
	// If the solver yields a satisfying assignment, intersection is proved
}

func (g *generator) generateUniversality() {
	g.generate1()

	// Encode that the input is not in L(g1)
	g.addFormula("(not parses1_%d_%d_%s)", 0, g.n, g.g1.start)
	// If the solver yields unsat, universality is proved
}

func main() {
	g1 := newGrammar(ps1, "E")
	g2 := newGrammar(ps2, "E")
	n := 19
	g := newGenerator(g1, g2, n)
	// g.generateEquivalence()
	g.generateUniversality()
	fmt.Print(g.put())
}
