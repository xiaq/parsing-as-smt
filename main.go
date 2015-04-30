package main

import "fmt"

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

func putBenchmark(extrapreds, formulas string) string {
	return fmt.Sprintf(benchmark, extrapreds, formulas)
}

func generateEquivalence(g1, g2 *grammar, n int) (extrapreds, formulas string) {
	addExtrapred := func(s string, a ...interface{}) {
		extrapreds += fmt.Sprintf(s, a...)
	}
	addFormula := func(s string, a ...interface{}) {
		formulas += fmt.Sprintf(s, a...)
	}

	isTerminal := make(map[string]bool)
	for t := range g1.isTerminal {
		isTerminal[t] = true
	}
	for t := range g2.isTerminal {
		isTerminal[t] = true
	}

	// Introduce the "is" family of variables
	for i := 0; i < n; i++ {
		for t := range isTerminal {
			addExtrapred(" (is_%d_%s)", i, t)
		}
	}
	extrapreds += "\n"

	// Encode that at most one of is_i_t for a fixed i is true
	for i := 0; i < n; i++ {
		for j := 0; j <= len(isTerminal); j++ {
			addExtrapred(" (y_%d_%d)", i, j)
		}
		j := 0
		for t := range isTerminal {
			addFormula("(or (not is_%d_%s) (and (not y_%d_%d) y_%d_%d))\n",
				i, t, i, j, i, j+1)
			addFormula("(or (not y_%d_%d) y_%d_%d)\n", i, j, i, j+1)
			j++
		}
	}
	// Encode that at least one of is_i_t for a fixed i is true
	for i := 0; i < n; i++ {
		addFormula("(or")
		for t := range isTerminal {
			addFormula(" is_%d_%s", i, t)
		}
		addFormula(")\n")
	}

	putParses := func(g *grammar, k int) {
		for i := 0; i <= n; i++ {
			for j := i + 1; j <= n; j++ {
				for nt := range g.isNonterminal {
					addExtrapred(" (parses%d_%d_%d_%s)", k, i, j, nt)
					// Encode production rules
					addFormula("(= parses%d_%d_%d_%s (or\n", k, i, j, nt)
					anyProduction := false
					for _, p := range g.productions {
						if p.lhs != nt || j-i < len(p.rhs) {
							continue
						}
						var f func(acc string, i int, rhs []string)
						f = func(acc string, i int, rhs []string) {
							if len(rhs) == 0 {
								if i == j {
									addFormula(acc + ")\n")
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
						addFormula("false")
					}
					addFormula("))\n")
				}
				for t := range g.isTerminal {
					addExtrapred(" (parses%d_%d_%d_%s)", k, i, j, t)
					if j == i+1 {
						addFormula("(= parses%d_%d_%d_%s is_%d_%s)\n",
							k, i, j, t, i, t)
					} else {
						addFormula("(not parses%d_%d_%d_%s\n)", k, i, j, t)
					}
				}
			}
		}
		addExtrapred("\n")
	}
	putParses(g1, 1)
	putParses(g2, 2)

	// Encode that the input is in L(g1) but not in L(g2) or vice versa
	addFormula("(xor parses1_%d_%d_%s parses2_%d_%d_%s)",
		0, n, g1.start, 0, n, g2.start)
	return
}

func main() {
	g1 := newGrammar(ps1, "E")
	g2 := newGrammar(ps2, "E")
	n := 19
	bm := putBenchmark(generateEquivalence(g1, g2, n))
	fmt.Print(bm)
}
