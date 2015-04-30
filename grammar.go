package main

import (
	"unicode"
	"unicode/utf8"
)

type production struct {
	lhs string
	rhs []string
}

// grammar represents a context-free grammar.
type grammar struct {
	isTerminal    map[string]bool
	isNonterminal map[string]bool
	productions   []production
	start         string
}

func newGrammar(ps []production, ss string) *grammar {
	g := &grammar{make(map[string]bool), make(map[string]bool), ps, ss}
	for _, p := range ps {
		g.isNonterminal[p.lhs] = true
		for _, s := range p.rhs {
			r, _ := utf8.DecodeRuneInString(s)
			if unicode.IsUpper(r) {
				g.isNonterminal[s] = true
			} else {
				g.isTerminal[s] = true
			}
		}
	}
	return g
}

/*
func parseGrammar(spec string) *grammar {
	pos := 0
	g := &grammar{make(map[string]bool), make(map[string]bool), nil, ""}

	read := func() {
		r, _ := utf8.DecodeRuneInString(spec[pos:])
	}

	skipWhitespace := func() {
		for pos < len(spec) {
			r, _ := utf8.DecodeRuneInString(spec[pos:])
		}
	}

	pGrammar := func() {
	}

	pProduction := func() {
	}

	return g
}
*/
