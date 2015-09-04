#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import
  regexprs, nfa, marshal

# The part that implements lexer generation as an exe to speed up
# this process.
proc findMacro(name: string): PRegExpr = nil

proc main(input: string): string =
  let inp = marshal.to[seq[string]](input)

  var bigRe: PRegExpr = nil
  for i in 0..<inp.len:
    let rex = parseRegExpr(inp[i], findMacro,
                           {reNoCaptures, reNoBackrefs})
    rex.rule = i+1
    if bigRe.isNil: bigRe = rex
    else: bigRe = altExpr(bigRe, rex)

  var n: NFA
  var d, o: DFA

  regExprToNFA(bigRe, n)
  let alph = fullAlphabet(n)
  NFA_to_DFA(n, d, alph)
  optimizeDFA(d, o, alph)
  result = $$o

echo main(readFile("lexe.input"))
