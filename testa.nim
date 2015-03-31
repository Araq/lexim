
import nfa, regexprs, listing, codegen

proc initExample2(a: var TNFA) =
  regexprs.addMacro("IDENT", parseRegExpr("[a-zA-Z_]"))
  regexprs.addMacro("E", parseRegExpr("[eE][+-]?[0-9]+"))
  let floatPat = parseRegExpr("[0-9]+ (\\.[0-9]+{e}? | { e })") # floating point numbers
  let intPat = parseRegExpr("[0-9]+") # integer
  let identPat = parseRegExpr("{ident}[0-9 A - Z a-z _]*")
  let elseExpr = parseRegExpr("e l s e ")
  let elifExpr = parseRegExpr("e l  i f    ")
  floatPat.rule = 3
  intPat.rule = 4
  identPat.rule = 5
  elseExpr.rule = 1
  elifExpr.rule = 2
  regExprToNFA(altExpr(identPat, intPat, floatPat, elifExpr, elseExpr), a)

const
  asRegex = "([a-zA-Z_][0-9A-Za-z_]*)|([0-9]+)|([0-9]+ (\\.[0-9]+([eE][+-]?[0-9]+)?|[eE][+-]?[0-9]+))|else|elif"

var n: TNFA
var d, o: TDFA

initExample2(n)
NFA_to_DFA(n, d)

optimizeDFA(d, o)

when false:
  var buffer = newStringOfCap(10_000)
  genMatcher(o, buffer)
  writeFile("matcher.nim", buffer)

import vm, vm2
from times import cpuTime

var bc = vm.Bytecode(code: @[], data: @[])
vm.genBytecode(o, bc)
echo "code ", bc.code.len, " data: ", bc.data.len


var bc2 = vm2.Bytecode(code: @[], data: @[])
vm2.genBytecode(o, bc2)
echo "code ", bc2.code.len, " data: ", bc2.data.len

template bench(text, doWork: expr) =
  var t0 = cpuTime()
  doWork
  echo text, " took [s] ", cpuTime() - t0

import re, strutils

let thaRe = re(asRegex)

proc main =
  while true:
    let inp = readLine(stdin)
    if inp.len == 0: break
    bench "vm 1":
      for i in 1..100_000:
        discard vm.execBytecode(bc, inp)
    bench "vm 2":
      for i in 1..100_000:
        discard vm2.execBytecode(bc2, inp)

    bench "re A":
      for i in 1..100_000:
        discard re.matchLen(inp, thaRe)

    bench "sets":
      for i in 1..100_000:
        discard strutils.allCharsInSet(inp, {'A'..'Z','a'..'z','0'..'9','_'})

    echo execBytecode(bc, inp)
    echo execBytecode(bc2, inp)
    echo re.matchLen(inp, thaRe)

main()

#var txt = open("testA.dot", fmWrite)
#convertDFAtoDOT(o, "optimized", txt)
#close(txt)
