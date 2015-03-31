
import nfa, regexprs, listing, codegen
from strutils import find

const
  asRegex = ".*[Pp]leas.*uring"

proc initExample2(a: var TNFA) =
  let r = parseRegExpr(asRegex)
  r.rule = 1
  regExprToNFA(r, a)

var n: TNFA
var d, o: TDFA

initExample2(n)
NFA_to_DFA(n, d)

optimizeDFA(d, o)

when false:
  import codegen

  var buffer = newStringOfCap(10_000)
  genMatcher(o, buffer)
  writeFile("matcher.nim", buffer)
else:
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

  # for me it's faster without 'reStudy':
  let thaRe = re("[Pp]leas.*?uring", {reDotAll})

  proc main =
    let inp = readFile("benchdata.txt")
    when true:
      bench "vm 1":
        for i in 1..100:
          discard vm.execBytecode(bc, inp)
      bench "vm 2":
        for i in 1..100:
          discard vm2.execBytecode(bc2, inp)

      bench "re A":
        for i in 1..100:
          discard re.find(inp, thaRe)

      bench "find":
        for i in 1..100:
          discard find(inp, "pleasuring")

      echo execBytecode(bc, inp)
      echo execBytecode(bc2, inp)
      echo re.find(inp, thaRe)#+len"pleasuring"
      echo find(inp, "Pleas")#+len"pleasuring"

  main()

  #var txt = open("testA.dot", fmWrite)
  #convertDFAtoDOT(o, "optimized", txt)
  #close(txt)
