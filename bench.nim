
import nfa, regexprs, listing
from strutils import find

const
  asRegex = ".*[Pp]leasuring"

import vm
from times import cpuTime

var bc = vm.re(asRegex)
echo "code ", bc.code.len, " data: ", bc.data.len

template bench(text, doWork: expr) =
  var t0 = cpuTime()
  doWork
  echo text, " took [s] ", cpuTime() - t0

import re, strutils

# for me it's faster without 'reStudy':
let thaRe = re.re("[Pp]leas.*?uring", {reDotAll})

proc main =
  let inp = readFile("benchdata.txt")
  when true:
    bench "vm 1":
      for i in 1..100:
        discard vm.matchLen(inp, bc)

    bench "re A":
      for i in 1..100:
        discard re.find(inp, thaRe)

    bench "find":
      for i in 1..100:
        discard find(inp, "pleasuring")

    echo matchLen(inp, bc)
    echo re.find(inp, thaRe)+len"pleasuring"
    echo find(inp, "pleasuring")+len"pleasuring"

main()
