
import nfa, regexprs, listing
from strutils import find

const
  asRegex = ".*[Pp]leasuring"

import vm
from times import cpuTime

var bc = vm.re(asRegex)
echo "code ", bc.code.len, " data: ", bc.data.len

template bench(text, doWork: untyped) =
  var t0 = cpuTime()
  doWork
  echo text, " took [s] ", cpuTime() - t0

import re, strutils

let thaRe = re.re("[Pp]leasuring", {reDotAll, reStudy})

import lexim
proc lex(input: string): int =
  var pos = 0
  while pos < input.len:
    lexim.match input, pos:
    of r"[Pp]leasuring":
      return pos
    of r".":
      discard
  return -1

import std/strscans
proc scan(input: string): int =
  var pos = 0
  while pos < input.len:
    if scanp(input, pos, {'P', 'p'}, "leasuring"):
      return pos
    inc pos
  return -1

import npeg
proc pegs(input: string): int =
  let p = peg search:
    search <- @({'P', 'p'} * "leasuring")
  let r = p.match(input)
  return if r.ok: r.matchLen else: -1

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

    bench "lexer":
      for i in 1..100:
        discard lex(inp)

    bench "scanp":
      for i in 1..100:
        discard scan(inp)

    bench "npeg":
      for i in 1..100:
        discard pegs(inp)

    echo matchLen(inp, bc)
    echo re.find(inp, thaRe)+len"pleasuring"
    echo find(inp, "pleasuring")+len"pleasuring"
    echo lex(inp) # +len"pleasuring"
    echo scan(inp) # +len"pleasuring"
    echo pegs(inp) # +len"pleasuring"

main()
