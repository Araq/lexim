#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Translates the DFA into a bytecode and then runs the bytecode.
## Cannot support most re features and is so doesn't even compile anymore.
import nfa, strutils, intsets

type
  Instr* = object
    d: uint16 # data to test against
    t: int16  # next state when match (true)
    f: int16  # next state when no match (false), if f < 0, return -f

  Bytecode* = object
    code*: seq[Instr]
    data*: seq[set[char]]
    startAt*: int

  PCtx* = var Bytecode

proc genData(c: PCtx; data: set[char]): int =
  for i in 0 .. c.data.high:
    if c.data[i] == data: return i
  result = c.data.len
  c.data.add data

proc genBytecode*(a: DFA; res: PCtx) =
  #doAssert a.startState == 1, "startState must be 1"
  var stateToLabel: seq[int16] = @[]

  for src in countup(1, a.stateCount):
    stateToLabel.add(res.code.len.int16)
    for dest in countup(1, a.stateCount):
      let cs = getTransCC(a, src, dest)
      if cs != {}:
        let d = genData(res, cs)
        let next = res.code.len.int16 + 1
        res.code.add(Instr(d: d.uint16, t: dest.int16, f: next))
    res.code[^1].f = -getRule(a, src).int16 - 1
  # Fixup the T jumps:
  for i in 0 .. res.code.high:
    res.code[i].t = stateToLabel[res.code[i].t-1]
  res.startAt = stateToLabel[a.startState-1]

type Action* = int #distinct range[1..32_000]

proc execBytecode*(m: Bytecode; input: string;
                   start=0): tuple[a: Action, endPos: int] =
  var pc = m.startAt
  var sp = start
  while true:
    # in my benchmarks, unrolling this loop only produced much worse results
    let instr = m.code[pc]
    pc = instr.f
    if input[sp] in m.data[instr.d.int]:
      if pc < -1: return (Action(-pc-1), sp)
      pc = instr.t
      inc sp
    else:
      if pc < 0: return (Action(-pc-1), sp)
