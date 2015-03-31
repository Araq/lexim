#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Translates the DFA into a bytecode and then runs the bytecode.
import unsigned, nfa, strutils, intsets

type
  TInstr* = distinct uint32

  TOpcode* = enum
    opcRet,         # return with some literal
    opcTestSet,     # test current character against bitset in data section
    opcTestChar,    # test current character against char embedded in instr
    opcTJmp         # jump if comparison was true

  Bytecode* = object
    code*: seq[TInstr]
    data*: seq[set[char]]
    startAt*: int

  PCtx* = var Bytecode

template opcode*(x: TInstr): TOpcode {.immediate.} = TOpcode(x.uint32 and 0xff'u32)
template regBx*(x: TInstr): int {.immediate.} = (x.uint32 shr 16'u32).int

proc codeListing(c: Bytecode, result: var string, start=0; last = -1) =
  # first iteration: compute all necessary labels:
  var jumpTargets = initIntSet()
  let last = if last < 0: c.code.len-1 else: min(last, c.code.len-1)
  for i in start..last:
    let x = c.code[i]
    if x.opcode == opcTJmp:
      jumpTargets.incl(x.regBx)

  var i = start
  while i <= last:
    if i in jumpTargets: result.addf("L$1:\n", i)
    let x = c.code[i]
    result.add($i)
    let opc = opcode(x)
    case opc
    of opcRet:
      result.addf("\t$#\t$#\n", ($opc).substr(3), x.regBx)
    of opcTestSet:
      result.addf("\t$#\t$#\n", ($opc).substr(3), $c.data[x.regBx])
    of opcTestChar:
      result.addf("\t$#\t$#\n", ($opc).substr(3), $chr(x.regBx))
    of opcTJmp:
      result.addf("\t$#\tL$#\n", ($opc).substr(3), x.regBx)
    inc i

proc echoCode*(c: PCtx; start=0; last = -1) {.deprecated.} =
  var buf = ""
  codeListing(c, buf, start, last)
  echo buf

proc genInstr(opc: TOpcode; bx: int): TInstr =
  # `bx` must be signed and in the range [-32767, 32768]
  const a = 0
  doAssert bx >= -32767 and bx <= 32768
  result = (opc.uint32 or a.uint32 shl 8'u32 or
            bx.uint32 shl 16'u32).TInstr

proc gABx(c: PCtx; opc: TOpcode; bx: int) =
  c.code.add(genInstr(opc, bx))

proc genData(c: PCtx; data: set[char]): int =
  for i in 0 .. c.data.high:
    if c.data[i] == data: return i
  result = c.data.len
  c.data.add data

proc genTest(res: PCtx; cs: set[char]) =
  var elem = '\0'
  var card = 0
  for x in cs:
    if elem == '\0': elem = x
    inc card
  if card == 1:
    gABx(res, opcTestChar, ord(elem))
  else:
    gABx(res, opcTestSet, genData(res, cs))

proc genBytecode*(a: TDFA; res: PCtx) =
  #doAssert a.startState == 1, "startState must be 1"
  var stateToLabel: seq[int] = @[]

  for src in countup(1, a.stateCount):
    stateToLabel.add(res.code.len)
    let rule = getRule(a, src)
    if rule == 0:
      for dest in countup(1, a.stateCount):
        let cs = getTransCC(a, src, dest)
        if cs != {}:
          genTest(res, cs)
          # We need to fixup this branch instruction later:
          gABx(res, opcTJmp, dest)
    gABx(res, opcRet, rule)
  # Fixup the TJmp instructions:
  for i in 0 .. res.code.high:
    let instr = res.code[i]
    if opcode(instr) == opcTJmp:
      res.code[i] = genInstr(opcTJmp, stateToLabel[regBx(instr)-1])
  res.startAt = stateToLabel[a.startState-1]

type Action* = int #distinct range[1..32_000]

proc execBytecode*(m: PCtx; input: string;
                   start=0): tuple[a: Action, endPos: int] =
  var pc = m.startAt
  var sp = start
  while true:
    let instr = m.code[pc]
    let opc = instr.opcode
    let arg = instr.regBx
    if opc == opcTestSet:
      # we *know* the next instruction is a TJmp:
      let next = m.code[pc+1]
      assert next.opcode == opcTJmp
      if input[sp] in m.data[arg]:
        pc = next.regBx
        inc sp
      else:
        inc pc, 2
    elif opc == opcTestChar:
      # we *know* the next instruction is a TJmp:
      let next = m.code[pc+1]
      assert next.opcode == opcTJmp
      if input[sp] == chr(arg):
        pc = next.regBx
        inc sp
      else:
        inc pc, 2
    else:
      assert opc == opcRet
      return (Action(arg), sp)
