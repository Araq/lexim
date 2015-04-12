#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Code generator. Hacked together and produces Nim as string for now. Macro
## support will follow.

import nfa, regexprs

type
  TVariables* = enum
    vaNone, vaCurrChar, vaNextChar, vaPrevChar, vaFillBuffer
  VarArray* = array[TVariables, string]
  TRule* = object
    match*: PRegExpr
    action*: string

const
  VarToName*: VarArray = ["", "CURRCHAR", "NEXTCHAR",
    "PREVCHAR", "FILLBUFFER"]

proc charLit(c: char): string =
  case c
  of '\b': result = "'\\b'"
  of '\t': result = "'\\t'"
  of '\C': result = "'\\r'"
  of '\L': result = "'\\l'"
  of '\v': result = "'\\v'"
  of '\f': result = "'\\f'"
  of '\e': result = "'\\e'"
  of '\a': result = "'\\a'"
  of '\\': result = "'\\\\'"
  else:
    if c < ' ' or c >= '\128':
      result = "'\\" & $ord(c) & "'"
    else:
      result = "'" & $c & "'"

proc charSetLit(cc: set[char]; lastChar: var int): string =
  const
    MaxChar = '\xFF'
  result = "{"
  var c1 = '\0'
  while true:
    if c1 in cc:
      var c2 = c1
      while c2 < MaxChar and succ(c2) in cc: c2 = succ(c2)
      if result.len > 1: result.add ", "
      if c1 == c2:
        if lastChar == 0: lastChar = c1.ord
        else: lastChar = -1
        result.add charLit(c1)
      elif c2 == succ(c1):
        lastChar = -1
        result.add charLit(c1) & ", " & charLit(c2)
      else:
        lastChar = -1
        result.add charLit(c1) & ".." & charLit(c2)
      c1 = c2
    if c1 >= MaxChar: break
    inc c1
  result.add "}"

proc getCmp(vars: VarArray; x: set[char]): string =
  var lastChar = 0
  result = vars[vaCurrChar] & " in " & charSetLit(x, lastChar)
  if lastChar > 0:
    result = vars[vaCurrChar] & " == " & charLit(chr(lastChar))

proc `&=`(x: var string; args: openArray[string]) =
  for a in args: x.add a

template pat(args: varargs[string, `$`]) {.dirty.} =
  res &= args

proc genMatcher*(a: TDFA; vars: VarArray; rules: openArray[TRule];
                 res: var string) =
  # XXX generate fillBuffer instruction!
  pat "  var state: range[1..", a.stateCount, "] = ", a.startState, "\n"
  pat "  while true:\n"
  pat "    case state\n"

  for src in countup(1, a.stateCount):
    pat "    of ", src, ":\n"
    let rule = getRule(a, src)
    var ifs = 0
    for dest in countup(1, a.stateCount):
      let cs = getTransCC(a, src, dest)
      if cs != {}:
        inc ifs
        pat((if ifs == 1: "      if " else: "      elif "),
          getCmp(vars, cs), ": ", vars[vaNextChar],"; state = ", dest, "\n")
    if ifs > 0:
      pat "      else:\n"
    else:
      pat "      if true:\n"
    if rule >= 1:
      pat "        ", rules[rule-1].action, "\n"
    pat "        break\n"
