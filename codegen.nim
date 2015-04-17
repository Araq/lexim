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
    vaNone, vaCurrChar, vaNextChar, vaBeforeBreak, vaFillBuffer
  VarArray* = array[TVariables, string]
  TRule* = object
    match*: PRegExpr
    action*: string

const
  VarToName*: VarArray = ["", "CURRCHAR", "NEXTCHAR",
    "BEFOREBREAK", "FILLBUFFER"]

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

proc charSetLit(cc: set[char]): string =
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
        result.add charLit(c1)
      elif c2 == succ(c1):
        result.add charLit(c1) & ", " & charLit(c2)
      else:
        result.add charLit(c1) & ".." & charLit(c2)
      c1 = c2
    if c1 >= MaxChar: break
    inc c1
  result.add "}"

proc getCmp(vars: VarArray; x: set[char]): string =
  result = vars[vaCurrChar] & " in " & charSetLit(x)

proc getSpecial(vars: VarArray; x: Alphabet): string =
  result = vars[vaCurrChar] & " == " & charLit(x.val)

proc `&=`(x: var string; args: openArray[string]) =
  for a in args: x.add a

template pat(args: varargs[string, `$`]) {.dirty.} =
  res &= args

proc genMatcher*(a: DFA; vars: VarArray; rules: openArray[TRule];
                 res: var string) =
  # XXX generate fillBuffer instruction!
  pat "  var state {.goto.}: range[1..", a.stateCount, "] = ", a.startState, "\n"
  pat "  while true:\n"
  pat "    case state\n"

  for src in countup(1, a.stateCount):
    pat "    of ", src, ":\n"
    let rule = getRule(a, src)
    var ifs = 0
    for dest in allDests(a, src):
      let (others, cs) = allTransitions(a, src, dest)
      if cs != {}:
        inc ifs
        pat((if ifs == 1: "      if " else: "      elif "),
          getCmp(vars, cs), ": ", vars[vaNextChar],"; state = ", dest, "\n")
      for ot in others:
        if ot.kind == reChar:
          inc ifs
          pat((if ifs == 1: "      if " else: "      elif "),
            getSpecial(vars, ot), ": ", vars[vaNextChar],"; state = ", dest, "\n")
        else:
          doAssert false, "not supported " & $ot.kind
    if ifs > 0:
      pat "      else:\n"
    else:
      pat "      if true:\n"
    if rule >= 1:
      pat "        ", rules[rule-1].action, "\n"
    if vars[vaBeforeBreak].len > 0:
      pat vars[vaBeforeBreak], "\n"
    pat "        break\n"
