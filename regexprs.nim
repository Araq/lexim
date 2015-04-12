#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module implements a parser for regular expressions. It is special here
# that whitespace is ignored in regular expressions for readability. The
# colon serves as a terminator of the expression. Thus : has to be written as
# \: if meant literally. Newlines are not allowed in regular expressions
# though. It would made the interface between the different scanners (for each
# programming language there should be a special one) too complicated.

discard """
expression   matches                        example
----------   ----------------------------   -------
c            any non-operator character c   a
\c           character c literally          \*
"s"          string s literally             "**"
.            any character (incl newline)   a.*b
[s]          any character in s             [abc]
[^s]         any character not in s         [^abc]
r*           zero or more r's               a*
r+           one or more r's                a+
r?           zero or one r                  a?
r{m,n}       m to n occurrences of r        a{1,5}
r{m}         m occurrences of r             a{5}
r1r2         r1 then r2                     ab
r1|r2        r1 or r2                       a|b
(r)          r                              (a|b)

The / and <> operators are not supported. The operators *, +, ? and {} have
highest precedence, followed by concatenation. The | operator has lowest
precedence. Parentheses () may be used to group expressions and overwrite
default precedences.
"""

import strutils

type
  Alphabet* = range[0..259] # usually a 'char', but \A, \Z, epsilon etc
                            # are not in the range \0..\255
  TRegExprType* = enum
    reEps,                    # epsilon node
    reChar,                   # character node
    reStr,                    # string node
    reCClass,                 # character class node
    reStar,                   # star node
    rePlus,                   # plus node
    reOpt,                    # option node
    reCat,                    # concatenation node
    reAlt                     # alternatives node (|)
  PRegExpr* = ref TRegExpr
  TRegExpr* = object
    regType*: TRegExprType
    a*, b*: PRegExpr          # some nodes have two successors
    c*: Alphabet
    s*: string
    cc*: ref set[char]
    rule*: int                # if >= 0 it is a final state;
                              # then it is the rule that was matched

  RegexError* = object of ValueError

const
  alBegin* = Alphabet(256)   # \A
  alEnd* = Alphabet(257)     # \Z
  alWordBoundary* = Alphabet(258) # \b
  alEpsilon* = Alphabet(259) # epsilon (not used by regex, but by NFA)

proc newExpr(regType: TRegExprType): PRegExpr =
  new(result)
  result.regtype = regtype

proc epsExpr*(): PRegExpr =
  result = newExpr(reEps)

proc charExpr*(c: char): PRegExpr =
  result = newExpr(reChar)
  result.c = Alphabet(c)

proc strExpr*(str: string): PRegExpr =
  if len(str) == 1:
    result = charExpr(str[0])
  else:
    result = newExpr(reStr)
    result.s = str

proc cclassExpr*(charset: set[char]): PRegExpr =
  result = newExpr(reCClass)
  new(result.cc)
  result.cc[] = charset

proc starExpr*(r: PRegExpr): PRegExpr =
  if r.regType == reStar:
    result = r
  else:
    result = newExpr(reStar)
    result.a = r

proc plusExpr*(r: PRegExpr): PRegExpr =
  result = newExpr(rePlus)
  result.a = r

proc optExpr*(r: PRegExpr): PRegExpr =
  result = newExpr(reOpt)
  result.a = r

proc catExpr*(a, b: PRegExpr): PRegExpr =
  result = newExpr(reCat)
  result.a = a
  result.b = b

proc altExpr*(a, b: PRegExpr): PRegExpr =
  result = newExpr(reAlt)
  result.a = a
  result.b = b

proc altExpr*(a: varargs[PRegExpr]): PRegExpr =
  result = altExpr(a[0], a[1])
  for i in 2 .. <a.len:
    result = result.altExpr(a[i])

proc mnExpr*(r: PRegExpr; m, n: int): PRegExpr =
  var ri: PRegExpr
  if m > n or n == 0:
    result = epsExpr()
  else:
    # construct r^m:
    if m == 0:
      ri = epsExpr()
    else:
      ri = r
      for i in countup(2, m): ri = catExpr(ri, r)
    result = ri               # r{m,n} := r^m
    for i in countup(m + 1, n):
      if ri.regType == reEps: ri = r
      else: ri = catExpr(ri, r)
      result = altExpr(result, ri) # r{m,n} := r{m,n} | r^i,
                                   #   i=m+1,...,n

type
  MacroLookupProc* = proc (macroname: string): PRegExpr {.closure.}

proc getNext(buf: string; pos: var int): char =
  while buf[pos] in {' ', '\t'}: inc(pos)
  result = buf[pos]

proc getChar(buf: string; pos: var int): string =
  var val, i: int
  while buf[pos] in {' ', '\t'}: inc(pos)
  if buf[pos] != '\\':
    result = $buf[pos]
    inc(pos)
  else:
    case buf[pos + 1]         # case
    of 'n', 'N':
      result = "\n"
      inc(pos, 2)
    of 'r', 'R':
      result = "\r"
      inc(pos, 2)
    of 'l', 'L':
      result = "\L"
      inc(pos, 2)
    of 't', 'T':
      result = "\t"
      inc(pos, 2)
    of 'b', 'B':
      result = "\b"
      inc(pos, 2)
    of 'e', 'E':
      result = "\e"
      inc(pos, 2)
    of 'a', 'A':
      result = "\a"
      inc(pos, 2)
    of 'v', 'V':
      result = "\v"
      inc(pos, 2)
    of 'f', 'F':
      result = "\f"
      inc(pos, 2)
    of '0'..'9':
      val = ord(buf[pos + 1]) - ord('0')
      inc(pos, 2)
      i = 1
      while (i <= 3) and (buf[pos] in {'0'..'9'}):
        val = val * 10 + ord(buf[pos]) - ord('0')
        inc(pos)
        inc(i)
      result = $chr(val)
    else:
      if buf[pos + 1] in {'\0'..'\x1F'}:
        raise newException(RegexError, "invalid character in regular expression #" &
            toHex(ord(buf[pos + 1]), 2))
      else:
        result = $buf[pos + 1]
        inc(pos, 2)

proc parseStr(buf: string; pos: var int): PRegExpr =
  var s = ""
  inc(pos)                    # skip "
  while buf[pos] != '\"':
    if buf[pos] in {'\0', '\C', '\L'}:
      raise newException(RegexError, "\" expected")
    s.add getChar(buf, pos)
  inc(pos)                    # skip "
  result = strExpr(s)

proc parseCClass(buf: string; pos: var int): PRegExpr =
  # scan a character class
  var
    caret: bool
    cc: set[char]
  inc(pos)                    # skip [
  if getNext(buf, pos) == '^':
    caret = true
    inc(pos)
  else:
    caret = false
  while getNext(buf, pos) != ']':
    if buf[pos] in {'\0', '\C', '\L'}:
      raise newException(RegexError, "] expected")
    let a = getChar(buf, pos)
    if len(a) != 1:
      raise newException(RegexError, "\\n is not a single character")
    incl(cc, a[0])
    if getNext(buf, pos) == '-':
      inc(pos)
      if getNext(buf, pos) == ']':
        incl(cc, '-')
        break
      let b = getChar(buf, pos)
      if len(b) != 1:
        raise newException(RegexError, "\\n is not a single character")
      cc = cc + {a[0]..b[0]}
    else:
      cc = cc + {a[0]}
  if buf[pos] == ']': inc(pos)
  else: raise newException(RegexError, "] expected")
  if caret: result = cclassExpr({'\1'..'\xFF'} - cc)
  else: result = cclassExpr(cc)

proc parseNum(buf: string; pos: var int): int =
  result = 0
  if buf[pos] in {'0'..'9'}:
    while true:
      result = result * 10 + ord(buf[pos]) - ord('0')
      inc(pos)
      if not (buf[pos] in {'0'..'9'}): break
  else:
    raise newException(RegexError, "number expected")

proc parseIdent(buf: string; pos: var int): string =
  result = ""
  if buf[pos] in {'a'..'z', 'A'..'Z', '_'}:
    while true:
      case buf[pos]
      of 'a'..'z', 'A'..'Z', '0'..'9':
        result.add toUpper(buf[pos])
        inc(pos)
      of '_':
        inc(pos)              # ignore _
      else: break
  else:
    raise newException(RegexError, "identifier expected")

proc parseMacroCall(buf: string; pos: var int;
                    findMacro: MacroLookupProc): PRegExpr =
  let name = parseIdent(buf, pos)
  result = findMacro(name)
  if result.isNil:
    raise newException(RegexError, "undefined macro: " & name)

proc parseRegExpr*(buf: string; pos: var int;
                   findMacro: MacroLookupProc): PRegExpr

proc factor(buf: string; pos: var int;
            findMacro: MacroLookupProc): PRegExpr =
  var n, m: int
  case getNext(buf, pos)
  of '\"':
    result = parseStr(buf, pos)
  of '[':
    result = parseCClass(buf, pos)
  of '.':
    inc(pos)
    result = cclassExpr({'\1'..'\xFF'}) # - {'\L'})
  of '(':
    inc(pos)                  # skip (
    result = parseRegExpr(buf, pos, findMacro)
    if getNext(buf, pos) == ')': inc(pos)
    else:
      raise newException(RegexError, ") expected")
  of '\\':
    result = strExpr(getChar(buf, pos))
  of '{':
    inc(pos)                  # skip {
    while (buf[pos] in {' ', '\t'}): inc(pos)
    result = parseMacroCall(buf, pos, findMacro)
    if getNext(buf, pos) == '}': inc(pos)
    else:
      raise newException(RegexError, "} expected")
  of '*', '+', '?':
    raise newException(RegexError, "escape " & buf[pos] & " with \\")
  else:
    result = charExpr(buf[pos])
    inc(pos)
  while true:
    case getNext(buf, pos)    # case
    of '*':
      inc(pos)
      result = starExpr(result)
    of '+':
      inc(pos)
      result = plusExpr(result)
    of '?':
      inc(pos)
      result = optExpr(result)
    of '{':
      inc(pos)                # skip {
      if getNext(buf, pos) notin {'0'..'9'}:
        # a macro, but do not parse it here, but later to
        # keep the operator predecence:
        while true:           # back to {
                              # a single decrement might not do
                              # because of skipped whitespace
          dec(pos)
          if buf[pos] == '{': break
        break
      else:
        m = parseNum(buf, pos)
        if getNext(buf, pos) == ',':
          inc(pos)
          while buf[pos] in {' ', '\t'}: inc(pos)
          n = parseNum(buf, pos)
        else:
          n = m
        result = mnExpr(result, m, n)
      if getNext(buf, pos) == '}': inc(pos)
      else: raise newException(RegexError, "} expected")
    else: break

proc term(buf: string; pos: var int;
          findMacro: MacroLookupProc): PRegExpr =
  const
    termDelim = {'\0', ':', '$', '|', ')'} #,'/'
  if getNext(buf, pos) notin termDelim:
    result = factor(buf, pos, findMacro)
    while getNext(buf, pos) notin termDelim:
      result = catExpr(result, factor(buf, pos, findMacro))
  else:
    result = epsExpr()

proc parseRegExpr(buf: string; pos: var int;
                 findMacro: MacroLookupProc): PRegExpr =
  result = term(buf, pos, findMacro)
  while getNext(buf, pos) == '|':
    inc(pos)
    result = altExpr(result, term(buf, pos, findMacro))

proc parseRegExpr*(reg: string;
                   findMacro: MacroLookupProc): PRegExpr =
  var pos: int                # dummy
  result = parseRegExpr(reg, pos, findMacro)
