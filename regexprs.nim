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
  Alphabet* = range[0..262] # usually a 'char', but \A, \Z, epsilon etc
                            # are not in the range \0..\255
  RegexKind* = enum
    reEps,                    # epsilon node
    reChar,                   # character node
    reStr,                    # string node
    reCClass,                 # character class node
    reStar,                   # star node
    rePlus,                   # plus node
    reOpt,                    # option node
    reCat,                    # concatenation node
    reAlt,                    # alternatives node (|)
    reCapture                 # (capture)
  PRegExpr* = ref TRegExpr
  TRegExpr* = object
    kind*: RegexKind
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
  alWordBoundaryNot* = Alphabet(259) # \B
  alCaptureBegin* = Alphabet(260)
  alCaptureEnd* = Alphabet(261)
  alEpsilon* = Alphabet(262) # epsilon (not used by regex, but by NFA)

const
  wordChars* = {'A'..'Z', 'a'..'z', '0'..'9', '_', '\128', '\255'}
  whitespace* = {'\1'..'\32'}
  digits* = {'0'..'9'}

proc newExpr(kind: RegexKind): PRegExpr =
  new(result)
  result.kind = kind

proc epsExpr*(): PRegExpr =
  result = newExpr(reEps)

proc charExpr*(c: char): PRegExpr =
  result = newExpr(reChar)
  result.c = Alphabet(c)

proc charExpr*(c: Alphabet): PRegExpr =
  result = newExpr(reChar)
  result.c = c

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
  if r.kind == reStar:
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
      if ri.kind == reEps: ri = r
      else: ri = catExpr(ri, r)
      result = altExpr(result, ri) # r{m,n} := r{m,n} | r^i,
                                   #   i=m+1,...,n

proc newCapture*(a: PRegExpr): PRegExpr =
  result = newExpr(reCapture)
  result.a = a

type
  MacroLookupProc* = proc (macroname: string): PRegExpr {.closure.}

proc getNext(buf: string; pos: var int): char =
  while buf[pos] in {' ', '\t'}: inc(pos)
  result = buf[pos]

proc error(msg: string) {.noinline.} =
  raise newException(RegexError, msg)

proc getChar(buf: string; pos: var int; inClass: bool): PRegExpr =
  var val, i: int
  while buf[pos] in {' ', '\t'}: inc(pos)
  if buf[pos] != '\\':
    result = charExpr(buf[pos])
    inc(pos)
  else:
    case buf[pos+1]
    of 'n':
      result = altExpr(strExpr("\C\L"), charExpr('\L'), charExpr('\C'))
      inc(pos, 2)
    of 'r':
      result = charExpr('\r')
      inc(pos, 2)
    of 'l', 'L':
      result = charExpr('\L')
      inc(pos, 2)
    of 't':
      result = charExpr('\t')
      inc(pos, 2)
    of 'b':
      result = if inClass: charExpr('\b') else: charExpr(alWordBoundary)
      inc(pos, 2)
    of 'B':
      result = if inClass: charExpr('\b') else: charExpr(alWordBoundaryNot)
      inc(pos, 2)
    of 'e':
      result = charExpr('\e')
      inc(pos, 2)
    of 'a', 'A':
      result = if inClass: charExpr('\a') else: charExpr(alBegin)
      inc(pos, 2)
    of 'v':
      result = charExpr('\v')
      inc(pos, 2)
    of 'f':
      result = charExpr('\f')
      inc(pos, 2)
    of 'z', 'Z':
      if not inClass: result = charExpr(alEnd)
      else: error("\\Z not supported in character class")
      inc(pos, 2)
    of 's':
      result = cclassExpr(whitespace)
      inc(pos, 2)
    of 'S':
      result = cclassExpr({'\1'..'\255'} - whitespace)
      inc(pos, 2)
    of 'd':
      result = cclassExpr(digits)
      inc(pos, 2)
    of 'D':
      result = cclassExpr({'\1'..'\255'} - digits)
      inc(pos, 2)
    of 'w':
      result = cclassExpr(wordChars)
      inc(pos, 2)
    of 'W':
      result = cclassExpr({'\1'..'\255'} - wordChars)
      inc(pos, 2)
    of '0'..'9':
      val = ord(buf[pos + 1]) - ord('0')
      inc(pos, 2)
      i = 1
      while (i <= 3) and (buf[pos] in {'0'..'9'}):
        val = val * 10 + ord(buf[pos]) - ord('0')
        inc(pos)
        inc(i)
      result = charExpr(char val)
    else:
      if buf[pos + 1] in {'\0'..'\x1F'}:
        error "invalid character #" & toHex(buf[pos+1].ord, 2)
      else:
        result = charExpr(buf[pos + 1])
        inc(pos, 2)

proc parseStr(buf: string; pos: var int): PRegExpr =
  var s = ""
  inc(pos)                    # skip "
  while buf[pos] != '\"':
    if buf[pos] in {'\0', '\C', '\L'}:
      error "\" expected"
    let al = getChar(buf, pos, false)
    if al.kind == reChar and al.c <= 255: s.add char(al.c)
    else: error "invalid regular expression " & buf
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
      error "] expected"
    let a = getChar(buf, pos, true)
    if a.kind == reChar and a.c <= 255:
      incl(cc, a.c.char)
      if getNext(buf, pos) == '-':
        inc(pos)
        if getNext(buf, pos) == ']':
          incl(cc, '-')
          break
        let b = getChar(buf, pos, true)
        if b.kind == reChar and b.c <= 255:
          cc = cc + {a.c.char .. b.c.char}
        elif b.kind == reCClass:
          incl(cc, '-')
          cc = cc + b.cc[]
        else:
          error "invalid regular expression " & buf
    elif a.kind == reCClass:
      cc = cc + a.cc[]
    else:
      error "invalid regular expression " & buf
  if buf[pos] == ']': inc(pos)
  else: error "] expected"
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
    error "number expected"

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
    error "identifier expected"

proc parseMacroCall(buf: string; pos: var int;
                    findMacro: MacroLookupProc): PRegExpr =
  let name = parseIdent(buf, pos)
  result = findMacro(name)
  if result.isNil:
    error "undefined macro: " & name

proc parseRegExpr*(buf: string; pos: var int;
                   findMacro: MacroLookupProc): PRegExpr

proc factor(buf: string; pos: var int;
            findMacro: MacroLookupProc): PRegExpr =
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
    var isCapture = true
    if buf[pos] == '?' and buf[pos+1] == ':':
      inc pos, 2
      isCapture = false
    result = parseRegExpr(buf, pos, findMacro)
    if getNext(buf, pos) == ')': inc(pos)
    else: error ") expected"
    if isCapture: result = newCapture(result)
  of '\\':
    result = getChar(buf, pos, false)
  of '{':
    inc(pos)                  # skip {
    while (buf[pos] in {' ', '\t'}): inc(pos)
    result = parseMacroCall(buf, pos, findMacro)
    if getNext(buf, pos) == '}': inc(pos)
    else: error "} expected"
  of '*', '+', '?':
    error "escape " & buf[pos] & " with \\"
  of '$':
    result = charExpr(alEnd)
    inc(pos)
  of '^':
    result = charExpr(alBegin)
    inc(pos)
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
        var n: int
        let m = parseNum(buf, pos)
        if getNext(buf, pos) == ',':
          inc(pos)
          while buf[pos] in {' ', '\t'}: inc(pos)
          n = parseNum(buf, pos)
        else:
          n = m
        result = mnExpr(result, m, n)
      if getNext(buf, pos) == '}': inc(pos)
      else: error "} expected"
    else: break

proc term(buf: string; pos: var int;
          findMacro: MacroLookupProc): PRegExpr =
  const
    termDelim = {'\0', ':', '|', ')'} #,'/'
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
