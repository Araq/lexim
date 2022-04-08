#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module implements a parser for regular expressions.

import strutils

type
  RegexKind* = enum         ## the regex AST's kind
    reEps,                  ## epsilon node
    reChar,                 ## character node
    reStr,                  ## string node
    reCClass,               ## character class node
    reStar,                 ## star node
    rePlus,                 ## plus node
    reOpt,                  ## option node
    reCat,                  ## concatenation node
    reAlt,                  ## alternatives node (|)
    reCapture,              ## (capture)
    reCaptureEnd,           ## not used by regex, but by NFA
    reBackref,              ## \\backref
    reBegin,                ## \\A
    reEnd,                  ## \\Z
    reWordBoundary,         ## \\b
    reWordBoundaryNot       ## \\B

  PRegExpr* = ref TRegExpr
  TRegExpr* = object
    kind*: RegexKind
    a*, b*: PRegExpr          # some nodes have two successors
    c*: char
    s*: string
    cc*: ref set[char]
    rule*: int                # if >= 0 it is a final state;
                              # then it is the rule that was matched

  RegexError* = object of ValueError
  RegexFlag* = enum  ## how regexes are parsed
    reExtended,      ## extended syntax support
    reNoBackrefs,    ## always process \\1 as a character literal,
                     ## not as back reference
    reNoCaptures     ## () is the same as (?:)

  MacroLookupProc* = proc (macroname: string): PRegExpr {.closure.} ## \
    ## lookup proc that expands {macros}.

  ReCtx = object
    pos: int
    flags: set[RegexFlag]
    captures: int # count the captures to give them an index
    findMacro: MacroLookupProc

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
  result.c = c

proc backrefExpr*(x: int): PRegExpr =
  result = newExpr(reBackref)
  result.c = char x

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
  for i in 2 ..< a.len:
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

proc getNext(buf: string; c: var ReCtx): char =
  if reExtended in c.flags:
    while c.pos < buf.len and buf[c.pos] in {' ', '\t'}: inc(c.pos)
  result = if c.pos < buf.len: buf[c.pos] else: '\0'

proc error(msg: string) {.noinline.} =
  raise newException(RegexError, msg)

proc getChar(buf: string; c: var ReCtx; inClass: bool): PRegExpr =
  var val, i: int
  if reExtended in c.flags and not inClass:
    while c.pos < buf.len and buf[c.pos] in {' ', '\t'}: inc(c.pos)
  if c.pos < buf.len and buf[c.pos] != '\\':
    result = charExpr(buf[c.pos])
    inc(c.pos)
  else:
    let ch = if c.pos+1 < buf.len: buf[c.pos+1] else: '\0'
    case ch
    of 'n':
      result = altExpr(strExpr("\C\L"), charExpr('\L'), charExpr('\C'))
      inc(c.pos, 2)
    of 'r':
      result = charExpr('\r')
      inc(c.pos, 2)
    of 'l', 'L':
      result = charExpr('\L')
      inc(c.pos, 2)
    of 't':
      result = charExpr('\t')
      inc(c.pos, 2)
    of 'b':
      result = if inClass: charExpr('\b') else: newExpr(reWordBoundary)
      inc(c.pos, 2)
    of 'B':
      result = if inClass: charExpr('\b') else: newExpr(reWordBoundaryNot)
      inc(c.pos, 2)
    of 'e':
      result = charExpr('\e')
      inc(c.pos, 2)
    of 'a', 'A':
      result = if inClass: charExpr('\a') else: newExpr(reBegin)
      inc(c.pos, 2)
    of 'v':
      result = charExpr('\v')
      inc(c.pos, 2)
    of 'f':
      result = charExpr('\f')
      inc(c.pos, 2)
    of 'z', 'Z':
      if not inClass: result = newExpr(reEnd)
      else: error("\\Z not supported in character class")
      inc(c.pos, 2)
    of 's':
      result = cclassExpr(whitespace)
      inc(c.pos, 2)
    of 'S':
      result = cclassExpr({'\1'..'\255'} - whitespace)
      inc(c.pos, 2)
    of 'd':
      result = cclassExpr(digits)
      inc(c.pos, 2)
    of 'D':
      result = cclassExpr({'\1'..'\255'} - digits)
      inc(c.pos, 2)
    of 'w':
      result = cclassExpr(wordChars)
      inc(c.pos, 2)
    of 'W':
      result = cclassExpr({'\1'..'\255'} - wordChars)
      inc(c.pos, 2)
    of '0'..'9':
      let startsWithZero = ch == '0'
      val = ord(ch) - ord('0')
      inc(c.pos, 2)
      i = 1
      while (i <= 4) and c.pos < buf.len and (buf[c.pos] in {'0'..'9'}):
        val = val * 10 + ord(buf[c.pos]) - ord('0')
        inc(c.pos)
        inc(i)
      if startsWithZero or reNoBackrefs in c.flags:
        result = charExpr(char val)
      else:
        result = backrefExpr(val)
    else:
      if ch in {'\0'..'\x1F'}:
        error "invalid character #" & toHex(ch.ord, 2)
      else:
        result = charExpr(ch)
        inc(c.pos, 2)

proc parseStr(buf: string; c: var ReCtx): PRegExpr =
  var s = ""
  inc(c.pos)                    # skip "
  while c.pos < buf.len and buf[c.pos] != '\"':
    if buf[c.pos] in {'\0', '\C', '\L'}:
      error "\" expected"
    let al = getChar(buf, c,false)
    if al.kind == reChar: s.add al.c
    else: error "invalid regular expression " & buf
  inc(c.pos)                    # skip "
  result = strExpr(s)

proc parseCClass(buf: string; c: var ReCtx): PRegExpr =
  # scan a character class
  var
    caret: bool
    cc: set[char]
  inc(c.pos)                    # skip [
  if c.pos < buf.len and buf[c.pos] == '^':
    caret = true
    inc(c.pos)
  else:
    caret = false
  while c.pos < buf.len and buf[c.pos] != ']':
    if buf[c.pos] in {'\0', '\C', '\L'}:
      error "] expected"
    let a = getChar(buf, c, true)
    if a.kind == reChar:
      incl(cc, a.c)
      if c.pos < buf.len and buf[c.pos] == '-':
        inc(c.pos)
        if c.pos < buf.len and buf[c.pos] == ']':
          incl(cc, '-')
          break
        let b = getChar(buf, c, true)
        if b.kind == reChar:
          cc = cc + {a.c .. b.c}
        elif b.kind == reCClass:
          incl(cc, '-')
          cc = cc + b.cc[]
        else:
          error "invalid regular expression " & buf
    elif a.kind == reCClass:
      cc = cc + a.cc[]
    else:
      error "invalid regular expression " & buf
  if c.pos < buf.len and buf[c.pos] == ']': inc(c.pos)
  else: error "] expected"
  if caret: result = cclassExpr({'\1'..'\xFF'} - cc)
  else: result = cclassExpr(cc)

proc parseNum(buf: string; c: var ReCtx): int =
  result = 0
  if c.pos < buf.len and buf[c.pos] in {'0'..'9'}:
    while true:
      result = result * 10 + ord(buf[c.pos]) - ord('0')
      inc(c.pos)
      if c.pos >= buf.len or buf[c.pos] notin {'0'..'9'}: break
  else:
    error "number expected"

proc parseIdent(buf: string; c: var ReCtx): string =
  result = ""
  if c.pos < buf.len and buf[c.pos] in {'a'..'z', 'A'..'Z', '_'}:
    while c.pos < buf.len:
      case buf[c.pos]
      of 'a'..'z', 'A'..'Z', '0'..'9':
        result.add toUpperAscii(buf[c.pos])
        inc(c.pos)
      of '_':
        inc(c.pos)              # ignore _
      else: break
  else:
    error "identifier expected"

proc parseMacroCall(buf: string; c: var ReCtx): PRegExpr =
  let name = parseIdent(buf, c)
  result = c.findMacro(name)
  if result.isNil:
    error "undefined macro: " & name

proc parseRegExpr*(buf: string; c: var ReCtx): PRegExpr

proc factor(buf: string; c: var ReCtx): PRegExpr =
  case getNext(buf, c)
  of '\"':
    result = parseStr(buf, c)
  of '[':
    result = parseCClass(buf, c)
  of '.':
    inc(c.pos)
    result = cclassExpr({'\1'..'\xFF'}) # - {'\L'})
  of '(':
    inc(c.pos)                  # skip (
    var isCapture = reNoCaptures notin c.flags
    if c.pos+1 < buf.len and buf[c.pos] == '?' and buf[c.pos+1] == ':':
      inc c.pos, 2
      isCapture = false
    result = parseRegExpr(buf, c)
    if getNext(buf, c) == ')': inc(c.pos)
    else: error ") expected"
    if isCapture:
      inc c.captures
      result = newCapture(result)
      result.c = char c.captures
  of '\\':
    result = getChar(buf, c, false)
  of '{':
    inc(c.pos)                  # skip {
    while c.pos < buf.len and buf[c.pos] in {' ', '\t'}: inc(c.pos)
    result = parseMacroCall(buf, c)
    if getNext(buf, c) == '}': inc(c.pos)
    else: error "} expected"
  of '*', '+', '?':
    error "escape " & buf[c.pos] & " with \\"
  of '$':
    result = newExpr(reEnd)
    inc(c.pos)
  of '^':
    result = newExpr(reBegin)
    inc(c.pos)
  else:
    result = charExpr(if c.pos < buf.len: buf[c.pos] else: '\0')
    inc(c.pos)
  while true:
    case getNext(buf, c)
    of '*':
      inc(c.pos)
      result = starExpr(result)
    of '+':
      inc(c.pos)
      result = plusExpr(result)
    of '?':
      inc(c.pos)
      result = optExpr(result)
    of '{':
      inc(c.pos)                # skip {
      if getNext(buf, c) notin {'0'..'9'}:
        # a macro, but do not parse it here, but later to
        # keep the operator predecence:
        while true:           # back to {
                              # a single decrement might not do
                              # because of skipped whitespace
          dec(c.pos)
          if buf[c.pos] == '{': break
        break
      else:
        var n: int
        let m = parseNum(buf, c)
        if getNext(buf, c) == ',':
          inc(c.pos)
          while c.pos < buf.len and buf[c.pos] in {' ', '\t'}: inc(c.pos)
          n = parseNum(buf, c)
        else:
          n = m
        result = mnExpr(result, m, n)
      if getNext(buf, c) == '}': inc(c.pos)
      else: error "} expected"
    else: break

proc term(buf: string; c: var ReCtx): PRegExpr =
  const
    termDelim = {'\0', ':', '|', ')'} #,'/'
  if getNext(buf, c) notin termDelim:
    result = factor(buf, c)
    while getNext(buf, c) notin termDelim:
      result = catExpr(result, factor(buf, c))
  else:
    result = epsExpr()

proc parseRegExpr(buf: string; c: var ReCtx): PRegExpr =
  result = term(buf, c)
  while getNext(buf, c) == '|':
    inc(c.pos)
    result = altExpr(result, term(buf, c))

proc parseRegExpr*(reg: string; findMacro: MacroLookupProc;
                   flags: set[RegexFlag] = {}): PRegExpr =
  var c: ReCtx
  c.pos = 0
  c.flags = flags
  c.findMacro = findMacro
  c.captures = 0
  result = parseRegExpr(reg, c)

proc containsInvCap(r: PRegExpr; inAlt: bool): bool =
  if r != nil:
    result = containsInvCap(r.a, inAlt or r.kind == reAlt) or
             containsInvCap(r.b, inAlt or r.kind == reAlt) or
             r.kind == reCapture and inAlt

proc containsInvalidCapture*(r: PRegExpr): bool =
  ## When the implementation uses a DFA, captures can only be supported in
  ## quite a limited way: (abc)|(xyz) cannot be supported. This proc checks for
  ## that so a nice error can be generated.
  result = containsInvCap(r, false)
