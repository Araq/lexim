#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#


## this modules contains utility functions for list generating routines:

import strutils

proc nchars*(cc: set[char]): int =
  result = 0
  for c in countup('\0', '\xFF'):
    if c in cc: inc(result)

proc charStr*(c: char; reserved: set[char]): string =
  case c
  of '\b':
    result = "\\b"
  of '\t':
    result = "\\t"
  of '\C':
    result = "\\r"
  of '\L':
    result = "\\l"
  of '\v':
    result = "\\v"
  of '\f':
    result = "\\f"
  of '\e':
    result = "\\e"
  of '\a':
    result = "\\a"
  of '\\':
    result = "\\\\"
  else:
    if c < ' ':
      result = '\\' & $ord(c)
    elif c in reserved:
      result = '\\' & $c
    else:
      result = $c

proc singleQuoteStr*(str: string): string =
  result = "'"
  for c in str: result.add charStr(c, {'\''})
  result.add '\''

proc doubleQuoteStr*(str: string): string =
  result = "\""
  for c in str: result.add charStr(c, {'\"'})
  result.add '\"'

proc charSetStrAux(cc: set[char]): string =
  const
    reserved = {'^', '-', ']'}
    MaxChar = '\xFF'
  result = ""
  var c1 = '\0'
  while true:
    if c1 in cc:
      var c2 = c1
      while (c2 < MaxChar) and (succ(c2) in cc): c2 = succ(c2)
      if c1 == c2:
        result.add charStr(c1, reserved)
      elif c2 == succ(c1):
        result.add charStr(c1, reserved) & charStr(c2, reserved)
      else:
        result.add charStr(c1, reserved) & '-' & charStr(c2, reserved)
      c1 = c2
    if c1 >= MaxChar: break
    inc(c1)

proc charSetStr*(cc: set[char]): string =
  if cc == {'\x01'..'\xFF'} - {'\L'}:
    result = "."
  else:
    if nchars(cc) > 128:
      result = "[^" & charSetStrAux({'\0'..'\xFF'} - cc) & ']'
    else:
      result = '[' & charSetStrAux(cc) & ']'

proc charSetOrCharStr*(cc: set[char]): string =
  var count = 0
  var c1 = '\0'                   # to avoid warnings
  for c in countup('\0', '\xFF'):
    if c in cc:
      c1 = c
      inc(count)
  if count > 1:
    result = charSetStr(cc)
  elif count == 1:
    result = charStr(c1, {'.'}) # was: singleQuoteStr(c1)
  else:
    result = "[]"

