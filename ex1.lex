# This test the Lexim for Nim

@section codegen
  currChar = "input[i]"
  nextChar = "inc(i)"
  prevChar = "dec(i)"
  fillBuffer = "i = fillBuffer(input, i)"
@end

@section macros
  letter = [A-Za-z_]
  digit = [0-9]
  alnum = {letter}|{digit}
  exp = [eE][+-]?{digit}+
  any = [\0-\255]
  space = [\32\t]
@end

type
  TokType = enum
    tkNone, tkSpaces,
    tkIf, tkElif, tkWhile, tkIntLit, tkFloatLit, tkStrLit, tkIdent

proc parse(input: string; i: var int): TokType =
@section rules
  "if": result = tkIf
  "elif": result = tkElif
  "while": result = tkWhile
  {digit}+: result = tkIntLit
  {digit}+"@"{alnum}+: result = tkIntLit
  {digit}+(\.{digit}+{exp}?|{exp}): result = tkFloatLit

  {letter}+{alnum}*: result = tkIdent

  {space}+: result = tkSpaces

  [rR] \" .* \": result = tkStrLit

  \" .* [^\\]\" | \"\": result = tkStrLit

  [rR] \"\"\" {any}* \"\"\": result = tkStrLit
@end

const
  testInput = """some identifier 12  34.5  3e100"""

var pos = 0
while true:
  let tok = parse(testInput, pos)
  echo tok
  if tok == tkNone: break

