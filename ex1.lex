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
@end

type
  TokType = enum
    tkIf, tkElif, tkWhile, tkIntLit, tkFloatLit, tkStrLit, tkIdent

proc parse(input: string): TokType =
  var i = 0
@section rules
  "if": return tkIf
  "elif": return tkElif
  "while": return tkWhile
  {digit}+: return tkIntLit
  {digit}+"@"{alnum}+: return tkIntLit
  {digit}+(\.{digit}+{exp}?|{exp}): return tkFloatLit

  {letter}+{alnum}*: return tkIdent
  [rR] \" .* \": return tkStrLit
  \" .* [^\\]\" | \"\": return tkStrLit
  [rR] \"\"\" {any}* \"\"\": return tkStrLit
@end

