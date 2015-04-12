#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import
  os, strutils, regexprs, listing, nfa, codegen

# This scanner/parser is primitive. It is line-based. Lines that it does
# not understand are simply copied to the output.

type # there won't be many macros in the source, so a linked list suffices
  PMacro* = ref TMacro
  TMacro = object
    next: PMacro
    name: string
    value: PRegExpr
  MacroRedefError* = object of ValueError

type
  TParser = object
    pos*: int                 # position in the input line
    linenumber*: int
    currRule*: int            # last parsed rule number + 1
    currIndent*: int
    line*: string             # variables:
    vars*: VarArray
    rules*: seq[TRule]
    infile*, outfile*: string # input and output filenames
    inp*, outp*: File         # input and output files

var
  macros*: PMacro

proc findMacro(name: string): PRegExpr =
  # list of all macros
  var it = macros
  while it != nil:
    if it.name == name: return it.value
    it = it.next

proc addMacro(name: string; value: PRegExpr) =
  if findMacro(name) != nil:
    raise newException(MacroRedefError, "attempt to redefine \"" & name & '\"')
  else:
    var n: PMacro
    new(n)
    n.next = macros
    macros = n
    n.name = name
    n.value = value

proc rawError(msg: string) =
  writeln(stdout, msg)
  quit(1)

proc error(p: TParser; msg: string) =
  writeln(stdout, p.infile, "(", $p.linenumber, ", ", $p.pos, ") ", msg)
  quit(1)

proc getWord(s: string; pos: var int): string =
  result = ""
  while true:
    case s[pos]
    of 'a'..'z':
      result.add toUpper(s[pos])
      inc(pos)
    of '_':
      inc(pos)                # ignore _
    of 'A'..'Z', '0'..'9':
      result.add s[pos]
      inc(pos)
    else: break

proc matchesWord(s: string; word: string; start: int): bool =
  var i = start
  result = getWord(s, i) == word

proc matchesDirective(s, dir: string; pos: var int): bool =
  if pos < len(s) and s[pos] == '@':
    inc(pos)
    result = getWord(s, pos) == dir

proc getString(p: var TParser): string =
  result = ""
  if p.line[p.pos] != '\"': error(p, "string expected")
  inc(p.pos)                  # skip "
  while p.pos < len(p.line) and p.line[p.pos] != '\"':
    add(result, p.line[p.pos])
    inc(p.pos)
  if p.line[p.pos] == '\"': inc(p.pos)
  else: error(p, "\" expected")

proc readLine(p: var TParser) =
  if not readLine(p.inp, p.line):
    error(p, "@end expected, but end of file reached")
  inc(p.linenumber)
  p.pos = 0

proc skipWhites(p: var TParser) =
  p.currIndent = 0
  while true:
    case p.line[p.pos]
    of ' ':
      inc(p.pos)
      inc(p.currIndent)
    of '\t':
      inc(p.pos)
      p.currIndent = p.currIndent + (p.currIndent and not 7) + 8
    else: break

proc rawSkipWhites(p: var TParser) =
  while p.line[p.pos] in {' ', '\t'}: inc(p.pos)

proc parseCodeGen(p: var TParser) =
  let varname = getWord(p.line, p.pos)
  if varname == "": error(p, "identifier expected")
  rawSkipWhites(p)
  if p.line[p.pos] == '=': inc(p.pos)
  else: error(p, "= expected")
  rawSkipWhites(p)
  let value = getString(p)
  var found = false
  for varc in countup(succ(vaNone), high(TVariables)):
    if varname == VarToName[varc]:
      found = true
      p.vars[varc] = value
  if not found: error(p, "unknown variable name: " & varname)

proc parseMacro(p: var TParser) =
  let varname = getWord(p.line, p.pos)
  rawSkipWhites(p)
  if p.line[p.pos] == '=': inc(p.pos)
  else: error(p, "= expected")
  rawSkipWhites(p)
  try:
    let value = regexprs.parseRegExpr(p.line, p.pos, findMacro)
    addMacro(varname, value)
  except RegexError:
    error(p, getCurrentExceptionMsg())
  except MacroRedefError:
    error(p, getCurrentExceptionMsg())

proc parseRule(p: var TParser) =
  try:
    let indentation = p.currIndent
    let regexpr = parseRegExpr(p.line, p.pos, findMacro)
    rawSkipWhites(p)
    if regexpr == nil or regexpr.regType == reEps:
      readline(p)             # just skip empty lines
      return
    if p.line[p.pos] == ':': inc(p.pos)
    else: error(p, ": expected")
    rawSkipWhites(p)
    var a = substr(p.line, p.pos, len(p.line))
    while true:
      readline(p)
      skipWhites(p)
      if p.currIndent <= indentation or
          matchesDirective(p.line, "END", p.pos):
        break
      a.add "\n"
      a.add(p.line)
    setlen(p.rules, p.currRule + 1)
    regexpr.rule = p.currRule + 1
    p.rules[p.currRule].match = regexpr
    p.rules[p.currRule].action = a
    inc(p.currRule)
  except RegExError:
    error(p, getCurrentExceptionMsg())

proc generateCodeAux(p: var TParser; d: DFA) =
  var buffer = newStringOfCap(20_000)
  genMatcher(d, p.vars, p.rules, buffer)
  write(p.outp, buffer)


var n: NFA
var d, o: DFA

proc generateCode(p: var TParser) =
  var bigRe: PRegExpr
  if len(p.rules) == 0: return
  bigRe = p.rules[0].match
  for i in countup(1, high(p.rules)): bigRe = altExpr(bigRe, p.rules[i].match)
  regExprToNFA(bigRe, n)
  NFA_to_DFA(n, d)
  optimizeDFA(d, o)
  generateCodeAux(p, o)

proc parse(p: var TParser; infile, outfile: string) =
  type
    TSectionType = enum
      seNone, seCodegen, seMacros, seRules
  var
    section: string
    sectionType: TSectionType
  if not open(p.inp, infile): rawError("could not open: " & infile)
  if not open(p.outp, outfile, fmWrite):
    rawError("could not create: " & outfile)
  p.infile = infile
  p.outfile = outfile
  p.linenumber = 0
  while not endOfFile(p.inp):
    readline(p)
    rawSkipWhites(p)
    if matchesDirective(p.line, "SECTION", p.pos):
      rawSkipWhites(p)
      section = getWord(p.line, p.pos)
      if section == "MACROS":
        sectionType = seMacros
      elif section == "RULES":
        sectionType = seRules
      elif section == "CODEGEN":
        sectionType = seCodegen
      else:
        error(p, "invalid section")
        sectionType = seNone
      readline(p)
      skipWhites(p)
      while true:
        if matchesDirective(p.line, "END", p.pos): break
        case sectionType
        of seMacros:
          parseMacro(p)
          readline(p)
          skipwhites(p)
        of seRules:
          parseRule(p)
        of seCodeGen:
          parseCodegen(p)
          readline(p)
          skipwhites(p)
        else: assert(false)
      if sectionType == seRules: generateCode(p)
    else:
      # just copy the line to the output:
      writeln(p.outp, p.line)
  close(p.inp)
  close(p.outp)

proc writeCommandLine() =
  stdout.writeln """
Lexim - Lexer generator for Nim
    (c) Andreas Rumpf 2015
Usage: inputfile [outputfile]"""

proc main =
  var
    p: TParser
    infile, outfile: string
  p.rules = @[]
  p.line = newStringOfCap(120)
  for i in 0..high(p.vars): p.vars[i] = ""
  var i = 1
  let paramc = paramCount()
  if paramc == 0:
    writeCommandline()
    quit(1)
  while i <= paramc:
    if infile.isNil:
      infile = paramStr(i)
    else:
      outfile = paramStr(i)
    inc(i)
  if outfile.isNil: outfile = changeFileExt(infile, "lexim")
  parse(p, infile, outfile)

main()
echo "Done."
