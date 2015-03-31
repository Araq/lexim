#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import
  strutils, regexprs, listing

const
  maxLabel* = 255

type
  TRuleIndex* = range[0..10_000]
  TLabel* = range[0..maxLabel] # 0 is an invalid label number, indicating there is no
                               # transition
  TLabelSet* = set[TLabel]    # max. size may be bigger in Nim
                              # transition tables: if label = 0,
                              # it is the start node
  TDFA_Trans* = array[TLabel, array[char, TLabel]] # transitions for DFA's
                                                   # label = 1 is the start node
  TNFA_Trans* = array[TLabel, array[char, TLabelSet]] # transitions for NFA's
                                                      # epsilon transitions have char index = \0
                                                      # label 0 is the start node
  TLabelToRule* = array[TLabel, TRuleIndex]
  TDFA* = object
    startState*: int          # start state; for some reason it won't always be 1
    stateCount*: int          # number of states; states are from 1 to stateCount
    ruleCount*: int           # number of rules; rule 0 means no match
    trans*: TDFA_Trans
    toRules*: TLabelToRule

  TNFA* = object              # 2 Megabytes is a bit much for this...
                              # however, we will only have one...
    trans*: TNFA_Trans
    toRules*: TLabelToRule

proc initNFA(a: var TNFA) = discard
proc initDFA(a: var TDFA) = discard

proc auxRegExprToNFA(r: PRegExpr; a: var TNFA; currState: int): int =
  # helper that is recursive; returns the new current state
  result = currState
  assert(r != nil)
  if r == nil: return
  case r.regType
  of reEps:
    incl(a.trans[result]['\0'], result + 1)
    inc(result)
  of reChar:
    incl(a.trans[result][r.c], result + 1)
    inc(result)
  of reStr:
    # string node
    for i in countup(0, <len(r.s)):
      incl(a.trans[result][r.s[i]], result + 1)
      inc(result)
  of reCat:
    # concatenation node
    result = auxRegExprToNFA(r.a, a, result)
    result = auxRegExprToNFA(r.b, a, result)
  of reCClass:
    assert(not ('\0' in r.cc[]))
    incl(a.trans[result]['\0'], result + 1)
    inc(result)
    for c in countup('\x01', '\xFF'):
      if c in r.cc[]:
        incl(a.trans[result][c], result + 1)
    inc(result)
  of reStar:
    # star node
    # we draw one transition too much, which shouldn't be wrong
    let aa = auxRegExprToNFA(r.a, a, result)
    incl(a.trans[result]['\0'], aa + 1)
    incl(a.trans[aa]['\0'], aa + 1)
    incl(a.trans[aa + 1]['\0'], result)
    result = aa + 1
  of rePlus:
    # plus node
    # constructed as M M* would be:
    result = auxRegExprToNFA(catExpr(r.a, starExpr(r.a)), a, result)
  of reOpt:
    # option node
    # constructed as M | eps would be:
    result = auxRegExprToNFA(altExpr(r.a, epsExpr()), a, result)
  of reAlt:
    # (|) node
    # I don't understand why we need this epsilon transition here, but
    # without it, the algorithm doesn't work (the literature also says
    # this transition is needed, but doesn't give any explanation)
    incl(a.trans[result]['\0'], result + 1)
    inc(result)
    let oldState = result
    let aa = auxRegExprToNFA(r.a, a, result)
    let bb = auxRegExprToNFA(r.b, a, aa + 1)
    incl(a.trans[oldState]['\0'], aa + 1)
    incl(a.trans[aa]['\0'], bb + 1)
    incl(a.trans[bb]['\0'], bb + 1)
    result = bb + 1
  else: assert(false)
  if r.rule != 0: a.toRules[result] = r.rule

proc regExprToNFA*(r: PRegExpr; a: var TNFA) =
  #var
  #  startState, endState: Integer;
  #
  #  startState := 0;
  #  endState := 0;
  initNFA(a)
  discard auxRegExprToNFA(r, a, 0)    #, startState, endState

proc printDFA(a: TDFA) =
  echo("number of states: ", a.stateCount)
  echo("number of rules: ", a.ruleCount)
  for L in countup(0, maxLabel):
    for c in countup('\x01', '\xFF'):
      if a.trans[L][c] != 0: echo(L, c, a.trans[L][c])
    if a.toRules[L] != 0: echo(L, " rule: ", a.toRules[L])

proc getTransCC*(a: TDFA; source, dest: TLabel): set[char] =
  result = {}
  for c in countup('\0', '\xFF'):
    if a.trans[source][c] == dest: incl(result, c)

proc getRule*(a: TDFA; s: TLabel): int = a.toRules[s]

proc getStateName(a: TDFA; s: TLabel): string =
  if a.toRules[s] == 0: result = 's' & $s
  else: result = 's' & $s & '_' & $a.toRules[s]

proc convertDFAtoDOT*(a: TDFA; name: string; txt: var File) =
  var cs: set[char]
  writeln(txt, "digraph ", name, " {")
  for L in countup(1, a.stateCount):
    if L == a.startState: writeln(txt, getStateName(a, L), " [shape=box];")
    for M in countup(1, a.stateCount):
      cs = getTransCC(a, L, M)
      if cs != {}:
        writeln(txt, getStateName(a, L), " -> ", getStateName(a, M),
                " [label=\"", listing.charSetOrCharStr(cs), "\"];")
  writeln(txt, '}')

proc closure(a: TNFA; S: TLabelSet): TLabelSet =
  var res: TLabelSet
  result = S
  while true:
    res = result
    for L in countup(0, maxLabel):
      if L in res:
        result = result + a.trans[L]['\0']
    if res == result: break

proc DFAedge(a: TNFA; d: TLabelSet; c: char): TLabelSet =
  var tmp: TLabelSet = {}
  for L in countup(0, maxLabel):
    if L in d:
      tmp = tmp + a.trans[L][c]
  result = closure(a, tmp)

type
  TStates = array[0..500, TLabelSet]

proc searchInStates(states: openarray[TLabelSet]; p: int; e: TLabelSet): int =
  # returns -1 if not found
  for i in countup(low(states), p):
    if states[i] == e:
      return i
  result = - 1

proc NFA_to_DFA*(a: TNFA; b: var TDFA) =
  # Look into 'Modern compiler implementation in Java' for reference of
  #  this algorithm.
  var
    p, j, minRule: int
    states: TStates
    e: TLabelSet
  states[0] = {}
  states[1] = closure(a, {0.TLabel}) # 0 is the start state
  p = 1
  j = 0
  while j <= p:
    for c in countup('\x01', '\xFF'):
      # '\0' does not belong to the alphabet!
      # because it is the epsilon transition
      e = DFAedge(a, states[j], c)
      let i = searchInStates(states, p, e)
      if i >= 0:
        b.trans[j][c] = i
      else:
        inc(p)
        states[p] = e
        b.trans[j][c] = p
    inc(j)
  for d in countup(low(TLabel), j - 1):
    minRule = high(int)
    for i in countup(low(TLabel), high(TLabel)):
      if i in states[d]:
        if (minRule > a.toRules[i]) and (a.toRules[i] != 0):
          minRule = a.toRules[i]
    if minRule == high(int):
      b.toRules[d] = 0
    else:
      b.toRules[d] = minRule
      if minRule > b.ruleCount: b.ruleCount = minRule
  b.stateCount = j - 1
  b.startState = 1            # for some reason this is always 1

proc getPreds(a: TDFA; s: TLabelSet; c: char): TLabelSet =
  # computes the set of predecessors for the set s (under the character c)
  result = {}
  for i in countup(1, a.stateCount):
    if a.trans[i][c] in s: incl(result, i)

proc card(s: TLabelSet; maxState: int): int =
  result = 0
  for i in countup(1, maxState):
    if i in s: inc(result)

proc choose(s: TLabelSet; maxState: int): TLabel =
  # choose an arbitrary element from s
  assert(s != {})
  for i in countup(1, maxState):
    if i in s:
      return i
  result = 0                  # invalid state

proc optimizeDFA*(a: TDFA; b: var TDFA) =
  # Optimizes the DFA a to produce a minimal DFA.
  # We use Hopcroft's algorithm; see the paper coming with this source.
  # We have different types of nodes: there is a one to one correspondence
  # between type and matching rule.
  var
    w, p: seq[TLabelSet] = @[]     # p[0], w[0] are unused
    wlen, plen, findRes: int
    s, I, R: TLabelSet
    x, y: TLabelSet
    repr: TLabel              # representant of a label set
  # assign each state to a partition and to the worklist:
  # w := {F, S-F}; p := {F, S-F}
  setlen(w, a.ruleCount + 1)
  setlen(p, a.ruleCount + 1)
  for d in countup(1, a.stateCount):
    incl(w[a.toRules[d]], d)
    incl(p[a.toRules[d]], d)
  wlen = a.ruleCount + 1
  plen = a.ruleCount + 1
  while wlen > 0:
    dec(wlen)
    s = w[wLen]
    setlen(w, wLen)           # remove s from w;
    for c in countup('\x01', '\xFF'):
      I = getPreds(a, s, c)
      if I == {}:
        continue              # speed things up
      for j in countdown(plen - 1, 0):
        R = p[j]
        if (R * I != {}) and not (R <= I):
          # partition R into x, y
          x = R * I
          y = R - x           # replace R by x and y in P:
          inc(plen)
          setlen(p, plen)
          p[j] = x
          p[plen - 1] = y
          findRes = searchInStates(w, wlen - 1, R)
          if findRes >= 0:
            # R is elem of W, so replace R by x, y
            w[findRes] = x
            inc(wlen)
            setlen(w, wlen)
            w[wlen - 1] = y
          else:
            inc(wlen)
            setlen(w, wlen)
            if (card(x, a.stateCount) <= card(y, a.stateCount)): # add y to W:
              w[wlen - 1] = x
            else:
              w[wlen - 1] = y
  b.stateCount = plen         # new states
  b.ruleCount = a.ruleCount   # rule count stays the same
  for j in countup(0, plen - 1):
    if p[j] != {}:
      repr = choose(p[j], a.stateCount) # choose a representant of the set
      if a.startState in p[j]: b.startState = j + 1
      b.toRules[j + 1] = a.toRules[repr]
      for c in countup('\x01', '\xFF'):
        if a.trans[repr][c] != 0:
          # test to speed things up
          for k in countup(0, plen - 1):
            if a.trans[repr][c] in p[k]:
              b.trans[j + 1][c] = k + 1
              break
