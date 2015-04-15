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
  TLabel* = range[0..maxLabel] # 0 is an invalid label number, indicating
                               # there is no transition
  TLabelSet* = set[TLabel]    # max. size may be bigger in Nim
                              # transition tables: if label = 0,
                              # it is the start node
  DFA_Edge* = object
    cond*: Alphabet
    dest*: TLabel
  DFA_Trans* = array[TLabel, seq[DFA_Edge]] # transitions for DFA's
                                            # label = 1 is the start node

  NFA_Edge* = object
    cond*: Alphabet
    dest*: TLabelSet
  NFA_Trans* = array[TLabel, seq[NFA_Edge]] # transitions for NFA's
                                            # label 0 is the start node
  TLabelToRule* = array[TLabel, TRuleIndex]
  DFA* = object
    startState*: int          # start state; for some reason it won't always be 1
    stateCount*: int          # number of states; states are from 1 to stateCount
    ruleCount*: int           # number of rules; rule 0 means no match
    trans*: DFA_Trans
    toRules*: TLabelToRule

  NFA* = object
    trans*: NFA_Trans
    toRules*: TLabelToRule

  NfaFlag* = enum
    supportCapture

proc initNFA(a: var NFA) = discard
proc initDFA(a: var DFA) = discard

proc addTrans(src: var seq[NFA_Edge]; c: Alphabet; d: TLabel) =
  if src.isNil:
    src = @[NFA_Edge(cond: c, dest: {d})]
  else:
    for i in 0 .. high(src):
      if src[i].cond == c:
        src[i].dest.incl d
        return
    src.add(NFA_Edge(cond: c, dest: {d}))
    if c == alEpsilon and src.len != 1:
      # make epsilon always the first transition to speed up later passes:
      swap(src[0], src[src.high])

proc addTrans(src: var seq[DFA_Edge]; c: Alphabet; d: TLabel) =
  if src.isNil:
    src = @[DFA_Edge(cond: c, dest: d)]
  else:
    for i in 0 .. high(src):
      if src[i].cond == c:
        src[i].dest = d
        return
    src.add(DFA_Edge(cond: c, dest: d))

proc auxRegExprToNFA(r: PRegExpr; a: var NFA; currState: int;
                     flags: set[NfaFlag]): int =
  # helper that is recursive; returns the new current state
  result = currState
  assert(r != nil)
  if r == nil: return
  case r.kind
  of reEps:
    addTrans(a.trans[result], alEpsilon, result + 1)
    inc(result)
  of reChar:
    addTrans(a.trans[result], r.c, result + 1)
    inc(result)
  of reStr:
    # string node
    for i in countup(0, <len(r.s)):
      addTrans(a.trans[result], Alphabet(r.s[i]), result + 1)
      inc(result)
  of reCat:
    # concatenation node
    result = auxRegExprToNFA(r.a, a, result, flags)
    result = auxRegExprToNFA(r.b, a, result, flags)
  of reCClass:
    addTrans(a.trans[result], alEpsilon, result + 1)
    inc(result)
    for c in countup(0, 0xFF):
      if char(c) in r.cc[]:
        addTrans(a.trans[result], c, result + 1)
    inc(result)
  of reStar:
    # star node
    # we draw one transition too much, which shouldn't be wrong
    let aa = auxRegExprToNFA(r.a, a, result, flags)
    addTrans(a.trans[result], alEpsilon, aa + 1)
    addTrans(a.trans[aa], alEpsilon, aa + 1)
    addTrans(a.trans[aa + 1], alEpsilon, result)
    result = aa + 1
  of rePlus:
    # plus node
    # constructed as M M* would be:
    result = auxRegExprToNFA(catExpr(r.a, starExpr(r.a)), a, result, flags)
  of reOpt:
    # option node
    # constructed as M | eps would be:
    result = auxRegExprToNFA(altExpr(r.a, epsExpr()), a, result, flags)
  of reAlt:
    # (|) node
    addTrans(a.trans[result], alEpsilon, result + 1)
    inc(result)
    let oldState = result
    let aa = auxRegExprToNFA(r.a, a, result, flags)
    let bb = auxRegExprToNFA(r.b, a, aa + 1, flags)
    addTrans(a.trans[oldState], alEpsilon, aa + 1)
    addTrans(a.trans[aa], alEpsilon, bb + 1)
    addTrans(a.trans[bb], alEpsilon, bb + 1)
    result = bb + 1
  of reCapture:
    if supportCapture in flags:
      assert r.rule > 0
      addTrans(a.trans[result], alCaptureBegin, result + 1)
      a.toRules[result] = r.rule
      inc(result)
      result = auxRegExprToNFA(r.a, a, result, flags)
      addTrans(a.trans[result], alCaptureEnd, result + 1)
      a.toRules[result] = r.rule
      inc(result)
    else:
      result = auxRegExprToNFA(r.a, a, result, flags)
  of reBackref:
    assert r.rule > 0
    addTrans(a.trans[result], alBackref, result + 1)
    a.toRules[result] = r.rule
    inc(result)
  if r.rule != 0: a.toRules[result] = r.rule

proc regExprToNFA*(r: PRegExpr; a: var NFA; flags: set[NfaFlag]) =
  initNFA(a)
  discard auxRegExprToNFA(r, a, 0, flags)

proc getTransCC*(a: DFA; source, dest: TLabel): set[Alphabet] =
  result = {}
  if not a.trans[source].isNil:
    for x in a.trans[source]:
      if x.dest == dest: result.incl x.cond

proc getRule*(a: DFA; s: TLabel): int = a.toRules[s]

proc closure(a: NFA; S: TLabelSet): TLabelSet =
  var res: TLabelSet
  result = S
  while true:
    res = result
    for L in countup(0, maxLabel):
      if L in res:
        if not a.trans[L].isNil and a.trans[L][0].cond == alEpsilon:
          result = result + a.trans[L][0].dest
    if res == result: break

proc getDest(a: seq[NFA_Edge]; c: Alphabet): TLabelSet =
  if a.isNil: return
  for t in a:
    if t.cond == c: return t.dest

proc getDest(a: seq[DFA_Edge]; c: Alphabet): TLabel =
  if a.isNil: return
  for t in a:
    if t.cond == c: return t.dest

proc getDFAedge(a: NFA; d: TLabelSet; c: Alphabet): TLabelSet =
  var tmp: TLabelSet = {}
  for L in countup(0, maxLabel):
    if L in d:
      tmp = tmp + getDest(a.trans[L], c)
  result = closure(a, tmp)

proc searchInStates(states: openarray[TLabelSet]; p: int; e: TLabelSet): int =
  # returns -1 if not found
  for i in countup(0, p):
    if states[i] == e: return i
  result = -1

proc NFA_to_DFA*(a: NFA; b: var DFA) =
  # Look into 'Modern compiler implementation in Java' for reference of
  # this algorithm.
  var
    states: seq[TLabelSet] = @[]
  states.add({})
  states.add closure(a, {0.TLabel}) # 0 is the start state
  var p = 1
  var j = 0
  while j <= p:
    for c in countup(0, alEpsilon-1):
      let e = getDFAedge(a, states[j], c)
      let i = searchInStates(states, p, e)
      if i >= 0:
        addTrans(b.trans[j], c, i)
      else:
        inc(p)
        if p >= states.len: setLen(states, p+1)
        states[p] = e
        addTrans(b.trans[j], c, p)
    inc(j)
  for d in countup(low(TLabel), j - 1):
    var minRule = high(int)
    for i in countup(low(TLabel), high(TLabel)):
      if i in states[d]:
        if minRule > a.toRules[i] and a.toRules[i] != 0:
          minRule = a.toRules[i]
    if minRule == high(int):
      b.toRules[d] = 0
    else:
      b.toRules[d] = minRule
      if minRule > b.ruleCount: b.ruleCount = minRule
  b.stateCount = j - 1
  b.startState = 1            # for some reason this is always 1

proc getPreds(a: DFA; s: TLabelSet; c: Alphabet): TLabelSet =
  # computes the set of predecessors for the set s (under the character c)
  result = {}
  for i in countup(1, a.stateCount):
    for t in a.trans[i]:
      if t.cond == c and t.dest in s: incl(result, i)

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

proc optimizeDFA*(a: DFA; b: var DFA) =
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
    for c in countup(0, alEpsilon-1):
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
      for c in countup(0, alEpsilon-1):
        let dest = a.trans[repr].getDest(c)
        if dest != 0:
          # test to speed things up
          for k in countup(0, plen - 1):
            if dest in p[k]:
              addTrans b.trans[j + 1], c, k + 1
              break
