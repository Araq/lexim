#
#
#    Lexim - The Lexer Generator for Nim
#        (c) Copyright 2015 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import
  regexprs

const
  maxLabel* = 255

type
  Alphabet* = object
    kind*: RegexKind
    val*: char

const
  alEpsilon* = Alphabet(kind: reEps, val: '\0')

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
    captures*, backrefs*: int
    ruleCount*: int           # number of rules; rule 0 means no match
    trans*: DFA_Trans
    toRules*: TLabelToRule

  NFA* = object
    captures, backrefs, stateCount: int
    trans*: NFA_Trans
    toRules*: TLabelToRule

proc initNFA(a: var NFA) = discard
proc initDFA(a: var DFA) = discard

proc addTrans(src: var seq[NFA_Edge]; c: Alphabet; d: TLabel) =
  for i in 0 .. high(src):
    if src[i].cond == c:
      src[i].dest.incl d
      return
  src.add(NFA_Edge(cond: c, dest: {d}))
  if c.kind == reEps and src.len != 1:
    # make epsilon always the first transition to speed up later passes:
    swap(src[0], src[src.high])

proc addTrans(src: var seq[DFA_Edge]; c: Alphabet; d: TLabel) =
  for i in 0 .. high(src):
    if src[i].cond == c:
      src[i].dest = d
      return
  src.add(DFA_Edge(cond: c, dest: d))

proc auxRegExprToNFA(r: PRegExpr; a: var NFA; currState: int): int =
  # helper that is recursive; returns the new current state
  result = currState
  assert(r != nil)
  if r == nil: return
  case r.kind
  of reEps:
    addTrans(a.trans[result], alEpsilon, result + 1)
    inc(result)
  of reChar:
    addTrans(a.trans[result], Alphabet(kind: reChar, val: r.c), result + 1)
    inc(result)
  of reWordBoundary, reWordBoundaryNot, reBegin, reEnd:
    addTrans(a.trans[result], Alphabet(kind: r.kind, val: '\0'), result + 1)
    inc(result)
  of reStr:
    # string node
    for i in countup(0, len(r.s)-1):
      addTrans(a.trans[result], Alphabet(kind: reChar, val: r.s[i]), result + 1)
      inc(result)
  of reCat:
    # concatenation node
    result = auxRegExprToNFA(r.a, a, result)
    result = auxRegExprToNFA(r.b, a, result)
  of reCClass:
    addTrans(a.trans[result], alEpsilon, result + 1)
    inc(result)
    for c in countup('\0', '\xFF'):
      if c in r.cc[]:
        addTrans(a.trans[result], Alphabet(kind: reChar, val: c), result + 1)
    inc(result)
  of reStar:
    # star node
    # we draw one transition too much, which shouldn't be wrong
    let aa = auxRegExprToNFA(r.a, a, result)
    addTrans(a.trans[result], alEpsilon, aa + 1)
    addTrans(a.trans[aa], alEpsilon, aa + 1)
    addTrans(a.trans[aa + 1], alEpsilon, result)
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
    addTrans(a.trans[result], alEpsilon, result + 1)
    inc(result)
    let oldState = result
    let aa = auxRegExprToNFA(r.a, a, result)
    let bb = auxRegExprToNFA(r.b, a, aa + 1)
    addTrans(a.trans[oldState], alEpsilon, aa + 1)
    addTrans(a.trans[aa], alEpsilon, bb + 1)
    addTrans(a.trans[bb], alEpsilon, bb + 1)
    result = bb + 1
  of reCapture, reCaptureEnd:
    a.captures = max(a.captures, int(r.c))
    addTrans(a.trans[result], Alphabet(kind: reCapture, val: r.c), result+1)
    inc(result)
    result = auxRegExprToNFA(r.a, a, result)
    addTrans(a.trans[result], Alphabet(kind: reCaptureEnd, val: r.c), result+1)
    inc(result)
  of reBackref:
    a.backrefs = max(a.backrefs, int(r.c))
    addTrans(a.trans[result], Alphabet(kind: reBackref, val: r.c), result + 1)
    inc(result)
  if r.rule != 0: a.toRules[result] = r.rule

proc regExprToNFA*(r: PRegExpr; a: var NFA) =
  initNFA(a)
  a.stateCount = auxRegExprToNFA(r, a, 0)

proc allTransitions*(a: DFA; source, dest: TLabel): (seq[Alphabet], set[char]) =
  result[0] = @[]
  if a.trans[source].len > 0:
    result[1] = {}
    var card = 0
    var lastChar = -1
    for x in a.trans[source]:
      if x.dest == dest:
        if x.cond.kind == reChar:
          inc card
          if lastChar < 0: lastChar = int x.cond.val
          result[1].incl x.cond.val
        else:
          result[0].add x.cond
    if card == 1:
      result[1] = {}
      result[0].add Alphabet(kind: reChar, val: char lastChar)

iterator allDests*(a: DFA; source: TLabel): TLabel =
  if a.trans[source].len > 0:
    # use a set to eliminate duplicates:
    var dests: TLabelSet
    for x in a.trans[source]: dests.incl x.dest
    for d in dests: yield d

proc getRule*(a: DFA; s: TLabel): int = a.toRules[s]

proc closure(a: NFA; S: TLabelSet): TLabelSet =
  var res: TLabelSet
  result = S
  while true:
    res = result
    for L in countup(0, a.stateCount):
      if L in res:
        if a.trans[L].len > 0 and a.trans[L][0].cond.kind == reEps:
          result = result + a.trans[L][0].dest
    if res == result: break

proc getDest(a: seq[NFA_Edge]; c: Alphabet): TLabelSet =
  if a.len == 0: return
  for t in a:
    if t.cond.kind == c.kind and t.cond.val == c.val: return t.dest

proc getDest(a: seq[DFA_Edge]; c: Alphabet): TLabel =
  if a.len == 0: return
  for t in a:
    if t.cond.kind == c.kind and t.cond.val == c.val: return t.dest

proc getDFAedge(a: NFA; d: TLabelSet; c: Alphabet): TLabelSet =
  var tmp: TLabelSet = {}
  for L in countup(0, a.stateCount):
    if L in d:
      tmp = tmp + getDest(a.trans[L], c)
  result = closure(a, tmp)

proc searchInStates(states: openarray[TLabelSet]; p: int; e: TLabelSet): int =
  # returns -1 if not found
  for i in countup(0, p):
    if states[i] == e: return i
  result = -1

proc fullAlphabet(captures, backrefs: int): seq[Alphabet] =
  result = @[]
  var c: Alphabet
  c.kind = reChar
  for x in '\0'..'\255':
    c.val = x
    result.add c
  c.kind = reBackref
  for x in 1..backrefs:
    c.val = char(x)
    result.add c
  for x in 1..captures:
    c.val = char(x)
    c.kind = reCapture
    result.add c
    c.kind = reCaptureEnd
    result.add c
  c.val = '\0'
  c.kind = reBegin
  result.add c
  c.kind = reEnd
  result.add c
  c.kind = reWordBoundary
  result.add c
  c.kind = reWordBoundaryNot
  result.add c

proc fullAlphabet*(a: NFA): seq[Alphabet] = fullAlphabet(a.captures, a.backrefs)

proc NFA_to_DFA*(a: NFA; b: var DFA; fullAlphabet: seq[Alphabet]) =
  # Look into 'Modern compiler implementation in Java' for reference of
  # this algorithm.
  var
    states: seq[TLabelSet] = @[]
  states.add({})
  states.add closure(a, {0.TLabel}) # 0 is the start state
  var p = 1
  var j = 0
  while j <= p:
    for c in fullAlphabet:
      let e = getDFAedge(a, states[j], c)
      let i = searchInStates(states, p, e)
      if i >= 0:
        addTrans(b.trans[j], c, i)
      else:
        inc(p)
        assert p == states.len
        states.add e
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
  b.captures = a.captures
  b.backrefs = a.backrefs

proc getPreds(a: DFA; s: TLabelSet; c: Alphabet): TLabelSet =
  # computes the set of predecessors for the set s (under the character c)
  result = {}
  let k = c.kind
  let v = c.val
  for i in countup(1, a.stateCount):
    for t in a.trans[i]:
      if t.cond.kind == k and t.cond.val == v and t.dest in s:
        incl(result, i)

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

proc optimizeDFA*(a: DFA; b: var DFA; fullAlphabet: seq[Alphabet]) =
  # Optimizes the DFA a to produce a minimal DFA.
  # We use Hopcroft's algorithm; see the paper coming with this source.
  # We have different types of nodes: there is a one to one correspondence
  # between type and matching rule.
  b.captures = a.captures
  b.backrefs = a.backrefs
  # p[0], w[0] are unused
  # assign each state to a partition and to the worklist:
  # w := {F, S-F}; p := {F, S-F}
  var w = newSeq[TLabelSet](a.ruleCount+1)
  var p = newSeq[TLabelSet](a.ruleCount+1)
  for d in countup(1, a.stateCount):
    incl(w[a.toRules[d]], d)
    incl(p[a.toRules[d]], d)
  while w.len > 0:
    let s = w.pop
    for c in fullAlphabet:
      let I = getPreds(a, s, c)
      if I == {}:
        continue              # speed things up
      for j in countdown(p.len - 1, 0):
        let R = p[j]
        if (R * I != {}) and not (R <= I):
          # partition R into x, y
          let x = R * I
          let y = R - x           # replace R by x and y in P:
          p[j] = x
          p.add y
          let findRes = searchInStates(w, w.len - 1, R)
          if findRes >= 0:
            # R is elem of W, so replace R by x, y
            w[findRes] = x
            w.add y
          else:
            if card(x, a.stateCount) <= card(y, a.stateCount): # add y to W:
              w.add x
            else:
              w.add y
  b.stateCount = p.len        # new states
  b.ruleCount = a.ruleCount   # rule count stays the same
  for j in countup(0, p.len - 1):
    if p[j] != {}:
      let repr = choose(p[j], a.stateCount) # choose a representant of the set
      if a.startState in p[j]: b.startState = j + 1
      b.toRules[j + 1] = a.toRules[repr]
      for c in fullAlphabet:
        let dest = a.trans[repr].getDest(c)
        if dest != 0:
          # test to speed things up
          for k in countup(0, p.len - 1):
            if dest in p[k]:
              addTrans b.trans[j + 1], c, k + 1
              break
