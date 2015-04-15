
import vm

doAssert match("(a b c)", re"\( .* \)")
doAssert match("while", re("while"))

doAssert "0158787".match(re"\d+")
doAssert "ABC 0232".match(re"\w+\s+\d+")
doAssert "ABC".match(re"\d+ | \w+")

doAssert matchLen("key", re"\w+") == 3

var pattern = re"[a-z0-9]+\s*=\s*[a-z0-9]+"
doAssert matchLen("key1=  cal9", pattern) == 11
doAssert match("abc", re"\Aabc\Z")

doAssert(not match("abcdef", re"^abc$"))

doAssert(not match("aef", re"\A(?:abc|def)\Z"))
doAssert(match("def", re"\A(?:abc|def)\Z"))
doAssert(not match("deffoo", re"\A(?:abc|def)\Z"))

doAssert(not match("deffoo", re"\b(?:abc|def)\b"))
doAssert(match("def foo", re"\b(?:abc|def)\b"))

doAssert(matchLen("def foo", re"\b(?:abc|def)\b") == 3)

doAssert(matchLen("def foo\C\L", re"\bdef\sfoo\n") == 9)

let complex = re"(\w+)" # |(a)bcxyz"

echoCode(complex)
if "abcc" =~ complex:
  echo matches
else:
  assert false

#echo matchLen("abc", complex) # == 3

when true:
  let complex2 = re"((a+)b(c)\2)"
  echoCode complex2
  if "aaaaabcc" =~ complex2:
    echo matches
    #for x in matches: echo x
    #assert matches[1] == "abc"
  else:
    assert false

when false:
  if "abc" =~ re"(cba)?.*":
    assert matches[0] == nil
  else: assert false

  if "abc" =~ re"().*":
    assert matches[0] == ""
  else: assert false
