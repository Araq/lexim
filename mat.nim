
include matcher

while true:
  let inp = readLine(stdin)
  if inp.len == 0: break
  echo matches(inp)
