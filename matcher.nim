proc matches(input: string): int =
  var state: range[1..11] = 11
  var i = 0
  while true:
    case state
    of 1:
      if input[i] == 'g': inc i; state = 2
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'f', 'h'..'o', 'q'..'\255'}: inc i; state = 11
      else: return 0
    of 2:
      return 1
    of 3:
      if input[i] == 'i': inc i; state = 4
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'h', 'j'..'o', 'q'..'\255'}: inc i; state = 11
      else: return 0
    of 4:
      if input[i] == 'n': inc i; state = 1
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'m', 'o', 'q'..'\255'}: inc i; state = 11
      else: return 0
    of 5:
      if input[i] == 'r': inc i; state = 3
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'o', 'q', 's'..'\255'}: inc i; state = 11
      else: return 0
    of 6:
      if input[i] == 'u': inc i; state = 5
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'o', 'q'..'t', 'v'..'\255'}: inc i; state = 11
      else: return 0
    of 7:
      if input[i] == 's': inc i; state = 6
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'o', 'q', 'r', 't'..'\255'}: inc i; state = 11
      else: return 0
    of 8:
      if input[i] == 'a': inc i; state = 7
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'`', 'b'..'o', 'q'..'\255'}: inc i; state = 11
      else: return 0
    of 9:
      if input[i] == 'e': inc i; state = 8
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'d', 'f'..'o', 'q'..'\255'}: inc i; state = 11
      else: return 0
    of 10:
      if input[i] == 'l': inc i; state = 9
      elif input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'k', 'm'..'o', 'q'..'\255'}: inc i; state = 11
      else: return 0
    of 11:
      if input[i] == 'p': inc i; state = 10
      elif input[i] in {'\1'..'o', 'q'..'\255'}: inc i; state = 11
      else: return 0
