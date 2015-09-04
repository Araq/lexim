
version = "1.0"
author = "Andreas Rumpf"
description = "Lexer generation and regex implementation for Nim."
license = "MIT"

requires "nim >= 0.11.3"

import ospaths

proc buildHelper(name: string) =
  if not fileExists(name.toExe):
    exec "nim c " & name

task build, "builds Lexim and an example":
  buildHelper "lexe"
  exec "nim c ex1"
  setCommand "nop"

task tests, "test regular expressions":
  exec "nim c -r tests"
  setCommand "nop"
