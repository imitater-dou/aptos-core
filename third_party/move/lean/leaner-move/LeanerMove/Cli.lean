-- Copyright © Aptos Foundation
-- SPDX-License-Identifier: Apache-2.0

import LeanerMove.SourceVerify

/-!
# The `leaner-move` command

`leaner-move verify <source>` exports a Move file or package directory
through compiler-v2, renders its modules as LeanerLang beside it
(`<source>.lean`, or `--output`), verifies every specified function, and
reports each message at its position in the Move sources.
-/

namespace LeanerMove.Cli

open LeanerLang.SourceVerify

private def usage : String :=
  "usage: leaner-move verify <source.move | package directory> [--output <generated.lean>]"

private def fail (message : String) : IO α := throw <| IO.userError s!"{message}\n{usage}"

private partial def parseOutput (source : System.FilePath) :
    List String → Option System.FilePath → IO System.FilePath
  | [], output => pure <| output.getD (source.addExtension "lean")
  | "--output" :: path :: rest, none => parseOutput source rest (some path)
  | "--output" :: _, some _ => fail "--output may be specified only once"
  | argument :: _, _ => fail s!"unknown verify argument `{argument}`"

private def verifySource (source output : System.FilePath) : IO UInt32 := do
  let reports ← LeanerMove.SourceVerify.verifySource (← importLeanerLang) source output
  for report in reports do IO.println report.render
  IO.println s!"leaner-move: generated {output}"
  pure <| if reports.any (·.severity == .error) then 1 else 0

def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | "verify" :: source :: rest => verifySource source (← parseOutput source rest none)
  | _ => fail "expected a command"

end LeanerMove.Cli
