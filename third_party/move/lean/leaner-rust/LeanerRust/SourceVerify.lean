-- Copyright © Aptos Foundation
-- SPDX-License-Identifier: Apache-2.0

import LeanerRust.Driver
import LeanerLang.SourceVerify

/-!
# Verifying a Rust source

A Rust file carries no specifications of its own: they are LeanerLang items —
`spec` blocks, specification functions, invariants — in a file beside it,
`<name>.spec.lean` for `<name>.rs` unless another is named. The file is
exported through rustc, its crate rendered as LeanerLang with those items
appended and verified, and every message reported in the coordinates of the
Rust file or of the specification file.
-/

namespace LeanerIR.Rust.SourceVerify

open LeanerLang.SourceVerify

/-- The specification file of a Rust source: the one named, or
`<name>.spec.lean` beside `<name>.rs` when it exists. -/
def specsFor (source : System.FilePath) (named : Option System.FilePath) :
    IO (Option Specs) := do
  let conventional := source.withExtension "spec.lean"
  let path? ← match named with
    | some path => pure (some path)
    | none => pure <| if ← conventional.pathExists then some conventional else none
  path?.mapM fun path => return { path, text := ← IO.FS.readFile path }

/-- Verify a Rust file against its specification file, writing the
LeanerLang rendering to `output`. -/
def verifyFile (environment : Lean.Environment) (source : System.FilePath)
    (specFile : Option System.FilePath) (output : System.FilePath)
    (rustcArgs : Array String := #[]) : IO (Array Report) := do
  let unit ← IO.FS.withTempDir fun directory =>
    return (← Driver.importRustFile {
      source, output := directory / "unit.raw.json", rustcArgs }).unit
  run environment { unit, specs := ← specsFor source specFile, output }

end LeanerIR.Rust.SourceVerify
