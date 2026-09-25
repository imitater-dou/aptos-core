-- Copyright © Aptos Foundation
-- SPDX-License-Identifier: Apache-2.0

import LeanerMove.Frontend
import LeanerLang.SourceVerify

/-!
# Verifying a Move source

A Move file or package is exported through compiler-v2, its modules rendered
as LeanerLang in dependency order and verified, and every message reported in the Move file's
coordinates. Its specifications are the Move `spec` blocks it declares.
-/

namespace LeanerMove.SourceVerify

open LeanerLang.SourceVerify

/-- Verify a Move file, or the modules of a Move package directory, writing
the LeanerLang rendering to `output`. -/
def verifySource (environment : Lean.Environment) (source output : System.FilePath) :
    IO (Array Report) := do
  let package ← if ← source.isDir then LeanerMove.Frontend.Cli.exportPackage source
    else LeanerMove.Frontend.Cli.exportMoveFiles [source]
  match LeanerMove.Frontend.LIR.Backend.fromXast package with
  | .ok unit => run environment { unit, output }
  | .error message => throw <| IO.userError s!"{source}: {message}"

end LeanerMove.SourceVerify
