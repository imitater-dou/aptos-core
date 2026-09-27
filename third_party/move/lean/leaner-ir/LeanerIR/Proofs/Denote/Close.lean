-- Copyright © Aptos Foundation
-- SPDX-License-Identifier: Apache-2.0

import LeanerIR.Proofs.Denote.Agreement
import LeanerIR.Proofs.Order
import LeanerIR.Proofs.Denote.SimpAll
import LeanerIR.Proofs.Denote.BitLift

/-!
# Closing the verification condition of a denotation

After the `lir_denote` normalization a goal is a tree of conjunctions,
implications, and conditionals whose leaves are arithmetic over the
native values and their certificates, or decidable propositions.  The
closer splits the tree structurally and decides each leaf: certificates
become bounds, then `omega`; finite leaves go to `decide`.  A leaf that
no decision procedure closes is reported at the authored clause its
`Obligation` marker names.  Nothing here selects a route or matches a
goal shape.
-/

namespace LeanerIR.Proofs.Denote

open Lean Elab Tactic Meta

/-- Show the residual goal of a clause the closer cannot establish. -/
register_option leaner.certifyDebug : Bool := {
  defValue := false
  descr := "show the residual goal of a specification clause the closer cannot establish"
}

/-- Marks a function's arguments and state at its start, what the `old` of
its loop invariants reads: the verified function's, and each inlined
callee's at its call. A hypothesis rather than an equation, so that
substitution rewrites it instead of eliminating it. -/
def FunctionStart {α : Type} (_function : LeanerIR.FunctionHandle) (_arguments : α)
    (_state : LeanerIR.RuntimeState) : Prop := True

theorem FunctionStart.intro {α : Type} (function : LeanerIR.FunctionHandle) (arguments : α)
    (state : LeanerIR.RuntimeState) : FunctionStart function arguments state := trivial

/-- The range an `Obligation` marker names, when the expression is one. -/
def obligationRange? (e : Lean.Expr) : Option ObligationRange := do
  guard <| e.isAppOfArity ``Obligation 4
  let .lit (.strVal file) := (e.getArg! 0).consumeMData | none
  let startByte ← (e.getArg! 1).nat? <|> (e.getArg! 1).rawNatLit?
  let endByte ← (e.getArg! 2).nat? <|> (e.getArg! 2).rawNatLit?
  pure { file, startByte, endByte }

/-- The ranges of the `Obligation` markers in an expression. -/
partial def obligationRanges (expression : Lean.Expr) : Array ObligationRange :=
  let rec walk (e : Lean.Expr) (found : Array ObligationRange) : Array ObligationRange :=
    let found := match obligationRange? e with
      | some range => found.push range
      | none => found
    match e with
    | .app function argument => walk argument (walk function found)
    | .lam _ type body _ => walk body (walk type found)
    | .forallE _ type body _ => walk body (walk type found)
    | .letE _ type value body _ => walk body (walk value (walk type found))
    | .mdata _ body => walk body found
    | .proj _ _ body => walk body found
    | _ => found
  walk expression #[]

/-- Where a goal the closer splits off comes from, when no clause marker
locates it. -/
inductive Provenance where
  | precondition (callee : String)
  | continuation (callee : String)
  | loopEntry
  | loopIteration

def Provenance.describe : Provenance → String
  | .precondition callee => s!"the precondition of `{callee}`"
  | .continuation callee => s!"the continuation after `{callee}`"
  | .loopEntry => "a loop invariant at entry"
  | .loopIteration => "a loop invariant at an iteration"

/-- What an obligation located at an authored clause says: a loop's
invariant is owed at entry and after each iteration, any other clause by the
function. -/
private def clauseFailure (origin : Option Provenance) (snippet : String) : MessageData :=
  match origin with
  | some .loopEntry => m!"the loop invariant `{snippet}` is not established at entry"
  | some .loopIteration => m!"the loop invariant `{snippet}` is not preserved by an iteration"
  | _ => m!"the specification clause `{snippet}` is not established"

/-- Report a verification condition that was not established, at every
authored clause its `Obligation` markers — those in it and the `clauses` its
closing stripped — locate not yet reported with the same message, or, with
no marker, as `origin` or a residual obligation with its goal. Returns the
reports so far. -/
def reportObligation (goal : MVarId) (origin : Option Provenance)
    (clauses : Array ObligationRange) (reported : Array (ObligationRange × String)) :
    TacticM (Array (ObligationRange × String)) := do
  let fileMap ← getFileMap
  let fileName ← getFileName
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let ranges := (clauses ++ obligationRanges target).toList.eraseDups.filter
      fun range => range.startByte < range.endByte
    if ranges.isEmpty then
      match origin with
      | some origin => logError m!"{origin.describe} is not established"
      | none => logError m!"verification failed with a residual obligation:\n{(← Lean.Meta.ppGoal goal)}"
    let mut reported := reported
    for range in ranges do
      -- A clause of another module's file is reported in that file.
      let source? ← if range.file == fileName then pure (some fileMap.source) else
        try some <$> IO.FS.readFile range.file catch _ => pure none
      let snippet := match source? with
        | some source => Substring.Raw.toString ⟨source, ⟨range.startByte⟩, ⟨range.endByte⟩⟩
        | none => s!"{range.file}:{range.startByte}"
      let message := clauseFailure origin snippet
      let key := (range, ← message.toString)
      if reported.contains key then continue
      reported := reported.push key
      match source? with
      | some _ =>
          if range.file == fileName then
            logErrorAt (Syntax.atom (.synthetic ⟨range.startByte⟩ ⟨range.endByte⟩) snippet) message
          else
            let foreign := FileMap.ofString (source?.getD "")
            logMessage {
              fileName := range.file
              pos := foreign.toPosition ⟨range.startByte⟩
              endPos := some (foreign.toPosition ⟨range.endByte⟩)
              severity := .error
              data := ← addMessageContext message }
      | none => logError message
    if leaner.certifyDebug.get (← getOptions) && !(ranges.isEmpty && origin.isNone) then
      logError m!"residual obligation:\n{(← Lean.Meta.ppGoal goal)}"
    return reported

register_option leaner.denoteDebug : Bool := {
  defValue := false
  descr := "show the normalized verification condition of a denotation before closing"
}

/-- The unsigned certified integer a `.val` projection reads, with its width. -/
private def unsignedValue? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``LeanerIR.SpecInt.val 3 && (e.getArg! 1).isConstOf ``Bool.false &&
      (e.getArg! 0).isAppOfArity ``LeanerIR.IntWidth.bits 1 && !e.hasLooseBVars then
    some ((e.getArg! 0).getArg! 0, e.getArg! 2)
  else none
/-- The signed certified integer a `.val` projection reads, with its width. -/
private def signedValue? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``LeanerIR.SpecInt.val 3 && (e.getArg! 1).isConstOf ``Bool.true &&
      (e.getArg! 0).isAppOfArity ``LeanerIR.IntWidth.bits 1 && !e.hasLooseBVars then
    some ((e.getArg! 0).getArg! 0, e.getArg! 2)
  else none

/-- A proof that an integer term is nonnegative, from its structure: a
certified unsigned value, a nonnegative literal, and sums, products,
shifts, conjunctions, and remainders of nonnegative terms. -/
private partial def nonnegative? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if let some (_, value) := unsignedValue? e then
    return some (← mkAppM ``And.left #[← mkAppM ``LeanerIR.SpecInt.unsigned_bounds #[value]])
  if let some literal := e.int? <|> (e.nat?.map Int.ofNat) then
    if 0 ≤ literal then
      return some (← mkDecideProof (← mkAppM ``LE.le #[mkIntLit 0, e]))
    return none
  let both (lemma : Name) : MetaM (Option Lean.Expr) := do
    match ← nonnegative? (e.getArg! 4), ← nonnegative? (e.getArg! 5) with
    | some left, some right => some <$> mkAppM lemma #[left, right]
    | _, _ => pure none
  if e.isAppOfArity ``HAdd.hAdd 6 then return ← both ``Int.add_nonneg
  if e.isAppOfArity ``HMul.hMul 6 then return ← both ``Int.mul_nonneg
  if e.isAppOfArity ``Int.shiftLeft 2 then
    let some value ← nonnegative? (e.getArg! 0) | return none
    return some (← mkAppM ``LeanerIR.Proofs.Denote.shiftLeft_nonneg #[e.getArg! 0, e.getArg! 1, value])
  if e.isAppOfArity ``LeanerIR.Proofs.IntegerArithmetic.bitwiseAnd 2 then
    let some left ← nonnegative? (e.getArg! 0) | return none
    let some right ← nonnegative? (e.getArg! 1) | return none
    return some (← mkAppM ``LeanerIR.Proofs.IntegerArithmetic.bitwiseAnd_nonneg #[left, right])
  if e.isAppOfArity ``Int.tmod 2 then
    let some value ← nonnegative? (e.getArg! 0) | return none
    return some (← mkAppM ``Int.tmod_nonneg #[e.getArg! 1, value])
  if e.isAppOfArity ``HMod.hMod 6 then
    let modulus := e.getArg! 5
    let some literal := modulus.int? <|> (modulus.nat?.map Int.ofNat) | return none
    unless literal != 0 do return none
    let nonzero ← mkDecideProof (← mkAppM ``Ne #[modulus, mkIntLit 0])
    return some (← mkAppM ``Int.emod_nonneg #[e.getArg! 4, nonzero])
  return none

/-- Both facts, either, or none. -/
private def conjoin? : Option Lean.Expr → Option Lean.Expr → MetaM (Option Lean.Expr)
  | some left, some right => some <$> mkAppM ``And.intro #[left, right]
  | some fact, none | none, some fact => pure (some fact)
  | none, none => pure none

/-- The bound of one bit operation, when its operands are certified. -/
private def operationFact? (sub : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if sub.hasLooseBVars then return none
  if sub.isAppOfArity ``LeanerIR.Proofs.IntegerArithmetic.bitwiseAnd 2 then
    match unsignedValue? (sub.getArg! 0), unsignedValue? (sub.getArg! 1) with
    | some (_, left), some (_, right) =>
        return some (← mkAppM ``LeanerIR.Proofs.Denote.BitOp.eval_bounds
          #[mkConst ``LeanerIR.Proofs.Denote.BitOp.and, left, right])
    | _, _ =>
        match ← nonnegative? (sub.getArg! 0), ← nonnegative? (sub.getArg! 1) with
        | some left, some right =>
            return some (← mkAppM ``LeanerIR.Proofs.IntegerArithmetic.bitwiseAnd_nonneg
              #[left, right])
        | _, _ => return none
  -- A shift by a literal distance is a multiplication or division by a
  -- literal, which `omega` reads.
  let literalDistance := (sub.getArg! 1).nat?.isSome || (sub.getArg! 1).rawNatLit?.isSome
  if sub.isAppOfArity ``Int.shiftRight 2 then
    let division ← if literalDistance then
        some <$> mkAppM ``LeanerIR.Proofs.Denote.shiftRight_eq_div #[sub.getArg! 0, sub.getArg! 1]
      else pure none
    let bounds ← match unsignedValue? (sub.getArg! 0) with
      | some (_, value) =>
          some <$> mkAppM ``LeanerIR.Proofs.Denote.shiftRight_bounds #[value, sub.getArg! 1]
      | none => pure none
    return ← conjoin? bounds division
  if sub.isAppOfArity ``HMul.hMul 6 && (sub.getArg! 0).isConstOf ``Int then
    match unsignedValue? (sub.getArg! 4), unsignedValue? (sub.getArg! 5) with
    | some (_, left), some (_, right) =>
        return some (← mkAppM ``LeanerIR.Proofs.Denote.mul_unsigned_bounds #[left, right])
    | _, _ => return none
  if sub.isAppOfArity ``Int.tdiv 2 || sub.isAppOfArity ``Int.tmod 2 then
    match ← nonnegative? (sub.getArg! 0), ← nonnegative? (sub.getArg! 1) with
    | some leftNonnegative, some rightNonnegative =>
        let lemma := if sub.isAppOfArity ``Int.tdiv 2
          then ``LeanerIR.Proofs.Denote.tdiv_bounds_of_nonneg
          else ``LeanerIR.Proofs.Denote.tmod_bounds_of_nonneg
        return some (← mkAppM lemma #[leftNonnegative, rightNonnegative])
    | _, _ =>
        match signedValue? (sub.getArg! 0), signedValue? (sub.getArg! 1) with
        | some (width, left), some (_, right) =>
            let lemma := if sub.isAppOfArity ``Int.tdiv 2
              then ``LeanerIR.Proofs.Denote.tdiv_signed_range
              else ``LeanerIR.Proofs.Denote.tmod_signed_range
            return some (mkApp3 (mkConst lemma) width left right)
        | _, _ =>
            let lemma := if sub.isAppOfArity ``Int.tdiv 2
              then ``LeanerIR.Proofs.Denote.tdiv_facts
              else ``LeanerIR.Proofs.Denote.tmod_facts
            return some (mkApp2 (mkConst lemma) (sub.getArg! 0) (sub.getArg! 1))
  if sub.isAppOfArity ``Int.shiftLeft 2 then
    let product ← if literalDistance then
        some <$> mkAppM ``LeanerIR.Proofs.Denote.shiftLeft_eq_mul #[sub.getArg! 0, sub.getArg! 1]
      else pure none
    let nonnegative ← nonnegative? sub
    return ← conjoin? nonnegative product
  return none

/-- The bit operations a proposition mentions. -/
private partial def operationSites (e : Lean.Expr) : Array Lean.Expr :=
  let here := if e.isAppOfArity ``LeanerIR.Proofs.IntegerArithmetic.bitwiseAnd 2 ||
      e.isAppOfArity ``Int.shiftRight 2 || e.isAppOfArity ``Int.shiftLeft 2 ||
      e.isAppOfArity ``Int.tdiv 2 || e.isAppOfArity ``Int.tmod 2 ||
      e.isAppOfArity ``HMul.hMul 6 then #[e] else #[]
  match e with
  | .app f a => here ++ operationSites f ++ operationSites a
  | .lam _ t b _ | .forallE _ t b _ => here ++ operationSites t ++ operationSites b
  | .letE _ t v b _ => here ++ operationSites t ++ operationSites v ++ operationSites b
  | .mdata _ b | .proj _ _ b => here ++ operationSites b
  | _ => here

/-- The closed applications of structure projections a proposition mentions. -/
private partial def projectionSites (env : Environment) (e : Lean.Expr) : Array Lean.Expr :=
  let here := match e.getAppFn with
    | .const name _ =>
        if e.isApp && !e.hasLooseBVars && (env.getProjectionFnInfo? name).isSome then #[e] else #[]
    | _ => #[]
  match e with
  | .app f a => here ++ projectionSites env f ++ projectionSites env a
  | .lam _ t b _ | .forallE _ t b _ => here ++ projectionSites env t ++ projectionSites env b
  | .letE _ t v b _ => here ++ projectionSites env t ++ projectionSites env v ++ projectionSites env b
  | .mdata _ b | .proj _ _ b => here ++ projectionSites env b
  | _ => here

/-- The native type an encoding function encodes, from its spelling: the
typed `NTy.encode τ`, or the codec of a type. -/
partial def codecType? (encoder : Lean.Expr) : Option Lean.Expr := do
  if encoder.isAppOfArity ``LeanerIR.Proofs.Denote.NTy.encode 2 then return encoder.getArg! 1
  guard (encoder.isAppOfArity ``LeanerIR.Proofs.Codec.encode 3)
  codecOf (encoder.getArg! 2)
where
  codecOf (codec : Lean.Expr) : Option Lean.Expr := do
    let scalar (name : Name) (τ : Name) : Option Lean.Expr :=
      if codec.isConstOf name then some (mkConst τ) else none
    if codec.isAppOfArity ``LeanerIR.Proofs.Denote.NTy.codec 2 then return codec.getArg! 1
    if codec.isAppOfArity ``LeanerIR.Proofs.Codec.specInt 2 then
      let width := codec.getArg! 0
      guard (width.isAppOfArity ``LeanerIR.IntWidth.bits 1)
      return mkAppN (mkConst ``LeanerIR.Proofs.Denote.NTy.int) #[width.getArg! 0, codec.getArg! 1]
    if codec.isAppOfArity ``LeanerIR.Proofs.Codec.boundedVector 2 then
      return mkApp (mkConst ``LeanerIR.Proofs.Denote.NTy.vector) (← codecOf (codec.getArg! 1))
    if codec.isAppOfArity ``LeanerIR.Proofs.Codec.tuple 2 then
      let row := codec.getArg! 1
      guard (row.isAppOfArity ``LeanerIR.Proofs.Denote.rowCodec 2)
      return mkApp (mkConst ``LeanerIR.Proofs.Denote.NTy.tuple) (row.getArg! 1)
    if codec.isAppOfArity ``LeanerIR.Proofs.Denote.Codec.nominalRow 4 then
      guard ((codec.getArg! 2).isAppOfArity ``Option.none 1)
      let row := codec.getArg! 3
      guard (row.isAppOfArity ``LeanerIR.Proofs.Denote.rowCodec 2)
      return mkAppN (mkConst ``LeanerIR.Proofs.Denote.NTy.struct) #[codec.getArg! 1, row.getArg! 1]
    scalar ``LeanerIR.Proofs.Codec.bool ``LeanerIR.Proofs.Denote.NTy.bool <|>
      scalar ``LeanerIR.Proofs.Codec.address ``LeanerIR.Proofs.Denote.NTy.address <|>
      scalar ``LeanerIR.Proofs.Codec.signer ``LeanerIR.Proofs.Denote.NTy.signer <|>
      scalar ``LeanerIR.Proofs.Codec.string ``LeanerIR.Proofs.Denote.NTy.string <|>
      scalar ``LeanerIR.Proofs.Codec.bytes ``LeanerIR.Proofs.Denote.NTy.bytes <|>
      scalar ``LeanerIR.Proofs.Codec.unit ``LeanerIR.Proofs.Denote.NTy.unit

/-- Assert the facts a leaf needs beside its hypotheses: the bounds of every
certified integer in context, and the bounds of every bit operation on
them that the goal or a hypothesis mentions. A fact whose statement is in
`skip` is not asserted. The statements asserted are returned. -/
def assertBounds (skip : Array Lean.Expr := #[]) : TacticM (Array Lean.Expr) := do
  if (← getGoals).isEmpty then return #[]
  let goal ← getMainGoal
  let facts ← goal.withContext do
    let mut facts : Array Lean.Expr := #[]
    let mut expressions := #[← instantiateMVars (← goal.getType)]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← whnfR (← instantiateMVars decl.type)
      expressions := expressions.push (← instantiateMVars decl.type)
      if ty.isAppOfArity ``LeanerIR.SpecVector 1 then
        facts := facts.push (← mkAppM ``LeanerIR.SpecVector.bounded #[decl.toExpr])
      if ty.isAppOfArity ``LeanerIR.SpecInt 2 then
        let width := ty.getArg! 0
        if width.isAppOfArity ``LeanerIR.IntWidth.bits 1 then
          let lemma := if (ty.getArg! 1).isConstOf ``Bool.true
            then ``LeanerIR.SpecInt.signed_bounds else ``LeanerIR.SpecInt.unsigned_bounds
          facts := facts.push (mkApp2 (mkConst lemma) (width.getArg! 0) decl.toExpr)
    for expression in expressions do
      for site in operationSites expression do
        if let some fact ← operationFact? site then facts := facts.push fact
    -- A proof that does not assemble is not a fact.
    let attempt (fact : MetaM Lean.Expr) : MetaM (Option Lean.Expr) :=
      try pure (some (← fact)) catch _ => pure none
    let mapped? (e : Lean.Expr) : Option Lean.Expr :=
      if e.isAppOfArity ``Array.map 4 then codecType? (e.getArg! 2) else none
    -- Range certificates and their negations in context yield bounds as
    -- separate facts; rewriting them would leave casts in the terms that
    -- depend on them.
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      -- An encoding equated to a runtime value names the native value it
      -- decodes to, and one distinguished from it excludes that value.
      let equation := if ty.isAppOfArity ``LeanerIR.Proofs.Obligation 4 then ty.getArg! 3 else ty
      if equation.isAppOfArity ``Not 1 && (equation.getArg! 0).isAppOfArity ``Eq 3 then
        let inner := equation.getArg! 0
        let lhs := inner.getArg! 1
        let rhs := inner.getArg! 2
        -- Distinct certified values differ in their fields.
        let carrier ← whnfR (inner.getArg! 0)
        if carrier.isAppOfArity ``LeanerIR.SpecInt 2 then
          facts := facts.push (← mkAppM ``LeanerIR.Proofs.Denote.SpecInt.val_ne_of_ne #[decl.toExpr])
        else if carrier.isAppOfArity ``LeanerIR.SpecVector 1 then
          facts := facts.push
            (← mkAppM ``LeanerIR.Proofs.Denote.SpecVector.values_ne_of_ne #[decl.toExpr])
        let fact ← if lhs.isAppOfArity ``LeanerIR.Proofs.Denote.NTy.encode 3 then
            attempt (mkAppM ``LeanerIR.Proofs.Denote.NTy.decode?_ne_of_encode_ne #[decl.toExpr])
          else if let some τ := mapped? lhs then
            attempt (mkAppOptM ``LeanerIR.Proofs.Denote.NTy.decode?_vector_ne_of_map_ne
              #[none, τ, none, none, decl.toExpr])
          else pure none
        if let some fact := fact then facts := facts.push fact
      if equation.isAppOfArity ``Eq 3 then
        let proof ← if ty.isAppOfArity ``LeanerIR.Proofs.Obligation 4 then
            mkAppM ``Iff.mp #[← mkAppOptM ``LeanerIR.Proofs.Obligation_iff
              #[ty.getArg! 0, ty.getArg! 1, ty.getArg! 2, equation], decl.toExpr]
          else pure decl.toExpr
        let lhs := equation.getArg! 1
        let rhs := equation.getArg! 2
        let isRuntime (e : Lean.Expr) := match e.getAppFn with
          | .const name _ => name.getPrefix == ``LeanerIR.RuntimeValue
          | _ => false
        let decodeFact ← if lhs.isAppOfArity ``LeanerIR.Proofs.Denote.NTy.encode 3 && isRuntime rhs then
            attempt (mkAppM ``LeanerIR.Proofs.Denote.NTy.decode?_of_encode #[proof])
          else if rhs.isAppOfArity ``LeanerIR.Proofs.Denote.NTy.encode 3 && isRuntime lhs then
            attempt (mkAppM ``LeanerIR.Proofs.Denote.NTy.decode?_of_encode #[← mkEqSymm proof])
          else if let some τ := mapped? lhs then
            attempt (mkAppOptM ``LeanerIR.Proofs.Denote.NTy.decode?_vector_of_map
              #[none, τ, none, none, proof])
          else if let some τ := mapped? rhs then
            attempt (mkAppOptM ``LeanerIR.Proofs.Denote.NTy.decode?_vector_of_map
              #[none, τ, none, none, ← mkEqSymm proof])
          else pure none
        if let some fact := decodeFact then facts := facts.push fact
        -- An encoded enum value equated to a variant holds that variant.
        let variantFact ← if lhs.isAppOfArity ``LeanerIR.Proofs.Denote.NTy.encode 3 &&
              rhs.isAppOfArity ``LeanerIR.RuntimeValue.nominal 3 then
            attempt (mkAppM ``LeanerIR.Proofs.Denote.NTy.variantName_of_encode_enum #[proof])
          else if rhs.isAppOfArity ``LeanerIR.Proofs.Denote.NTy.encode 3 &&
              lhs.isAppOfArity ``LeanerIR.RuntimeValue.nominal 3 then
            attempt (mkAppM ``LeanerIR.Proofs.Denote.NTy.variantName_of_encode_enum
              #[← mkEqSymm proof])
          else pure none
        if let some fact := variantFact then facts := facts.push fact
      let (negated, fits) := if ty.isAppOfArity ``Not 1 then (true, ty.getArg! 0) else (false, ty)
      unless fits.isAppOfArity ``LeanerIR.IntegerValueFits 3 do continue
      let width := fits.getArg! 0
      unless width.isAppOfArity ``LeanerIR.IntWidth.bits 1 do continue
      let signed := (fits.getArg! 1).isConstOf ``Bool.true
      if negated then
        let some bits := (width.getArg! 0).nat? | continue
        if bits == 0 then continue
        let nonzero ← mkDecideProof (← mkAppM ``Ne #[width.getArg! 0, mkNatLit 0])
        let lemma := if signed then ``LeanerIR.Proofs.Denote.bounds_of_not_fits_signed
          else ``LeanerIR.Proofs.Denote.bounds_of_not_fits_unsigned
        facts := facts.push (← mkAppM lemma #[nonzero, decl.toExpr])
      else
        let lemma := if signed then ``LeanerIR.Proofs.Denote.bounds_of_fits_signed
          else ``LeanerIR.Proofs.Denote.bounds_of_fits_unsigned
        facts := facts.push (← mkAppM lemma #[decl.toExpr])
    -- Certified integers read through a structure projection, such as a
    -- twin's field, carry their bounds too.
    for expression in expressions do
      for site in projectionSites (← getEnv) expression do
        let ty ← whnfR (← inferType site)
        if ty.isAppOfArity ``LeanerIR.SpecInt 2 then
          let width := ty.getArg! 0
          if width.isAppOfArity ``LeanerIR.IntWidth.bits 1 then
            let lemma := if (ty.getArg! 1).isConstOf ``Bool.true
              then ``LeanerIR.SpecInt.signed_bounds else ``LeanerIR.SpecInt.unsigned_bounds
            facts := facts.push (mkApp2 (mkConst lemma) (width.getArg! 0) site)
    pure facts
  -- A fact already in context is not added again.
  let mut goal := goal
  let mut known ← goal.withContext do
    (← getLCtx).foldlM (init := skip) fun known decl => do
      if decl.isImplementationDetail then pure known
      else pure (known.push (← instantiateMVars decl.type))
  let mut added := #[]
  for proof in facts do
    let type ← goal.withContext (instantiateMVars (← inferType proof))
    if known.contains type then continue
    known := known.push type
    added := added.push type
    let asserted ← goal.assert `bounds type proof
    let (_, next) ← asserted.intro1P
    goal := next
    -- The projections of literal values in the fact reduce, so that a
    -- decision procedure reads the value, not the projection.
    setGoals [goal]
    let name := mkIdent `bounds
    evalTactic (← `(tactic| try dsimp only at $name:ident))
    goal ← getMainGoal
  replaceMainGoal [goal]
  return added

/-- Assert the bounds a leaf needs beside its hypotheses (`assertBounds`). -/
elab "leaner_denote_bounds" : tactic => discard assertBounds

/-- A structure projection applied to a constructor application, reduced. -/
private def reduceProjection? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let .const name _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? name | return none
  let arguments := e.getAppArgs
  let some value := arguments[info.numParams]? | return none
  let .const constructor _ := value.getAppFn | return none
  unless constructor == info.ctorName do return none
  let some field := value.getAppArgs[info.numParams + info.i]? | return none
  return some (mkAppN field (arguments.extract (info.numParams + 1) arguments.size))

/-- Reduce every projection of a constructor application, in the goal and in
every hypothesis. A substituted value leaves `{ val := e, … }.val` behind,
which arithmetic cannot see through; the reduction is a definitional change,
so it reaches the hypotheses other terms depend on, which `simp at *`
leaves alone. -/
elab "leaner_denote_reduce_projections" : tactic => do
  let mut goal ← getMainGoal
  let reduce (e : Lean.Expr) : MetaM Lean.Expr :=
    Meta.transform e (post := fun e => do
      match ← reduceProjection? e with
      | some reduced => return .visit reduced
      | none => return .continue)
  for decl in ← goal.withContext getLCtx do
    if decl.isImplementationDetail || decl.isLet then continue
    let type ← goal.withContext (instantiateMVars decl.type)
    let reduced ← goal.withContext (reduce type)
    if reduced != type then
      goal ← goal.replaceLocalDeclDefEq decl.fvarId reduced
  let target ← goal.withContext (instantiateMVars (← goal.getType))
  let reduced ← goal.withContext (reduce target)
  if reduced != target then goal ← goal.replaceTargetDefEq reduced
  replaceMainGoal [goal]

/-- Clear every hypothesis that speaks about computations rather than
values: the loop hypotheses and recursive iterations a leaf never needs. -/
elab "leaner_denote_clear_computations" : tactic => do
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let victims ← goal.withContext do
    let mut found := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      let constants := ty.getUsedConstants
      if constants.contains ``LeanerIR.Proofs.wp || constants.contains ``LeanerIR.Proofs.Spec ||
          constants.contains ``LeanerIR.Validation.prepareExecution ||
          constants.contains ``LeanerIR.Validation.ExecutableUnit ||
          constants.contains ``LeanerIR.Validation.SemanticsRegistry then
        found := found.push decl.fvarId
    pure found
  let mut goal := goal
  for fvarId in victims.reverse do
    goal ← goal.tryClear fvarId
  replaceMainGoal [goal]

/-- Consume the hypotheses a call leaves behind before a computation goal
is normalized again: an implication whose premise is decided by omega is
specialized, existentials and conjunctions are destructured, and the
equations on state components and on witnesses rewrite the goal. -/
elab "leaner_denote_consume" : tactic => do
  if (← getGoals).isEmpty then return
  let mut goal ← getMainGoal
  -- Specialize decided implications.
  let mut progress := true
  while progress do
    progress := false
    let candidate ← goal.withContext do
      (← getLCtx).findDeclM? fun decl => do
        if decl.isImplementationDetail then return none
        let ty ← instantiateMVars decl.type
        unless ty.isArrow do return none
        let premise := ty.bindingDomain!
        if premise.hasLooseBVars then return none
        unless ← isProp premise do return none
        if premise.getUsedConstants.contains ``LeanerIR.Proofs.wp then return none
        return some (decl.fvarId, premise, ty.bindingBody!)
    if let some (fvarId, premise, conclusion) := candidate then
      let saved ← saveState
      try
        let premiseProof ← goal.withContext do
          let syntactic ← (← getLCtx).findDeclM? fun decl => do
            if decl.isImplementationDetail then return none
            return if (← instantiateMVars decl.type) == premise then some decl.toExpr else none
          match syntactic with
          | some proof => pure proof
          | none =>
              let proof ← mkFreshExprMVar premise
              setGoals [proof.mvarId!]
              evalTactic (← `(tactic| omega))
              pure proof
        let specialized ← goal.withContext do
          instantiateMVars (mkApp (mkFVar fvarId) premiseProof)
        let asserted ← goal.assert `consumed conclusion specialized
        let (_, next) ← asserted.intro1P
        goal ← next.tryClear fvarId
        progress := true
      catch _ =>
        restoreState saved
        -- Leave it; a later leaf may still use it.
        pure ()
      if !progress then break
  -- Destructure existentials and conjunctions.
  progress := true
  while progress do
    progress := false
    let compound ← goal.withContext do
      (← getLCtx).findDeclM? fun decl => do
        if decl.isImplementationDetail then return none
        let ty ← instantiateMVars decl.type
        return if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then some decl.fvarId else none
    if let some fvarId := compound then
      match ← goal.cases fvarId with
      | #[subgoal] =>
          goal := subgoal.mvarId
          progress := true
      | _ => break
  -- Substitute witness equations: a variable that is not a state.
  progress := true
  while progress do
    progress := false
    let witness ← goal.withContext do
      (← getLCtx).findDeclM? fun decl => do
        if decl.isImplementationDetail then return none
        let ty ← instantiateMVars decl.type
        unless ty.isAppOfArity ``Eq 3 do return none
        let isWitness (e : Lean.Expr) : MetaM Bool := do
          unless e.isFVar do return false
          let type ← whnfR (← inferType e)
          return !type.isConstOf ``LeanerIR.RuntimeState
        if ← isWitness (ty.getArg! 2) then return some decl.fvarId
        if ← isWitness (ty.getArg! 1) then return some decl.fvarId
        return none
    if let some fvarId := witness then
      try
        goal ← Lean.Meta.subst goal fvarId
        progress := true
      catch _ => pure ()
  -- Rewrite with state-component equations.
  let equations ← goal.withContext do
    let mut found := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``Eq 3 then
        let lhs := ty.getArg! 1
        if lhs.isApp && lhs.appArg!.isFVar && lhs.isAppOfArity ``LeanerIR.RuntimeState.globals 1 then
          found := found.push decl.fvarId
    pure found
  setGoals [goal]
  if !equations.isEmpty then
    let idents ← equations.mapM fun fvarId => do
      let name := (← goal.withContext (fvarId.getDecl)).userName
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident)
    evalTactic (← `(tactic| try simp only [$idents,*]))

/-- The constructor a term applies, when it is a full application of a
constructor with fields. -/
private def fieldConstructor? (e : Lean.Expr) : MetaM (Option Name) := do
  let .const name _ := e.getAppFn | return none
  match (← getEnv).find? name with
  | some (.ctorInfo info) =>
      return if info.numFields > 0 && e.getAppNumArgs == info.numParams + info.numFields then
        some name else none
  | _ => return none

/-- A loop invariant's elimination over a slot it asserts defined: the
slot and the invariant at its value. -/
private def slotElimination? (ty : Lean.Expr) : MetaM (Option (FVarId × Lean.Expr)) := do
  if ty.isAppOfArity ``Option.elim 5 && (ty.getArg! 3).isConstOf ``False then
    -- The slot is a projection of the row until the row is destructured.
    match ← whnfR (ty.getArg! 2) with
    | .fvar slot => return some (slot, ty.getArg! 4)
    | _ => return none
  else return none

/-- Split every conjunctive or existential hypothesis into its parts,
every row-valued variable into its components, and every slot an
invariant asserts defined into its value, so that a leaf is over
scalars. -/
elab "leaner_denote_split_hypotheses" : tactic => do
  if (← getGoals).isEmpty then return
  let mut goal ← getMainGoal
  let mut progress := true
  while progress do
    progress := false
    let conjunction ← goal.withContext do
      (← getLCtx).findDeclM? fun decl => do
        if decl.isImplementationDetail then return none
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then return some decl.fvarId
        if (← whnfD ty).isAppOfArity ``Prod 2 then return some decl.fvarId
        if (← slotElimination? ty).isSome then return some decl.fvarId
        -- Two constructor applications equated, whatever type the equation
        -- is stated at: a pair splits into its components, a variant into
        -- its payload, and different variants refute the context.
        if ty.isAppOfArity ``Eq 3 then
          if (← fieldConstructor? (ty.getArg! 1)).isSome then
            if (← fieldConstructor? (ty.getArg! 2)).isSome then return some decl.fvarId
        return none
    if let some fvarId := conjunction then
      let isConstructorEquation ← goal.withContext do
        let ty ← instantiateMVars (← fvarId.getType)
        if ty.isAppOfArity ``Eq 3 then return (← fieldConstructor? (ty.getArg! 1)).isSome
        return false
      if isConstructorEquation then
        match ← Lean.Meta.injection goal fvarId with
        | Lean.Meta.InjectionResult.subgoal subgoal _ _ =>
            goal := subgoal
            progress := true
        | Lean.Meta.InjectionResult.solved =>
            replaceMainGoal []
            return
      else if let some (slot, _) ← goal.withContext do
          slotElimination? (← instantiateMVars (← fvarId.getType)) then
        -- A slot a loop invariant asserts defined: the empty case refutes
        -- the context, and the defined case reads the invariant at the
        -- value, by definition.
        let mut defined := none
        for subgoal in ← goal.cases slot do
          let hypothesis := subgoal.subst.get fvarId
          match subgoal.ctorName with
          | some ``Option.none =>
              subgoal.mvarId.withContext do
                subgoal.mvarId.assign (← mkFalseElim (← subgoal.mvarId.getType) hypothesis)
          | some ``Option.some =>
              defined := some (← subgoal.mvarId.withContext do
                let ty ← instantiateMVars (← inferType hypothesis)
                let value := (← whnfR (ty.getArg! 2)).appArg!
                let read := (ty.getArg! 4).beta #[value]
                -- The value takes the name the invariant binds the slot by.
                let named ← subgoal.mvarId.rename value.fvarId! (ty.getArg! 4).bindingName!
                named.replaceLocalDeclDefEq hypothesis.fvarId! read)
          | _ => throwError "a slot has a case besides its definedness"
        let some next := defined | throwError "a slot has no defined case"
        goal := next
        progress := true
      else
      let subgoals ← goal.cases fvarId
      match subgoals with
      | #[subgoal] =>
          goal := subgoal.mvarId
          progress := true
      | _ => break
    else
      -- An array equated through its list is substituted as the array of
      -- that list.
      let listEquation ← goal.withContext do
        (← getLCtx).findDeclM? fun decl => do
          if decl.isImplementationDetail then return none
          let ty ← instantiateMVars decl.type
          unless ty.isAppOfArity ``Eq 3 do return none
          let lhs := ty.getArg! 1
          let rhs := ty.getArg! 2
          let asList (side other : Lean.Expr) (symm : Bool) : Option (Lean.LocalDecl × Bool) :=
            if side.isAppOfArity ``Array.toList 2 then
              match side.getArg! 1 with
              | .fvar xs => if other.containsFVar xs then none else some (decl, symm)
              | _ => none
            else none
          return asList lhs rhs false <|> asList rhs lhs true
      match listEquation with
      | some (decl, symm) =>
          let (equation, asserted) ← goal.withContext do
            let h ← if symm then mkEqSymm decl.toExpr else pure decl.toExpr
            let proof ← mkAppM ``LeanerIR.Proofs.Denote.array_eq_of_toList_eq #[h]
            let asserted ← goal.assert `arrayEq (← inferType proof) proof
            asserted.intro1P
          goal ← asserted.withContext (Lean.Meta.subst asserted equation)
          progress := true
      | none => pure ()
    -- Once nothing else destructures, a twin-typed local splits: a struct
    -- twin into its fields, an enum twin into its variants, so that its
    -- native view and erasure reduce to constructor forms. The tag on the
    -- twin's declaration licenses the split; an enum's variants become
    -- separate goals, each continued by the next round.
    if !progress then
      let twin ← goal.withContext do
        (← getLCtx).findDeclM? fun decl => do
          if decl.isImplementationDetail then return none
          let ty ← instantiateMVars decl.type
          let .const name _ := ty.getAppFn | return none
          return if Proofs.leanerTwinAttribute.hasTag (← getEnv) name then some decl.fvarId
            else none
      if let some fvarId := twin then
        let subgoals ← goal.cases fvarId
        match subgoals with
        | #[subgoal] =>
            goal := subgoal.mvarId
            progress := true
        | _ =>
            replaceMainGoal (subgoals.map (·.mvarId)).toList
            return
  replaceMainGoal [goal]

/-- The proof arguments of an expression that mention a local, each with
the proposition its position expects, when the local occurs nowhere else.
A proof whose proposition itself mentions the local, through the proofs
of an earlier argument, is left for a later pass, once those are
detached. -/
private partial def proofsMentioning (x : FVarId) (e : Lean.Expr) :
    MetaM (Option (Array (Lean.Expr × Lean.Expr))) := do
  let rec visit (e : Lean.Expr) (found : Array (Lean.Expr × Lean.Expr)) :
      MetaM (Option (Array (Lean.Expr × Lean.Expr))) := do
    if !e.containsFVar x then return some found
    match e with
    | .app function argument => do
        let some found ← visit function found | return none
        if argument.containsFVar x && !argument.hasLooseBVars && (← Meta.isProof argument) then
          let .forallE _ proposition _ _ ← whnf (← inferType function) | return none
          let proposition ← instantiateMVars proposition
          if proposition.containsFVar x || proposition.hasLooseBVars then return some found
          return some (found.push (argument, proposition))
        visit argument found
    | .mdata _ body => visit body found
    | _ => return none
  visit e #[]

/-- An equation between a local and a value that mentions the local only
inside proofs, restated so that it does not: each such proof becomes a
hypothesis of its proposition, innermost first.  By proof irrelevance the
restated equation is the same up to definitional equality, and the local
can be substituted. -/
private partial def detachProofs (goal : MVarId) (equation : FVarId) (x : FVarId) :
    MetaM (Option MVarId) := goal.withContext do
  let type ← instantiateMVars (← equation.getType)
  unless type.isAppOfArity ``Eq 3 do return none
  let (value, valueOnLeft) :=
    if type.getArg! 2 == .fvar x then (type.getArg! 1, true) else (type.getArg! 2, false)
  let some proofs ← proofsMentioning x value | return none
  if proofs.isEmpty then return none
  let hypotheses := proofs.map fun (proof, proposition) =>
    ({ userName := `detached, type := proposition, value := proof } : Hypothesis)
  let (detached, goal) ← goal.assertHypotheses hypotheses
  goal.withContext do
    let value := (proofs.zip detached).foldl (fun value ((proof, _), hypothesis) =>
      value.replace fun sub => if sub == proof then some (.fvar hypothesis) else none) value
    let restated := if valueOnLeft then mkApp3 type.getAppFn (type.getArg! 0) value (.fvar x)
      else mkApp3 type.getAppFn (type.getArg! 0) (.fvar x) value
    let goal ← goal.replaceLocalDeclDefEq equation restated
    -- The proofs the detached ones exposed, until the local is gone.
    if value.containsFVar x then detachProofs goal equation x else return some goal

/-- Whether a runtime value is a constructor that fixes its variant: a
nominal value's variant is a literal. -/
private def fixesVariant (value : Lean.Expr) : Bool :=
  match value.getAppFn.constName? with
  | some ``LeanerIR.RuntimeValue.nominal =>
      value.getAppNumArgs == 3 && match (value.getArg! 1).consumeMData with
        | .app (.app (.const ``Option.some _) _) (.lit (.strVal _)) => true
        | .app (.const ``Option.none _) _ => true
        | _ => false
  | some name => name.getPrefix == ``LeanerIR.RuntimeValue
  | none => false

/-- A hypothesis fixing the encoding of a local, `encode τ x = e` with `x`
not in `e` and `e` a constructor fixing its variant, that `rewritten` does
not list. -/
private def encodingEquation? (goal : MVarId) (rewritten : Array FVarId) :
    MetaM (Option FVarId) := goal.withContext do
  (← getLCtx).findDeclM? fun decl => do
    if decl.isImplementationDetail || rewritten.contains decl.fvarId then return none
    let ty ← instantiateMVars decl.type
    unless ty.isAppOfArity ``Eq 3 do return none
    let encodes (side other : Lean.Expr) : Bool :=
      side.isAppOfArity ``NTy.encode 3 && fixesVariant other && match side.appArg! with
        | .fvar x => !other.containsFVar x
        | _ => false
    if encodes (ty.getArg! 1) (ty.getArg! 2) || encodes (ty.getArg! 2) (ty.getArg! 1) then
      return some decl.fvarId
    return none

/-- Rewrite the target and the other hypotheses by an equation fixing a
local's encoding, each where the rewrite is well typed. -/
private def rewriteByEncoding (goal : MVarId) (equation : FVarId) : MetaM MVarId :=
  goal.withContext do
    let type ← instantiateMVars (← equation.getType)
    let symm := !(type.getArg! 1).isAppOfArity ``NTy.encode 3
    let mut goal := goal
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.fvarId == equation then continue
      let rewritten ← observing? do
        let result ← goal.rewrite decl.type (Lean.mkFVar equation) symm
        unless result.mvarIds.isEmpty do failure
        pure result
      if let some result := rewritten then
        goal := (← goal.replaceLocalDecl decl.fvarId result.eNew result.eqProof).mvarId
    let rewritten ← observing? do
      let result ← goal.rewrite (← goal.getType) (Lean.mkFVar equation) symm
      unless result.mvarIds.isEmpty do failure
      pure result
    if let some result := rewritten then
      goal ← goal.replaceTargetEq result.eNew result.eqProof
    return goal

/-- Close a goal by a case hypothesis `∀ xs, a = b → … → False` that an
instance refutes: the fall-through case of a match whose discriminant is
known to be a pattern's constructor, as a split states it or as the
normalizer leaves it, its equation taken apart. -/
private def refuteFallthrough (goal : MVarId) : MetaM Bool := goal.withContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    unless type.isForall do continue
    let refuted ← observing? do
      let (arguments, _, body) ← forallMetaTelescopeReducing type
      unless body.isConstOf ``False do failure
      let mut equations := 0
      for argument in arguments do
        let argumentType ← instantiateMVars (← inferType argument)
        let_expr Eq _ left right := argumentType | continue
        unless ← isDefEq left right do failure
        argument.mvarId!.assign (← mkEqRefl left)
        equations := equations + 1
      if equations == 0 then failure
      let proof ← instantiateMVars (mkAppN decl.toExpr arguments)
      if proof.hasExprMVar then failure
      goal.assign (← mkFalseElim (← goal.getType) proof)
    if refuted.isSome then return true
  return false

/-- Destructure a local along its native carrier: a variant sum into its
alternatives, a row into its fields, until the parts are scalars or
parameters. -/
private partial def destructureCarrier (goal : MVarId) (value : FVarId) :
    MetaM (Array MVarId) := goal.withContext do
  let type ← whnfD (← instantiateMVars (← value.getType))
  unless type.isAppOf ``Sum || type.isAppOf ``Prod || type.isAppOf ``PUnit ||
      type.isAppOf ``Empty do
    return #[goal]
  let cases ← goal.cases value
  cases.foldlM (init := #[]) fun found case => do
    let mut goals := #[case.mvarId]
    for field in case.fields do
      let .fvar part := field | continue
      goals ← goals.flatMapM fun goal => destructureCarrier goal part
    return found ++ goals

/-- Substitute every hypothesis equating a local variable to a term, by
syntactic shape alone: no hypothesis is unfolded to find one. -/
elab "leaner_denote_subst_vars" : tactic => do
  if (← getGoals).isEmpty then return
  let mut goal ← getMainGoal
  let mut progress := true
  let mut attempted : Array FVarId := #[]
  let mut encoded : Array FVarId := #[]
  while progress do
    progress := false
    let equation ← goal.withContext do
      (← getLCtx).findDeclM? fun decl => do
        if decl.isImplementationDetail then return none
        let ty ← instantiateMVars decl.type
        unless ty.isAppOfArity ``Eq 3 do return none
        let lhs := ty.getArg! 1
        let rhs := ty.getArg! 2
        let substitutable (x : Lean.Expr) (other : Lean.Expr) : Bool :=
          match x with
          | .fvar id => !other.containsFVar id
          | _ => false
        if substitutable lhs rhs || substitutable rhs lhs then return some (decl.fvarId, none)
        -- The local occurs on the other side, perhaps only inside proofs.
        if attempted.contains decl.fvarId then return none
        match rhs, lhs with
        | .fvar x, _ => return some (decl.fvarId, some x)
        | _, .fvar x => return some (decl.fvarId, some x)
        | _, _ => return none
    match equation with
    | some (fvarId, none) =>
        goal ← goal.withContext (Lean.Meta.subst goal fvarId)
        progress := true
    | some (fvarId, some x) =>
        attempted := attempted.push fvarId
        if let some detached ← detachProofs goal fvarId x then
          goal := detached
        progress := true
    | none =>
        -- A local whose encoding is fixed, such as a generic callee's
        -- result, is known wherever that encoding occurs.
        if let some fvarId ← encodingEquation? goal encoded then
          encoded := encoded.push fvarId
          goal ← rewriteByEncoding goal fvarId
          progress := true
  -- A match's fall-through case whose discriminant the substitutions have
  -- fixed to a constructor is refuted.
  if ← refuteFallthrough goal then replaceMainGoal []; return
  -- A local's own structure follows from its encoding once it is
  -- destructured; the alternatives an equation excludes compute to
  -- contradictions.
  let mut goals := #[goal]
  for equation in encoded do
    goals ← goals.flatMapM fun goal => goal.withContext do
      let some decl := (← getLCtx).find? equation | return #[goal]
      let type ← instantiateMVars decl.type
      let side := if (type.getArg! 1).isAppOfArity ``NTy.encode 3 then type.getArg! 1
        else type.getArg! 2
      let .fvar encodedLocal := side.appArg! | return #[goal]
      destructureCarrier goal encodedLocal
  replaceMainGoal goals.toList

/-- Split a leaf goal into its cases: a conjunction into its parts, and a
binder, implication, or negation into a hypothesis, until the goal is
atomic.  Each case then carries the equations of its branch, which a
rewriting pass turns into closed arithmetic. -/
partial def splitGoal (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let target ← whnfR (← instantiateMVars (← goal.getType))
  if target.isAppOfArity ``And 2 then
    let subgoals ← goal.apply (mkConst ``And.intro)
    return (← subgoals.mapM splitGoal).flatten
  if target.isAppOfArity ``Not 1 then
    let (_, next) ← (← goal.change (mkForall `h .default (target.getArg! 0) (mkConst ``False))).intro1
    return ← splitGoal next
  if target.isForall then
    -- A quantified variable keeps its name, for an authored proof.
    let (_, next) ← goal.intro1P
    return ← splitGoal next
  return [goal]

elab "leaner_denote_split_goal" : tactic => do
  if (← getGoals).isEmpty then return
  let goals ← (← getMainGoal).withContext (splitGoal (← getMainGoal))
  replaceMainGoal goals

/-- What a saturation round can change of a goal: its target and its
hypotheses. The hypotheses are compared as a collection: the rewriting
pass restates the hypotheses it changes after the others, so a round that
proves nothing new may still reorder them. -/
private def goalContent (goal : MVarId) : MetaM (Lean.Expr × Array Lean.Expr) := goal.withContext do
  let mut hypotheses := #[]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      hypotheses := hypotheses.push (← instantiateMVars decl.type)
  return (← instantiateMVars (← goal.getType), hypotheses.qsort (·.lt ·))

/-- The bounds asserted on a goal's ancestors, by the goal's content: the
rewriting pass restates each bound, or drops it as known, so asserting it
again would only be undone by the next pass. Emptied for every target. -/
initialize assertedBounds :
    IO.Ref (Std.HashMap (Lean.Expr × Array Lean.Expr) (Array Lean.Expr)) ← IO.mkRef {}

/-- Take each goal through `step` on its own, after asserting the bounds it
needs (`assert`), and record the bounds asserted on the goals `step` leaves
and their ancestors: those are not asserted on them again. -/
private def withBounds (assert : Bool) (step : Syntax) : TacticM Unit := do
  let mut remaining := []
  for goal in ← getGoals do
    let known := (← assertedBounds.get)[← goalContent goal]?.getD #[]
    setGoals [goal]
    let asserted := known ++ (← if assert then assertBounds known else pure #[])
    evalTactic step
    let results ← getGoals
    unless asserted.isEmpty do
      for result in results do
        let content ← goalContent result
        assertedBounds.modify (·.insert content asserted)
    remaining := remaining ++ results
  setGoals remaining

/-- Assert the bounds each goal needs, then run a tactic on it. -/
elab "leaner_denote_bounded " step:tactic : tactic => withBounds true step

/-- Run a tactic on each goal; the goals it leaves have their ancestor's
bounds. -/
elab "leaner_denote_inheriting " step:tactic : tactic => withBounds false step

/-- One saturation round: bound the integers, destructure the hypotheses,
substitute witnesses, and rewrite with every hypothesis. -/
macro "leaner_denote_saturate_round" : tactic => `(tactic|
  leaner_denote_bounded (
    all_goals leaner_denote_split_hypotheses
    all_goals leaner_denote_subst_vars
    all_goals (try leaner_simp_all [lir_denote_norm])))

/-- Saturate a leaf's context: rounds of rewriting while new hypotheses
appear, after the round the leaf has already run, at most four. A round
that leaves the goals as they were has reached the fixed point, and a
further round would repeat it. -/
elab "leaner_denote_saturate" : tactic => do
  for _ in [0:4] do
    let before ← (← getGoals).mapM fun goal => goalContent goal
    evalTactic (← `(tactic| leaner_denote_saturate_round))
    if (← (← getGoals).mapM fun goal => goalContent goal) == before then return

/-- `decide` on a closed goal only: on an open one the kernel evaluates
the instance for as long as the goal is large, then fails anyway. -/
elab "leaner_denote_decide" : tactic => do
  let target ← instantiateMVars (← (← getMainGoal).getType)
  if target.hasFVar then throwError "the goal is not closed"
  evalTactic (← `(tactic| decide))

/-- Identify the elements two lookups of one position found: from
`e = some a` and `e = some b`, `a = b`, which injection then splits. -/
elab "leaner_denote_merge_lookups" : tactic => do
  let goal ← getMainGoal
  let found ← goal.withContext do
    let decls := (← getLCtx).foldl (init := #[]) fun found decl =>
      if decl.isImplementationDetail then found else found.push decl
    let mut pairs : Array (Lean.Expr × Lean.Expr) := #[]
    for i in [:decls.size] do
      let ti ← instantiateMVars decls[i]!.type
      unless ti.isAppOfArity ``Eq 3 && (ti.getArg! 2).isAppOfArity ``Option.some 2 do continue
      for j in [i + 1:decls.size] do
        let tj ← instantiateMVars decls[j]!.type
        unless tj.isAppOfArity ``Eq 3 && (tj.getArg! 2).isAppOfArity ``Option.some 2 do continue
        if (ti.getArg! 2) != (tj.getArg! 2) then
          if ← withReducible (isDefEq (ti.getArg! 1) (tj.getArg! 1)) then
            pairs := pairs.push (decls[i]!.toExpr, decls[j]!.toExpr)
    return pairs
  let mut goal := goal
  for (left, right) in found do
    let proof ← goal.withContext do
      mkAppM ``Option.some.inj #[← mkEqTrans (← mkEqSymm left) right]
    let (_, next) ← (← goal.assert `sameElement (← goal.withContext (inferType proof)) proof).intro1P
    goal := next
  replaceMainGoal [goal]

/-- The normalization every leaf receives before a decision: the leaf an
authored proof takes over is left in this form. -/
macro "leaner_denote_prepare" : tactic => `(tactic| (
  leaner_denote_clear_computations
  leaner_denote_split_hypotheses
  leaner_denote_subst_vars
  leaner_denote_reduce_projections
  leaner_denote_bounds
  -- A conditional whose condition omega decides, such as a vector's bound
  -- after an update, takes its branch; a condition a hypothesis states is
  -- proved by that hypothesis, so that the branch's proof term mentions
  -- nothing a substitution would then have to keep.
  try simp (disch := first | assumption | omega) only [LeanerIR.Proofs.Obligation_iff, Nat.reduceAdd,
    Int.reducePow, Int.reduceSub, Nat.reducePow, Nat.reduceSub, Int.tmod_eq_emod_of_nonneg,
    Int.tdiv_eq_ediv_of_nonneg, lir_denote_norm, dif_pos, dif_neg, if_pos, if_neg, Prod.fst,
    Prod.snd] at *
  all_goals leaner_denote_split_hypotheses
  all_goals leaner_denote_subst_vars
  all_goals leaner_denote_reduce_projections
  -- Lookups of one position, once substitution has exposed them.
  all_goals leaner_denote_merge_lookups
  all_goals leaner_denote_split_hypotheses
  all_goals leaner_denote_subst_vars
  all_goals (try simp only [Prod.fst, Prod.snd] at *)))

/-- Split the goal's first conditional or match. A match's fall-through
case that its computed discriminant refutes is closed at once. -/
elab "leaner_denote_split" : tactic => do
  -- A discriminant a hypothesis equates to a term is split as that term.
  let original ← getMainGoal
  evalTactic (← `(tactic| leaner_denote_subst_vars))
  -- A refuted or destructured goal is progress enough.
  if (← getGoals).length != 1 then return
  -- The context stays normalized for the deciders that rewrite with it.
  if (← getMainGoal) != original then
    evalTactic (← `(tactic| try simp only [lir_denote, lir_denote_norm, lir_denote_eval,
      Prod.fst, Prod.snd] at *))
  evalTactic (← `(tactic| split))
  let goals ← (← getGoals).filterM fun goal => do return !(← refuteFallthrough goal)
  setGoals goals

/-- The general leaf: one pipeline, each stage over the previous stage's
goals, so that a rewriting pass is never repeated for a later alternative. -/
macro "leaner_denote_pipeline" : tactic => `(tactic| (
  leaner_denote_subst_vars
  leaner_denote_reduce_projections
  leaner_denote_bounded (try simp (disch := omega) only [LeanerIR.Proofs.Obligation_iff,
    Nat.reduceAdd, Int.reducePow, Int.reduceSub, Nat.reducePow, Nat.reduceSub,
    Int.tmod_eq_emod_of_nonneg, Int.tdiv_eq_ediv_of_nonneg, lir_denote_norm] at *)
  first
  | done
  | omega
  | (leaner_denote_saturate_round
     all_goals (first
       | done
       | (leaner_denote_bounds; omega)
       | (leaner_denote_saturate
          leaner_denote_inheriting
            (all_goals (try (leaner_denote_split <;> (try leaner_simp_all [lir_denote_norm]))))
          leaner_denote_inheriting
            (all_goals (try (leaner_denote_split <;> (try leaner_simp_all [lir_denote_norm]))))
          leaner_denote_inheriting (all_goals leaner_denote_split_goal)
          leaner_denote_saturate_round
          all_goals (first | (leaner_denote_bounds; omega) | leaner_denote_bv))))))

/-- An existential goal whose body some hypothesis states at a witness. -/
elab "leaner_denote_witness" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOfArity ``Exists 2 do throwError "not an existential"
    let body := target.getArg! 1
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let witness ← mkFreshExprMVar (target.getArg! 0)
      let saved ← saveState
      if ← isDefEq (body.beta #[witness]) (← instantiateMVars decl.type) then
        let proof ← mkAppOptM ``Exists.intro #[target.getArg! 0, body, ← instantiateMVars witness,
          decl.toExpr]
        goal.assign proof
        replaceMainGoal []
        return
      restoreState saved
    throwError "no hypothesis states the existential at a witness"

/-- The cheap deciders of a leaf: those that never rewrite the context. -/
macro "leaner_denote_decide_cheap" : tactic => `(tactic|
  first
  | leaner_denote_witness
  | (simp only [LeanerIR.Proofs.Obligation_iff, Nat.reduceAdd, Int.reducePow, Int.reduceSub,
      Nat.reducePow, Nat.reduceSub]
     first
     | done
     | (leaner_denote_bounds; omega)
     | leaner_denote_decide))

/-- A goal some hypothesis states, up to reducible unfolding. Plain
`assumption` compares at default transparency, which unfolds large
verification conditions at length before failing on the leaves nothing
closes. -/
elab "leaner_denote_assumption" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if ← withReducible (isDefEq target (← instantiateMVars decl.type)) then
        goal.assign decl.toExpr
        replaceMainGoal []
        return
    throwError "no hypothesis states the goal"

/-- `trivial` at reducible transparency and without `decide` and
`contradiction`: an open goal's decision and a search for contradicting
hypotheses belong to the deciders, which bound them. -/
syntax "leaner_denote_trivial" : tactic

macro_rules
  | `(tactic| leaner_denote_trivial) => `(tactic|
      first
      | leaner_denote_assumption
      | with_reducible rfl
      | exact True.intro
      | (apply And.intro <;> leaner_denote_trivial))

/-- A goal that is an instance of a quantified hypothesis: the hypothesis
applied at reducible transparency, its premises closed by omega or by a
hypothesis. -/
elab "leaner_denote_instance" : tactic => do
  let initial ← saveState
  let (_, goal) ← (← getMainGoal).intros
  let candidates ← goal.withContext do
    (← getLCtx).foldlM (init := #[]) fun found decl => do
      if decl.isImplementationDetail then return found
      let ty ← instantiateMVars decl.type
      return if ty.isForall then found.push decl.toExpr else found
  for candidate in candidates.reverse do
    let saved ← saveState
    try
      let premises ← withReducible (goal.apply candidate)
      setGoals premises
      evalTactic (← `(tactic| all_goals first | leaner_denote_assumption | omega))
      if (← getGoals).isEmpty then return
    catch _ => pure ()
    saved.restore
  initial.restore
  throwError "no quantified hypothesis has the goal as an instance"

/-- The goal in normal form rewritten by the hypotheses, but for the
equations that would rewrite a term into one containing it. -/
elab "leaner_denote_simp_by_context" : tactic => withMainContext do
  let stx ← `(tactic| simp only [LeanerIR.Proofs.Obligation_iff, Nat.reduceAdd, Int.reducePow,
    Int.reduceSub, Nat.reducePow, Nat.reduceSub, lir_denote_norm])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let mut hypotheses : SimpTheorems := {}
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    unless ← isProp type do continue
    if ← selfReferential type then continue
    hypotheses ← hypotheses.add (.fvar decl.fvarId) #[] decl.toExpr
  let ctx ← Simp.mkContext ctx.config (ctx.simpTheorems.push hypotheses)
    (withoutBranchConditions ctx.congrTheorems)
  match ← simpGoal (← getMainGoal) ctx simprocs (simplifyTarget := true) (fvarIdsToSimp := #[]) with
  | (none, _) => replaceMainGoal []
  | (some (_, goal), _) => replaceMainGoal [goal]

/-- The deciders of a leaf an authored proof may take over: the cheap ones,
and the goal alone in normal form rewritten by the hypotheses, which is
cheap where the context is large and decides a leaf whose facts are
already in the context. -/
macro "leaner_denote_decide_residual" : tactic => `(tactic|
  first
  | done
  | omega
  | leaner_denote_decide_cheap
  | leaner_denote_instance
  | (leaner_denote_simp_by_context
     first | done | (leaner_denote_bounds; omega))
  | leaner_denote_trivial)

/-- Decide one leaf cheaply, without rewriting its context. -/
macro "leaner_denote_leaf_cheap" : tactic => `(tactic|
  (leaner_denote_clear_computations
   first
   | leaner_denote_assumption
   | (leaner_denote_split_hypotheses
      leaner_denote_decide_residual)))

/-- Decide one leaf. -/
syntax "leaner_denote_leaf" : tactic

macro_rules
  | `(tactic| leaner_denote_leaf) => `(tactic|
      (leaner_denote_clear_computations
       first
       -- A goal a hypothesis states, before splitting takes it apart.
       | leaner_denote_assumption
       -- Atomic hypotheses first: each is rewritten, used, and dropped on
       -- its own.
       | (leaner_denote_split_hypotheses
          first
          | leaner_denote_decide_cheap
          | leaner_denote_pipeline
          | leaner_denote_trivial)))

/-- A structural update of an array literal at literal positions: the
positions move, the elements are not inspected. -/
private def reduceArrayLiteral (array : Lean.Expr) (positions : Array Lean.Expr)
    (update : List Lean.Expr → Array Nat → Option (List Lean.Expr)) : MetaM Simp.DStep := do
  let some (type, elements) := array.arrayLit? | return .continue
  let some positions := positions.mapM (·.nat?) | return .continue
  let some updated := update elements positions | return .continue
  return .visit (← mkArrayLit type updated)

/-- An in-bounds write into an array literal. -/
dsimproc [lir_denote_norm] reduceSetIfInBounds (Array.setIfInBounds _ _ _) := fun e => do
  let_expr Array.setIfInBounds _ array index value := e | return .continue
  reduceArrayLiteral array #[index] fun elements positions =>
    let index := positions[0]!
    some (if index < elements.length then elements.set index value else elements)

/-- An in-bounds exchange in an array literal. -/
dsimproc [lir_denote_norm] reduceSwapIfInBounds (Array.swapIfInBounds _ _ _) := fun e => do
  let_expr Array.swapIfInBounds _ array left right := e | return .continue
  reduceArrayLiteral array #[left, right] fun elements positions =>
    match elements[positions[0]!]?, elements[positions[1]!]? with
    | some first, some second =>
        some ((elements.set positions[0]! second).set positions[1]! first)
    | _, _ => some elements

/-- A slice of an array literal, its end clamped to the size. -/
dsimproc [lir_denote_norm] reduceExtract (Array.extract _ _ _) := fun e => do
  let_expr Array.extract _ array start stop := e | return .continue
  reduceArrayLiteral array #[start, stop] fun elements positions =>
    some ((elements.take positions[1]!).drop positions[0]!)

/-- A range reversal of an array literal. -/
dsimproc [lir_denote_norm] reduceReverseRange (LeanerIR.Proofs.Denote.reverseRange _ _ _ _) :=
  fun e => do
    let_expr LeanerIR.Proofs.Denote.reverseRange _ count left right array := e | return .continue
    reduceArrayLiteral array #[count, left, right] fun elements positions => Id.run do
      let mut elements := elements
      let mut left := positions[1]!
      let mut right := positions[2]!
      for _ in [0:positions[0]!] do
        elements := match elements[left]?, elements[right]? with
          | some first, some second => (elements.set left second).set right first
          | _, _ => elements
        left := left + 1
        right := right - 1
      return some elements

/-- Normalize only a bind's action. Its continuation is the rest of the
program: the closer reaches it through a folded continuation when the action
completes, so the normalizer never traverses it while a head is processed.
An action that completed hands the bind back to the rewrite rules that
reduce it. -/
private def bindActionStep (e : Lean.Expr) : Simp.SimpM Simp.Step := do
  let arguments := e.getAppArgs
  if arguments.size < 2 then return .continue
  let action := arguments[arguments.size - 2]!
  let next := arguments[arguments.size - 1]!
  let result ← Simp.simp action
  let head := mkAppN e.getAppFn (arguments.extract 0 (arguments.size - 2))
  let expr := mkApp2 head result.expr next
  let proof? ← result.proof?.mapM fun proof => do mkCongrFun (← mkCongrArg head proof) next
  let completed := match result.expr.getAppFn with
    | .const name _ => name == ``LeanerIR.Proofs.Spec.pure || name == ``LeanerIR.Proofs.Spec.abort
    | _ => false
  if completed then return .continue (some { expr, proof? })
  return .done { expr, proof? }

simproc ↓ [lir_denote_norm] bindAction (LeanerIR.Proofs.Spec.bind _ _) := bindActionStep

simproc ↓ [lir_denote_norm] flowBindAction (@LeanerIR.Proofs.Denote.Flow.bind ?skolems _ _ _ _ _ _) :=
  bindActionStep

/-- A type argument of a literal row: the substitution evaluates. -/
dsimproc ↓ [lir_denote_norm] reduceParameterSubst (LeanerIR.Proofs.Denote.NTy.subst _ _) :=
  fun e => do
    let reduced ← whnfR e
    if reduced == e then return .continue
    return .visit reduced

/-- An equation between values of a type parameter under the family a
call's type arguments induce is the equation of their encodings at the
argument's type, which the normalizer reduces to the runtime structure a
caller's clauses speak about. -/
simproc ↓ [lir_denote_norm] instantiatedEqAsEncoding (@Eq _ _ _) :=
  fun e => do
    let_expr Eq carrier left right := e | return .continue
    let some (outer, argument) ← (do
        match carrier.getAppFn.constName?, carrier.getAppArgs with
        | some ``LeanerIR.Proofs.Denote.Skolems.carrier, #[family, index] =>
            let_expr LeanerIR.Proofs.Denote.Skolems.instantiate θ outer := family | pure none
            pure (some (outer, mkApp2 (mkConst ``LeanerIR.Proofs.Denote.NTy.subst)
              (← mkAppM ``Subtype.val #[θ])
              (mkApp (mkConst ``LeanerIR.Proofs.Denote.NTy.param) index)))
        | some ``LeanerIR.Proofs.Denote.NTy.carrier, #[family, τ] =>
            let_expr LeanerIR.Proofs.Denote.Skolems.instantiate θ outer := family | pure none
            pure (some (outer, mkApp2 (mkConst ``LeanerIR.Proofs.Denote.NTy.subst)
              (← mkAppM ``Subtype.val #[θ]) τ))
        | _, _ => pure none : MetaM (Option (Lean.Expr × Lean.Expr)))
      | return .continue
    let encode (value : Lean.Expr) :=
      mkApp3 (mkConst ``LeanerIR.Proofs.Denote.NTy.encode) outer argument value
    let equation ← mkEq (encode left) (encode right)
    let injective := mkAppN (mkConst ``LeanerIR.Proofs.Denote.NTy.encode_inj) #[outer, argument, left, right]
    let proof ← mkAppM ``propext #[← mkAppM ``Iff.symm #[injective]]
    return .visit { expr := equation, proof? := some proof }

/-- Decoding a literal integer at a literal width is decided outright: the
certificate is a kernel decision, so no conditional is left for a split. -/
simproc ↓ [lir_denote_norm] decodeIntegerLiteral
    (LeanerIR.Proofs.Codec.decode? (LeanerIR.Proofs.Codec.specInt _ _) (LeanerIR.RuntimeValue.integer _)) :=
  fun e => do
    unless e.isAppOfArity ``LeanerIR.Proofs.Codec.decode? 4 do return .continue
    let codec := e.getArg! 2
    let raw := e.getArg! 3
    unless codec.isAppOfArity ``LeanerIR.Proofs.Codec.specInt 2 do return .continue
    unless raw.isAppOfArity ``LeanerIR.RuntimeValue.integer 1 do return .continue
    let width := codec.getArg! 0
    let signed := codec.getArg! 1
    let value := raw.getArg! 0
    unless width.isAppOfArity ``LeanerIR.IntWidth.bits 1 && (width.getArg! 0).nat?.isSome do
      return .continue
    unless signed.isConstOf ``Bool.true || signed.isConstOf ``Bool.false do return .continue
    let some _ := value.int? | return .continue
    let fits ← mkAppM ``LeanerIR.IntegerValueFits #[width, signed, value]
    -- The equation is closed and decidable: its certificate is a decision.
    let fitsProof? ← try some <$> mkDecideProof fits catch _ => pure none
    let result ← match fitsProof? with
      | some proof =>
          mkAppM ``Option.some #[mkAppN (mkConst ``LeanerIR.SpecInt.mk) #[width, signed, value, proof]]
      | none => mkAppOptM ``Option.none #[← mkAppM ``LeanerIR.SpecInt #[width, signed]]
    let equation ← mkEq e result
    let proof? ← try some <$> mkDecideProof equation catch _ => pure none
    let some proof := proof? | return .continue
    return .done { expr := result, proof? := some proof }

/- The normalization of a verification condition: the denotation's rules,
the weakest-precondition rules, and the propositional normal forms a leaf
is decided in. -/
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.NTy.encode_enum_inl
  LeanerIR.Proofs.Denote.NTy.encode_enum_inr LeanerIR.Proofs.Denote.HList.encode_cons
  LeanerIR.Proofs.Denote.HList.encode_nil LeanerIR.Proofs.Denote.NTy.encode_int
attribute [lir_denote_norm] LeanerIR.Proofs.wp_choose LeanerIR.Proofs.wp_assume
-- A literal instantiation keys a family as the runtime does.
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.instantiatedTypeId_cons
  LeanerIR.Proofs.Denote.instantiatedTypeId_nil LeanerIR.TypeId.mk.injEq
-- A type parameter's value is encoded by its family's codec, and defaults
-- under an induced family to its argument's value.
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.Skolems.default_instantiate
  LeanerIR.Proofs.Denote.NTy.inhabitant LeanerIR.Proofs.Denote.HList.inhabitant
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.NTy.codec_param
  LeanerIR.Proofs.Denote.NTy.encode_param LeanerIR.Proofs.Denote.Skolems.codec_instantiate
-- A function calling itself, or a member of a cycle of calls: the calls
-- routed to the cycle are `self`, every other call its callee's meaning.
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.routeMeaning_self
  LeanerIR.Proofs.Denote.routeMeaning_other LeanerIR.Proofs.Denote.routeGeneric_self
  LeanerIR.Proofs.Denote.routeGeneric_other LeanerIR.FunctionHandle.mk.injEq
  LeanerIR.NamespaceId.mk.injEq LeanerIR.FunctionId.mk.injEq
-- The structural order, as the ordering it computes.
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.compareResult_val LeanerIR.orderValue_lt_zero
  LeanerIR.orderValue_eq_zero LeanerIR.zero_lt_orderValue LeanerIR.orderValue_le_zero
  LeanerIR.zero_le_orderValue LeanerIR.orderValue_eq_neg_one LeanerIR.orderValue_eq_one
  LeanerIR.RuntimeValue.order_integer LeanerIR.RuntimeValue.order_bool Int.compare_eq_lt
  Int.compare_eq_gt Int.compare_eq_eq
-- A search over a whole vector, as membership.
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.getD_map_field
-- A vector construction whose representability is decided, and in-bounds
-- insertion and removal with their sizes.
attribute [lir_denote_norm] Option.dite_none_right_eq_some
  LeanerIR.Proofs.Denote.insertIdxIfInBounds_of_le LeanerIR.Proofs.Denote.eraseIdxIfInBounds_of_lt
  Array.size_insertIdx Array.size_eraseIdx
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.findIndex?_eq_none_iff
  LeanerIR.Proofs.Denote.findIndex?_isSome_iff
-- Bitwise conjunction commutes; simp orders its operands.
attribute [lir_denote_norm] LeanerIR.Proofs.IntegerArithmetic.bitwiseAnd_comm
-- A wrapping shift whose value cannot reach the modulus.
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.shiftLeft_emod_of_fits
  LeanerIR.Proofs.Denote.shiftLeft_tmod_of_fits
-- A resolved prophecy brings an operation's result into a leaf.
attribute [lir_denote_norm] LeanerIR.Proofs.Denote.wrapInt_unsigned
  LeanerIR.Proofs.Denote.wrapInt_signed LeanerIR.Proofs.Denote.ModularOp.run_val
  LeanerIR.Proofs.Denote.BitOp.run_val
attribute [lir_denote_norm] LeanerIR.Proofs.wp_pure
  LeanerIR.Proofs.wp_abort LeanerIR.Proofs.Spec.pure_bind LeanerIR.Proofs.Spec.abort_bind
  LeanerIR.Proofs.Denote.ResultShape.bodyType Bool.not_eq_true decide_eq_true_eq Bool.and_eq_true
  Bool.or_eq_true and_assoc exists_and_left exists_and_right exists_eq_left exists_eq_left'
  and_true true_and and_imp forall_and forall_eq forall_eq' Prod.mk.injEq exists_eq exists_eq'
  and_false false_and not_false_eq_true not_true_eq_false true_implies false_implies implies_true
  imp_self eq_self_iff_true ite_true ite_false Bool.false_eq_true Bool.true_eq_false
  Bool.not_eq_false decide_eq_false_iff_not Bool.and_eq_false_imp Bool.not_true Bool.not_false
  Bool.not_not Option.some.injEq Option.elim_some Option.elim_none LeanerIR.RuntimeValue.field
  LeanerIR.RuntimeValue.asInt LeanerIR.RuntimeValue.asBool LeanerIR.RuntimeValue.asString
  LeanerIR.RuntimeValue.variant? List.getElem?_toArray List.getElem?_cons_zero
  List.getElem?_cons_succ Option.getD_some LeanerIR.RuntimeValue.nominal.injEq
  LeanerIR.RuntimeValue.tuple.injEq LeanerIR.RuntimeValue.integer.injEq
  LeanerIR.RuntimeValue.bool.injEq LeanerIR.RuntimeValue.address.injEq List.cons.injEq List.nil_eq
  beq_self_eq_true LeanerIR.Proofs.Denote.Array.push_eq_push_iff
  LeanerIR.Proofs.Denote.specInt_encode LeanerIR.Proofs.Denote.bool_encode
  LeanerIR.Proofs.Denote.address_encode Nat.lt_succ_self Nat.lt_add_one Nat.le_refl
  Option.map_some Option.map_none LeanerIR.Proofs.Denote.specInt_decode_integer
  LeanerIR.Proofs.Denote.bool_decode_bool LeanerIR.Proofs.Denote.address_decode_address
  LeanerIR.Proofs.Denote.signer_decode_signer LeanerIR.Proofs.Denote.NTy.codec_int
  LeanerIR.Proofs.Denote.NTy.codec_bool LeanerIR.Proofs.Denote.NTy.codec_address
  LeanerIR.Proofs.Denote.NTy.codec_unit LeanerIR.Proofs.Denote.nat_eq_add_succ_iff
  LeanerIR.Proofs.Denote.nat_add_succ_eq_iff LeanerIR.Proofs.Denote.nat_eq_succ_iff
  LeanerIR.Proofs.Denote.nat_succ_eq_iff LeanerIR.Proofs.Denote.Family.key_eq
  LeanerIR.Proofs.Denote.NTy.codec_encode Option.bind_some Option.bind_none
  LeanerIR.FamilyRepresentation Option.getD_none LeanerIR.Proofs.Denote.HList.encode_inj
  LeanerIR.Proofs.Denote.NTy.decode?_struct_literal
  LeanerIR.Proofs.Denote.NTy.decode?_struct_nominal LeanerIR.Proofs.Denote.rowCodec_decode?_cons
  LeanerIR.Proofs.Denote.rowCodec_decode?_nil LeanerIR.Proofs.Denote.NTy.decode?_tuple_literal
  LeanerIR.Proofs.Denote.NTy.encode_inj LeanerIR.Proofs.Denote.NTy.decode?_encode
  LeanerIR.Proofs.Denote.storageKey_address LeanerIR.Proofs.Denote.storageKey_signer
  LeanerIR.SemanticOperations.globalKey LeanerIR.GlobalMap.lookup_insert_self
  LeanerIR.GlobalMap.lookup_erase_self LeanerIR.SemanticOperations.instantiatedTypeId_empty
  Nat.add_assoc LeanerIR.Proofs.Denote.nat_self_eq_add_iff
  LeanerIR.Proofs.Denote.nat_add_eq_self_iff LeanerIR.Proofs.Denote.NTy.codec_vector
  LeanerIR.Proofs.Denote.decodeElements?_nil LeanerIR.Proofs.Denote.decodeElements?_cons
  LeanerIR.Proofs.Denote.boundedVector_decode?_vector LeanerIR.Proofs.Codec.boundedVector_encode
  LeanerIR.SpecVector.ofArray?_eq LeanerIR.SpecVector.values_set LeanerIR.SpecVector.values_mk
  Array.size_set! Array.size_push Array.size_map LeanerIR.Proofs.Denote.toArray_inj_iff
  LeanerIR.RuntimeValue.vector.injEq List.map_toArray List.map_cons List.map_nil List.push_toArray
  List.size_toArray List.length_cons List.length_nil List.getElem?_eq_some_iff
  Array.getElem?_eq_none_iff Array.size_setIfInBounds Array.getElem?_map
  -- The transport of a value at the identity instantiation.
  Option.map_id' Array.map_id' Int.sub_add_cancel
  Option.map_map Function.comp_def Array.set!_eq_setIfInBounds List.setIfInBounds_toArray
  List.set_cons_zero List.set_cons_succ List.insertIdxIfInBounds_toArray List.insertIdx_zero
  List.insertIdx_succ_cons List.eraseIdxIfInBounds_toArray List.eraseIdx_cons_zero
  List.eraseIdx_cons_succ List.toList_toArray Option.bind_eq_some_iff Option.map_eq_some_iff
  Int.toNat_natCast LeanerIR.Proofs.Denote.vectorLength_val
  LeanerIR.Proofs.Denote.NTy.encode_vector LeanerIR.Proofs.Denote.NTy.eqb_vector_decide
  LeanerIR.Proofs.Denote.NTy.refFree LeanerIR.Proofs.Denote.NRow.refFree
  LeanerIR.Proofs.Denote.NRows.refFree Option.isSome_some Option.isSome_none Option.isSome_map
  LeanerIR.GlobalKey.mk.injEq LeanerIR.StorageKey.address.injEq Option.map_eq_none_iff
  LeanerIR.StructHandle.mk.injEq LeanerIR.Proofs.Contract.typed LeanerIR.Proofs.Denote.hlistCodec
  LeanerIR.Proofs.Denote.resultCodec LeanerIR.Proofs.Denote.NTy.encode_bool
  LeanerIR.Proofs.Denote.NTy.encode_unit LeanerIR.Proofs.Denote.NTy.encode_address
  LeanerIR.Proofs.Denote.NTy.encode_tuple LeanerIR.Proofs.Denote.NTy.encode_struct
  List.toArray_eq_iff exists_prop exists_const Int.not_lt Int.not_le ne_eq Decidable.not_not
  Bool.true_or Bool.false_or Bool.or_true Bool.or_false


attribute [lir_denote_eval] reduceCtorEq Nat.reduceAdd Nat.reduceSub Nat.reduceDiv Nat.reducePow
  Nat.reduceLT Nat.reduceEqDiff Int.reduceAdd Int.reduceSub Int.reducePow Int.reduceLT Int.reduceLE
  Int.reduceNatCast' Int.reduceToNat String.reduceBEq String.reduceEq String.reduceBNe
  String.reduceNe dite_true dite_false

macro "leaner_denote_normalize" location:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [lir_denote, lir_denote_norm, lir_denote_eval, Prod.fst, Prod.snd]
    $[$location]?)

/-- The loop a goal's weakest precondition is over, if any: its site, and
the arguments of `wp_loopAt` besides the invariant. -/
private def loopGoal? (goal : MVarId) : MetaM (Option (Nat × Array Lean.Expr)) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOfArity ``LeanerIR.Proofs.wp 7 do return none
    let action := target.getArg! 3
    unless action.isAppOfArity ``LeanerIR.Proofs.Denote.loopAt 6 do return none
    let some site ← (evalNat (action.getArg! 3)).run | return none
    return some (site, action.getAppArgs ++ #[target.getArg! 4, target.getArg! 5, target.getArg! 6])

/-- One structural split of a goal, on its syntax alone: a binder, a
conjunction, or a conditional.  Nothing is unfolded to find one.  Only a
conditional's branches can hold new redexes: a binder or conjunct of a
normalized goal is normalized already. -/
private def splitOnce (goal : MVarId) : TacticM (Option (List MVarId × Bool)) := do
  let target ← goal.withContext (instantiateMVars (← goal.getType))
  if target.isForall then
    -- A quantified variable keeps its name, for an authored proof.
    let (_, next) ← goal.intro1P
    return some ([next], false)
  if target.isAppOfArity ``And 2 then
    let subgoals ← goal.apply (mkConst ``And.intro)
    return some (subgoals, false)
  let saved ← saveState
  try
    setGoals [goal]
    evalTactic (← `(tactic| leaner_denote_split))
    return some (← getGoals, true)
  catch _ =>
    saved.restore
    return none

/-- The goal applied to the loop hypothesis it is an instance of, if any:
the premises that remain. -/
private def recursiveHypothesis? (goal : MVarId) : TacticM (Option (List MVarId)) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOfArity ``LeanerIR.Proofs.wp 7 && (target.getArg! 3).getAppFn.isFVar do
      return none
    (← getLCtx).findDeclM? fun decl => do
      if decl.isImplementationDetail then return none
      let ty ← instantiateMVars decl.type
      unless ty.isForall && ty.bindingBody!.isForall do return none
      let saved ← saveState
      try
        let subgoals ← goal.apply decl.toExpr
        if subgoals.isEmpty then
          saved.restore
          return none
        return some subgoals
      catch _ =>
        saved.restore
        return none

/-- The callee a goal's weakest precondition is over, if any, with the
action: the handle of a `propheticMeaning` application, or a callee given
as a local function, as a function calling itself is. -/
private def callGoal? (goal : MVarId) (callees : Array (Lean.Expr × String × Lean.Expr)) :
    MetaM (Option (Lean.Expr × Lean.Expr)) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOfArity ``LeanerIR.Proofs.wp 7 do return none
    let action := target.getArg! 3
    if action.isAppOfArity ``LeanerIR.Proofs.Denote.propheticMeaning 7 then
      return some (action.getArg! 3, action)
    let head := action.getAppFn
    if head.isFVar && callees.any (·.1 == head) then return some (head, action)
    return none

/-- The contract constants a callee theorem speaks about, to unfold at a
call site: the typed contract and the raw contract it wraps. -/
private def contractConstants (theoremType : Lean.Expr) : MetaM (Array Name) := do
  let type ← instantiateMVars theoremType
  let type := type.getForallBody
  unless type.isAppOfArity ``LeanerIR.Proofs.Satisfies 6 do return #[]
  let contract := type.getArg! 5
  let mut names := #[]
  if let .const name _ := contract.getAppFn then
    names := names.push name
    if let some info := (← getEnv).find? name then
      if let some value := info.value? then
        for dependency in value.getUsedConstants do
          if name.getPrefix.isPrefixOf dependency then names := names.push dependency
  return names

/-- The name of a continuation — a loop's, or a bind's — bound as a local
definition while the action before it is traversed. Substitutions
re-introduce locals, so the closer recognizes it by name rather than by
identity. -/
def continuationName : Name := `leanerContinuation

/-- Whether an action can branch, so that its continuation would be reached
on several paths. -/
private def mayBranch (action : Lean.Expr) : MetaM Bool := do
  let env ← getEnv
  return (action.find? fun sub => match sub.getAppFn with
    | .const name _ =>
        name == ``ite || name == ``dite || name == ``LeanerIR.Proofs.Denote.loopAt ||
          Lean.Meta.isMatcherCore env name
    | _ => false).isSome

/-- A bind at the head of a goal, taken by its rule: the goal with the
action at the head, and whether the action can branch. -/
private def bindRule? (goal : MVarId) : MetaM (Option (MVarId × Bool)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``LeanerIR.Proofs.wp 7 do return none
  let action := (target.getArg! 3).consumeMData.headBeta
  let conditions := #[target.getArg! 4, target.getArg! 5, target.getArg! 6]
  let rule ← if action.isAppOfArity ``LeanerIR.Proofs.Spec.bind 6 then
      mkAppM ``LeanerIR.Proofs.wp_bind (#[action.getArg! 4, action.getArg! 5] ++ conditions)
    else if action.isAppOfArity ``LeanerIR.Proofs.Denote.Flow.bind 7 then
      -- The flow's own skolem family and types instantiate the rule.
      pure (mkAppN (mkConst ``LeanerIR.Proofs.Denote.wp_flowBind) (action.getAppArgs ++ conditions))
    else return none
  let [unfolded] ← goal.apply (← mkAppM ``Iff.mpr #[rule])
    | throwError "the bind rule did not leave one goal"
  return some (unfolded, ← mayBranch (action.getArg! (action.getAppNumArgs - 2)))

/-- Bind a goal's continuation as a local definition, which the normalizer
leaves folded until the action completes: a branching action reaches it on
several paths, and no branch renormalizes it. -/
private def foldContinuation (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``LeanerIR.Proofs.wp 7 do return goal
  let ensures := target.getArg! 4
  if ensures.isFVar then return goal
  let defined ← goal.define continuationName (← inferType ensures) ensures
  let (continuation, folded) ← defined.intro1P
  folded.withContext do
    let target ← instantiateMVars (← folded.getType)
    folded.replaceTargetDefEq
      (mkAppN target.getAppFn (target.getAppArgs.set! 4 (mkFVar continuation)))

/-- Strip the `Obligation` markers heading a goal, returning the goal and
the clause ranges they carried, kept aside for reporting. A contract clause
is decided whole under its marker; a loop invariant is established as the
closer takes it apart, its quantifiers introduced by name for an authored
proof and its existentials left to a witness, so an invariant goal's
markers are set aside rather than sealing its clauses. -/
private partial def stripObligations (goal : MVarId) (clauses : Array ObligationRange) :
    MetaM (MVarId × Array ObligationRange) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``LeanerIR.Proofs.Obligation 4 do return (goal, clauses)
  let clauses := match obligationRange? target with
    | some range => clauses.push range
    | none => clauses
  stripObligations (← goal.replaceTargetDefEq (target.getArg! 3)) clauses

/-- Close every goal: a loop by its invariant, a recursive-call leaf by the
loop hypothesis, a call by the callee's theorem, a structural node by
splitting, and a leaf by decision. -/
partial def closeGoals (invariants : Array (Nat × Lean.Expr × Lean.Expr))
    (callees : Array (Lean.Expr × String × Lean.Expr)) (equations : Array Lean.Expr := #[])
    (residual : Bool := false) :
    TacticM Unit := do
  assertedBounds.set {}
  -- In residual mode an undecided leaf is left for an authored proof.
  let mut residuals : Array MVarId := #[]
  -- The target's closed equations, such as its generic calls' frame
  -- instantiations, apply wherever a body brings such a term into a goal.
  let rewriteEquations (goals : List MVarId) : TacticM (List MVarId) := do
    if equations.isEmpty then return goals
    let mut rewritten := []
    for goal in goals do
      setGoals [goal]
      let lemmas ← goal.withContext <| equations.mapM fun equation => do
        `(Lean.Parser.Tactic.simpLemma| $(← Lean.Elab.Term.exprToSyntax equation):term)
      evalTactic (← `(tactic| try simp only [$lemmas,*]))
      rewritten := rewritten ++ (← getGoals)
    return rewritten
  setGoals (← rewriteEquations (← getGoals))
  -- The structural matchers read a target's head: drop the metadata an
  -- introduction may leave around it.
  setGoals (← (← getGoals).mapM fun goal => do
    let target ← instantiateMVars (← goal.getType)
    if target.isMData then goal.replaceTargetDefEq target.consumeMData else pure goal)
  -- The function's arguments and state at its start, what a loop
  -- invariant's `old` reads, from the goal's own context.
  -- A function's latest start on the path: an inlined callee's calls are
  -- sequential, and a loop runs inside the call that reached it.
  let start? (goal : MVarId) (function : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) :=
    goal.withContext do
      let mut found := none
      for declaration in ← getLCtx do
        let type ← instantiateMVars declaration.type
        if type.isAppOfArity ``FunctionStart 4 then
          if ← isDefEq (type.getArg! 1) function then
            found := some (type.getArg! 2, type.getArg! 3)
      return found
  let debug := leaner.denoteDebug.get (← getOptions)
  let startHeartbeats ← IO.getNumHeartbeats
  let mut leaves := 0
  let mut stageCost : Array (String × Nat) := #[]
  let mut reported : Array (ObligationRange × String) := #[]
  let mut pending : Array (MVarId × Option Provenance × Array ObligationRange) :=
    (← getGoals).toArray.map fun g => (g, none, #[])
  while let some (goal, provenance, clauses) := pending.back? do
    pending := pending.pop
    let (goal, clauses) ← match provenance with
      | some .loopEntry | some .loopIteration => stripObligations goal clauses
      | _ => pure (goal, clauses)
    if ← goal.isAssigned then continue
    setGoals [goal]
    let stageStart ← IO.getNumHeartbeats
    -- An exit of a loop reaches its continuation, which is unfolded here, at
    -- the one place the rest of the function is needed.
    let exit? ← goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      let .fvar id := target.getAppFn | pure none
      let declaration ← id.getDecl
      if declaration.isLet && declaration.userName == continuationName then
        pure (some (← zetaDeltaFVars target #[id]).headBeta)
      else pure none
    if let some unfolded := exit? then
      setGoals [← goal.replaceTargetDefEq unfolded]
      evalTactic (← `(tactic| try leaner_denote_normalize))
      if debug then
        let head := match unfolded.getAppFn with
          | .const name _ => toString name
          | _ => "?"
        let action := if unfolded.isAppOfArity ``LeanerIR.Proofs.wp 7 then
            match (unfolded.getArg! 3).consumeMData.headBeta.getAppFn with
            | .const name _ => s!" of {name}"
            | _ => " of ?"
          else ""
        logInfo m!"exit into {head}{action}: {((← IO.getNumHeartbeats) - stageStart) / 1000}k"
      pending := pending ++ (← getGoals).toArray.map fun g => (g, provenance, clauses)
      stageCost := stageCost.push ("exit", (← IO.getNumHeartbeats) - stageStart)
      continue
    if let some (unfolded, branches) ← bindRule? goal then
      -- A straight-line action keeps its continuation in place: it reaches
      -- it on one path.
      setGoals [← if branches then foldContinuation unfolded else pure unfolded]
      evalTactic (← `(tactic| try leaner_denote_normalize))
      pending := pending ++ (← getGoals).toArray.map fun g => (g, provenance, clauses)
      stageCost := stageCost.push ("bind", (← IO.getNumHeartbeats) - stageStart)
      continue
    if let some (site, arguments) ← loopGoal? goal then
      let some (_, function, invariant) := invariants.find? (·.1 == site)
        | throwError m!"no invariant for the loop at site {site}"
      -- Without a recorded start, the invariant does not read `old`, and
      -- its start arguments vanish on reduction.
      let (start, startState) ← match ← start? goal function with
        | some start => pure start
        | none => goal.withContext do
            let type ← inferType invariant
            let .forallE _ argumentsType rest _ := type
              | throwError m!"the invariant at site {site} takes no function start"
            let .forallE _ stateType _ _ := rest
              | throwError m!"the invariant at site {site} takes no function start"
            pure (← mkFreshExprMVar argumentsType, ← mkFreshExprMVar stateType)
      let invariant ← goal.withContext
        (whnfR (mkAppN invariant #[start, startState, arguments[5]!, arguments[8]!]))
      if (← instantiateMVars invariant).hasExprMVar then
        throwError m!"the invariant at site {site} reads `old` without a recorded function start"
      -- The loop's continuation is bound once, as a local definition the
      -- normalizer does not unfold: the loop hypothesis and every back edge
      -- carry it folded.
      let ensures := arguments[6]!
      let (continuation, goal) ← goal.withContext do
        let target ← instantiateMVars (← goal.getType)
        let defined ← goal.define continuationName (← inferType ensures) ensures
        let (continuation, goal) ← defined.intro1P
        let abstracted := target.replace fun e =>
          if e == ensures then some (mkFVar continuation) else none
        pure (continuation, ← goal.replaceTargetDefEq abstracted)
      let arguments := arguments.set! 6 (mkFVar continuation)
      let rule := mkAppN (mkConst ``LeanerIR.Proofs.Denote.wp_loopAt)
        (arguments.extract 0 6 ++ #[invariant] ++ arguments.extract 6 9)
      let subgoals ← goal.withContext (goal.apply rule)
      match subgoals with
      | [entryHolds, step] =>
          let stepStart ← IO.getNumHeartbeats
          let mut marks : Array (String × Nat) := #[]
          setGoals [step]
          evalTactic (← `(tactic| intro recursive loopHypothesis env state loopInvariant))
          -- Assumed, the invariant's clauses are facts rather than obligations.
          evalTactic (← `(tactic| try simp only [LeanerIR.Proofs.Obligation_iff] at loopInvariant))
          evalTactic (← `(tactic| leaner_denote_normalize at loopHypothesis loopInvariant ⊢))
          marks := marks.push ("normalize 1", ← IO.getNumHeartbeats)
          -- The invariant's equations on the locals are substituted before
          -- the iteration is traversed, so the traversal sees their values.
          evalTactic (← `(tactic| all_goals leaner_denote_split_hypotheses))
          evalTactic (← `(tactic| all_goals leaner_denote_subst_vars))
          marks := marks.push ("split/subst 1", ← IO.getNumHeartbeats)
          -- The whole context once, so that every leaf of the iteration
          -- inherits normal hypotheses, with the equations the
          -- normalization exposes substituted.
          evalTactic (← `(tactic| all_goals (try leaner_denote_normalize at *)))
          marks := marks.push ("normalize 2", ← IO.getNumHeartbeats)
          evalTactic (← `(tactic| all_goals leaner_denote_split_hypotheses))
          evalTactic (← `(tactic| all_goals leaner_denote_subst_vars))
          marks := marks.push ("split/subst 2", ← IO.getNumHeartbeats)
          evalTactic (← `(tactic| all_goals (try leaner_denote_normalize at *)))
          marks := marks.push ("normalize 3", ← IO.getNumHeartbeats)
          if debug then
            let mut previous := stepStart
            let mut report := m!"loop step at site {site}:"
            for (label, mark) in marks do
              report := report ++ m!" {label} {(mark - previous) / 1000}k;"
              previous := mark
            logInfo m!"{report} {(← getGoals).length} goals"
          pending := pending ++ (← getGoals).toArray.map fun g => (g, provenance, clauses)
          setGoals [entryHolds]
          evalTactic (← `(tactic| try leaner_denote_normalize))
          pending := pending ++ (← getGoals).toArray.map fun g => (g, some .loopEntry, #[])
      | _ => throwError "the loop rule did not produce its two obligations"
      stageCost := stageCost.push ("loop", (← IO.getNumHeartbeats) - stageStart)
      continue
    if let some (handle, _) ← callGoal? goal callees then
      let some (_, calleeName, theoremProof) ← callees.findM? fun (candidate, _, _) =>
          goal.withContext (isDefEq candidate handle)
        | throwError m!"no verified callee for {handle}"
      -- A generic callee's theorem holds at every skolem family and type
      -- instantiation; the call's own are found by unification.
      let (theoremProof, theoremArguments) ← goal.withContext do
        let (arguments, _, _) ← forallMetaTelescope (← inferType theoremProof)
        pure (mkAppN theoremProof arguments, arguments)
      let proofSyntax ← goal.withContext (Lean.Elab.Term.exprToSyntax theoremProof)
      setGoals [goal]
      let proofType ← goal.withContext (instantiateMVars (← inferType theoremProof))
      if proofType.isAppOfArity ``Eq 3 then
        -- An unspecified callee: its compiled body replaces the call, by
        -- the agreement theorem, and the traversal continues into it.
        let compiled := (proofType.getArg! 2).appArg!
        let unfoldNames := match compiled with
          | .const name _ =>
              [name, name.getPrefix ++ `body, name.getPrefix ++ `mutables, name.getPrefix ++ `params,
                name.getPrefix ++ `locals, name.getPrefix ++ `shape, name.getPrefix ++ `row]
          | _ => []
        let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← unfoldNames.toArray.mapM
          fun name => `(Lean.Parser.Tactic.simpLemma| $(mkIdent (rootNamespace ++ name)):ident)
        let target ← goal.withContext (instantiateMVars (← goal.getType))
        let action := target.getArg! 3
        let quote (e : Lean.Expr) := goal.withContext (Lean.Elab.Term.exprToSyntax e)
        let familySyntax ← quote (action.getArg! 0)
        let unitSyntax ← quote (action.getArg! 1)
        let instantiationSyntax ← quote (action.getArg! 2)
        let handleSyntax ← quote (action.getArg! 3)
        let valuesSyntax ← quote (action.getArg! 6)
        let compiledSyntax ← quote compiled
        let ensuresSyntax ← quote (target.getArg! 4)
        let abortsSyntax ← quote (target.getArg! 5)
        let initialSyntax ← quote (target.getArg! 6)
        evalTactic (← `(tactic| refine
          (@LeanerIR.Proofs.Denote.wp_propheticMeaning_of_compiled $familySyntax $unitSyntax
            $instantiationSyntax $handleSyntax
            $compiledSyntax $proofSyntax $valuesSyntax $ensuresSyntax $abortsSyntax
            $initialSyntax).mpr ?_))
        -- The inlined callee starts here: its loops' invariants read `old`
        -- from its arguments at the call.
        if ← invariants.anyM fun (_, function, _) => goal.withContext (isDefEq function handle) then
          let inlined ← getMainGoal
          let started ← inlined.withContext do
            let proof ← mkAppM ``FunctionStart.intro
              #[action.getArg! 3, action.getArg! 6, target.getArg! 6]
            let (_, started) ← (← inlined.assert `leanerStart (← inferType proof) proof).intro1P
            pure started
          replaceMainGoal [started]
        evalTactic (← `(tactic| try simp only [$lemmas,*, LeanerIR.Proofs.Denote.Function.denote,
          LeanerIR.Proofs.Denote.NRow.nil_append, LeanerIR.Proofs.Denote.NRow.cons_append]))
        evalTactic (← `(tactic| try leaner_denote_normalize))
        pending := pending ++
          (← rewriteEquations (← getGoals)).toArray.map fun g => (g, provenance, clauses)
        continue
      evalTactic (← `(tactic| refine LeanerIR.Proofs.Denote.wp_call $proofSyntax ?_ ?_ ?_))
      let subgoals ← getGoals
      -- A callee's theorem assumes the natives it reaches, a generic one's
      -- at every family and instantiation; the caller assumes them too.
      for argument in theoremArguments do
        if let .mvar id ← instantiateMVars argument then
          let native ← forallTelescope (← instantiateMVars (← id.getType)) fun _ body =>
            pure (body.isAppOf ``LeanerIR.Proofs.Satisfies)
          if native then id.assumption
      let constants ← goal.withContext (contractConstants (← inferType theoremProof))
      let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← constants.mapM fun name => do
        let ident := mkIdent (rootNamespace ++ name)
        `(Lean.Parser.Tactic.simpLemma| $ident:ident)
      for (subgoal, index) in subgoals.toArray.zipIdx do
        setGoals [subgoal]
        evalTactic (← `(tactic| try simp only [$lemmas,*, lir_denote_norm]))
        evalTactic (← `(tactic| try leaner_denote_normalize))
        let origin := if index == 0 then some (Provenance.precondition calleeName)
          else if index == 1 then some (.continuation calleeName) else none
        pending := pending ++ (← getGoals).toArray.map fun g =>
          (g, origin, if index == 0 then #[] else clauses)
      continue
    if let some subgoals ← recursiveHypothesis? goal then
      -- The invariant at the iteration's end, normalized so that its
      -- conjunction splits into leaves.
      setGoals subgoals
      evalTactic (← `(tactic| all_goals (try leaner_denote_normalize)))
      pending := pending ++ (← getGoals).toArray.map fun g => (g, some .loopIteration, #[])
      stageCost := stageCost.push ("recursive", (← IO.getNumHeartbeats) - stageStart)
      continue
    let splitTarget ← if debug then goal.withContext do
        pure (some (← instantiateMVars (← goal.getType))) else pure none
    if let some (subgoals, conditional) ← splitOnce goal then
      let splitDone ← IO.getNumHeartbeats
      for subgoal in subgoals do
        setGoals [subgoal]
        let target ← subgoal.withContext (instantiateMVars (← subgoal.getType))
        if target.isAppOf ``LeanerIR.Proofs.wp then
          let consumed ← if provenance matches some (.continuation _) then do
              evalTactic (← `(tactic| try leaner_denote_consume))
              pure ((← getGoals) != [subgoal])
            else pure false
          if conditional || consumed then
            evalTactic (← `(tactic| try leaner_denote_normalize))
        pending := pending ++ (← getGoals).toArray.map fun g => (g, provenance, clauses)
      let finished ← IO.getNumHeartbeats
      if let some target := splitTarget then
        let head := match target.getAppFn with
          | .const name _ => toString name
          | _ => "?"
        let action := if target.isAppOfArity ``LeanerIR.Proofs.wp 7 then
            match (target.getArg! 3).getAppFn with
            | .const name _ => s!" of {name}"
            | _ => ""
          else ""
        logInfo m!"split {head}{action}: {subgoals.length} goals; split {(splitDone - stageStart) / 1000}k, normalize {(finished - splitDone) / 1000}k"
      stageCost := stageCost.push ("split", (← IO.getNumHeartbeats) - stageStart)
      continue
    setGoals [goal]
    if residual then
      -- An authored proof takes over what the cheap deciders leave, on the
      -- normalized leaf: the pipeline is not run for a leaf the proof
      -- will prove anyway, and a leaf the cheap deciders close costs no
      -- normalization at all.
      leaves := leaves + 1
      let before ← IO.getNumHeartbeats
      let beforeCheap ← saveState
      let closed ← try
          Lean.Elab.Tactic.withoutRecover (evalTactic (← `(tactic| leaner_denote_leaf_cheap)))
          let remaining ← getGoals
          if debug && !remaining.isEmpty then
            let types ← remaining.mapM fun g => g.withContext do instantiateMVars (← g.getType)
            logInfo m!"leaf {leaves}: the cheap deciders leave {remaining.length} goals: {types}"
          pure remaining.isEmpty
        catch failure =>
          if debug then logInfo m!"leaf {leaves} not decided cheaply: {failure.toMessageData}"
          pure false
      if closed then
        if debug then
          logInfo m!"leaf {leaves} closed cheaply: {((← IO.getNumHeartbeats) - before) / 1000}k heartbeats"
        continue
      -- The failed attempt's partial work on the goal is undone.
      beforeCheap.restore (restoreInfo := true)
      setGoals [goal]
      if debug then
        logInfo m!"leaf {leaves} before prepare:\n{goal}"
      let cheap ← IO.getNumHeartbeats
      let beforePrepare ← saveState
      try evalTactic (← `(tactic| leaner_denote_prepare))
      catch failure =>
        let report ← failure.toMessageData.toString
        beforePrepare.restore
        if debug then logInfo m!"leaf {leaves}: prepare failed: {report}"
      let prepared ← IO.getNumHeartbeats
      evalTactic (← `(tactic| all_goals (try leaner_denote_decide_residual)))
      evalTactic (← `(tactic| all_goals (try simp only [LeanerIR.Proofs.Obligation_iff])))
      if debug then
        logInfo m!"leaf {leaves}: cheap {(cheap - before) / 1000}k, prepare {(prepared - cheap) / 1000}k, \
          deciders {((← IO.getNumHeartbeats) - prepared) / 1000}k heartbeats; \
          {(← getGoals).length} residual"
        for g in ← getGoals do logInfo m!"leaf {leaves} after prepare:\n{g}"
      for remaining in ← getGoals do
        remaining.setTag (Name.mkSimple s!"leaf_{residuals.size + 1}")
        residuals := residuals.push remaining
      continue
    let leafStart ← IO.getNumHeartbeats
    let closed ← try
        -- Without recovery: a failing alternative raises at once, so the
        -- next alternative runs instead of an aborted goal list.
        Lean.Elab.Tactic.withoutRecover (evalTactic (← `(tactic| leaner_denote_leaf)))
        pure (← getGoals).isEmpty
      catch failure =>
        if debug then logInfo m!"leaf not decided: {failure.toMessageData}"
        pure false
    stageCost := stageCost.push (if closed then "leaf" else "undecided",
      (← IO.getNumHeartbeats) - leafStart)
    unless closed do
      setGoals [goal]
      reported ← reportObligation goal provenance clauses reported
      admitGoal goal
  if debug then
    let mut totals : Array (String × Nat × Nat) := #[]
    for (stage, cost) in stageCost do
      match totals.findIdx? (·.1 == stage) with
      | some index => totals := totals.modify index fun (name, count, sum) => (name, count + 1, sum + cost)
      | none => totals := totals.push (stage, 1, cost)
    let mut report := m!""
    for (stage, count, sum) in totals do
      report := report ++ m!" {stage} ×{count} {sum / 1000}k;"
    logInfo m!"closer: {((← IO.getNumHeartbeats) - startHeartbeats) / 1000}k heartbeats, \
      {leaves} leaves, {residuals.size} residual;{report}"
  setGoals residuals.toList

/-- Split the normalized goal into leaves and decide each; report the
clause of every leaf that is not decided.  Loops are handled by the
invariants given as `(site, function, invariant)` triples, calls by the callees' theorems,
and the `using` equations rewrite wherever a body brings their terms in. -/
syntax "leaner_denote_close" &" residual"? (" [" term,* "]")? (" with" " [" term,* "]")?
  (" using" " [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| leaner_denote_close $[residual%$residualToken]? $[[$loops:term,*]]?
      $[with [$calls:term,*]]? $[using [$equations:term,*]]?) => do
      if leaner.denoteDebug.get (← getOptions) then
        logInfo m!"normalized verification condition:\n{← getMainGoal}"
      let mut invariants : Array (Nat × Lean.Expr × Lean.Expr) := #[]
      for loop in (loops.map (·.getElems)).getD #[] do
        let triple ← Lean.Elab.Tactic.elabTerm loop none
        let triple ← whnf (← instantiateMVars triple)
        let rest ← whnf (triple.getArg! 3)
        unless triple.isAppOfArity ``Prod.mk 4 && rest.isAppOfArity ``Prod.mk 4 do
          throwError m!"a loop invariant must be a `(site, function, invariant)` triple, \
            not {triple}"
        let some site ← (evalNat (triple.getArg! 2)).run
          | throwError m!"a loop site must be a numeral, not {triple.getArg! 2}"
        invariants := invariants.push (site, rest.getArg! 2, rest.getArg! 3)
      let mut callees : Array (Lean.Expr × String × Lean.Expr) := #[]
      for call in (calls.map (·.getElems)).getD #[] do
        let pair ← Lean.Elab.Tactic.elabTerm call none
        let pair ← instantiateMVars pair
        let pair ← whnf pair
        unless pair.isAppOfArity ``PProd.mk 4 && (pair.getArg! 3).isAppOfArity ``PProd.mk 4 do
          throwError m!"a callee must be `PProd.mk handle (PProd.mk name theorem)`, not {pair}"
        let inner := pair.getArg! 3
        let some name := (match inner.getArg! 2 with
            | .lit (.strVal name) => some name
            | _ => none)
          | throwError m!"a callee name must be a string literal, not {inner.getArg! 2}"
        callees := callees.push (pair.getArg! 2, name, inner.getArg! 3)
      let equations ← ((equations.map (·.getElems)).getD #[]).mapM fun equation => do
        instantiateMVars (← Lean.Elab.Tactic.elabTerm equation none)
      closeGoals invariants callees equations residualToken.isSome

end LeanerIR.Proofs.Denote
