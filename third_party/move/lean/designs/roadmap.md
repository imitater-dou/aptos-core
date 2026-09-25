# Roadmap and test ledger

Status: 2026-09-27. This is the one place for project status: what is
still open across the designs, in priority order, and the ledger of the
acceptance fixtures that measures it ([Tests](#tests)). Each linked design
stays authoritative for its own scope and rationale; when a status
changes, update it here, not in the design. Done work is named in one line
per track so the open items read in context; the history lives in
[`historical/`](historical/).

The design documents inside `v0/` (`move/`, `move-model/`, `transpiler/`)
describe the deprecated stack. Nothing is scheduled from them; they are
mined for solutions, and all their verification fixtures are ported to the
ledger below.

## 1. Verification of validated LIR

Design: [`denotation.md`](denotation.md), with the reference model of
[`prophetic-references.md`](prophetic-references.md).

Done: one `denote` of validated LIR into `Spec`, compiled per target and
certified by the kernel (D0–D6: control, loops with invariants, references
as prophecies, storage and resource invariants, vectors, Move generics,
recursion and cycles of calls). Calls follow the Move Prover: callees are
inlined unless native, opaque, or on a cycle; contracts have `[abstract]`
and `[concrete]` views; `pragma bv` restates bit arithmetic over bit
vectors for `bv_decide`. Every Check fixture passes ([Tests](#tests)).

Open:

- **The agreement theorem.** `compileFunction_agrees` and
  `compileFunction_least_cycle` are axioms by decision; proving them by
  induction over `compileFunction` removes the last project-specific
  assumptions besides the natively checked `bv_decide` certificates.
- **Quantifier automation.** Specification quantifiers over types, ranges,
  and vectors (by index, as in the Move Prover) translate; the closer
  introduces universals but does not instantiate a quantified hypothesis
  at index terms, extend a range invariant by one iteration, or choose a
  witness for an existential. These are the goals of `bit_vector` and
  `acl` below.
- **Not carried by `denote`:** signed bitwise operations, `bytes` and
  fixed-length vectors, the generic residuals of D3 (aliasing instances), unspecified pure callees used as summaries, references
  inside an aggregate, and nested destructuring patterns.
- **Cost.** One `simp_all` pass per leaf over the shared context dominates
  storage targets (100M heartbeats for two global borrows with
  invariants); sharing it across the leaves of a target is the next cost
  item. A leaf no decider closes costs most: each saturation round over a
  large context costs 8–18M heartbeats. Every target runs under a budget
  (`leaner.verifyHeartbeats`, 180M heartbeats by default, the check
  driver's cap), so a target that does not verify fails within it.

## 2. Verification across modules

Design: [`relocatable-namespaces.md`](relocatable-namespaces.md).

Done: R1 (relocation: namespaces carry their own tables and validation
certificates, and a unit links them without re-validating) and R2
(a `leaner module` links the registered modules it uses; verification
inlines across modules; a clause is reported in the file that authored
it).

Open:

- **R3: proof reuse.** An opaque callee of another module is verified again
  in every importer. Reusing its theorem needs the semantics invariant
  under consistent renumbering, or semantics over namespace-local
  identities; either makes a package's verification cost linear.
- **R4: shipped namespaces.** The exchange format carries relocatable
  namespaces, so a frontend can ship a precompiled package.

## 3. The Move standard library as the verification corpus

Design: [`source-verification.md`](source-verification.md).

The package verifies module by module; the baseline
`leaner-e2e-tests/LeanerE2ETests/SourceVerify/MoveStdlib.exp` lists what
does not verify yet. `option`, `vector`, `fixed_point32`, `error`, and the
bit-flag functions of `features` (`set`, `contains`) verify. Open:

- `features`: `is_enabled` leaves the fact that a global resource
  decodes; `change_feature_flags_internal` and
  `change_feature_flags_for_next_epoch`, which assume `apply_diff`'s
  quantified postconditions, exceed the verification budget; `apply_diff`
  reaches the recursion limit and reads a parameter with `old` in a loop
  invariant; `on_new_epoch`.
- `bit_vector`: range-quantified loop invariants and postconditions
  (quantifier automation, section 1);
  `shift_left_for_verification_only` exceeds the verification budget.
- `acl`: a kernel type mismatch in the denotation of the generic loop of
  `contains`; `add` exceeds the verification budget; `remove` calls the
  native `vector::move_range`, which has no contract.
- A residual obligation that no clause marker locates is reported at the
  module header, not at the function.
- **Verification in the Move CLI (later).** The package verifies a
  checked-in copy of the standard library sources, which already drifts
  from `aptos-move/framework/move-stdlib` (`cmp`, `signer`). Instead,
  Leaner verification is integrated into the Move CLI behind a flag, so
  the framework packages are verified in place with the usual tool set,
  as the Move Prover is run today; the copy then serves only the
  Move-to-LeanerLang baselines.

## 4. Shared checking

Design: [`lir-design.md`](lir-design.md), Phases 1–2.

Done: a single-run `validate` with authoritative name resolution,
unification typing of executable and specification bodies, and the
initialization and borrow analyses run once with certificates on
`ValidatedUnit`.

Open:

- The checked trait-selection evidence table (also blocking
  [`rust-mir-design.md`](rust-mir-design.md)).
- The certification pass that turns `prepare*` into pure mode filters.
- Borrow checking: general non-lexical loan death, dependency and unknown
  aggregate alias propagation, nominal variance, use-site region solving.
- Strict external JSON compatibility of RawUnit and the full staged API.

## 5. Runtime semantics

Design: [`elaboration-design.md`](elaboration-design.md) (runtime model,
big-step semantics, interpreter).

Open: the metatheory of the big-step semantics — determinism,
completeness of the interpreter up to fuel, preservation, and no-stuck for
prepared invocations.

## 6. MonoVM differential harness

Design: [`monovm-link-design.md`](monovm-link-design.md).

Done: M0–M3 and M4a (the linked adapter, marshalling, the three-way
differential driver, composite values); M4b in part.

Open: resources and events, and mutable-reference out-parameters (M5).

## 7. Rust frontend

Design: [`rust-mir-design.md`](rust-mir-design.md).

Open: the M0 gate (blocked upstream, below), then M1 mapper completion and
Charon differential tests, M1.5 prebuilt exporter distribution, M2
contracts and `verify` for Rust through `denote`, M3 regions over the
prophetic model, M4 drops and panics, M5 the unsafe profile
([`unsafe-pointers.md`](unsafe-pointers.md), a proposal scheduled here),
M6 library models, M7 alignment proofs.

## 8. Surface and backends

Designs: [`leaner-lang.md`](leaner-lang.md) and
[`lir-design.md`](lir-design.md) Phases 4, 6, 7.

Done: validated LIR lowers to XIR, and compiler-v2 compiles `.lean`
sources through it (2026-09-25).

Open: the LeanerLang forms still stated as target language (`core.*`,
`spec.*`, extension and dependency forms); retiring the NSIR bridge;
corpus-wide semantic alpha-equivalence and source maps; a
compiler-correctness theorem connecting source verification to the
emitted bytecode.

## Tests

### Gates

| Gate | Result |
|---|---|
| `leaner-ir` build and `lake test`, with the `DenotePerformance` and `CompositionPerformance` cost gates | PASS |
| `leaner-move`, `leaner-rust` builds and tests | PASS |
| `leaner-e2e-tests` `lake test`: suites `move`, `rust`, `verify`, `check`, `monodiff` | PASS |
| Check fixtures | 76 of 76 pass exactly |
| Move-to-LeanerLang corpus round trip | every module is a typed fixed point |

The `verify` suite verifies the staged Move standard library; its baseline
records what does not verify yet (section 3).

### Check ledger

Each name is a `.lean` file under
[`leaner-e2e-tests/LeanerE2ETests/Check/<Folder>/`](../leaner-e2e-tests/LeanerE2ETests/Check/).
Every file passes: its whole output matches the adjacent `.exp` at the
driver's caps (180k verification heartbeats per target). Notes name what
a file covers beyond its title: intended negatives, authored proofs, and
files without `verify` targets.

| Folder | Files | Notes |
|---|---|---|
| Scalars | `Addresses`, `Arithmetic`, `BitVectors`, `Integers`, `Literals`, `Order`, `Signed`, `SpecLogicalArithmetic` | `BitVectors`: `pragma bv`; a wrong postcondition and the same leaf without the pragma fail (intended). `Order`: an authored proof of transitivity. |
| Structs | `Abilities`, `Invariants`, `PositionalStructs`, `Tuples` | `Abilities` has no `verify` targets. |
| Enums | `EnumPatterns`, `EnumPayloads`, `EnumRefContracts`, `EnumRefs`, `Enums` | `EnumRefs` is execution only. |
| Vectors | `VectorBounds`, `VectorOperations`, `Vectors` | A target whose guards stay undecided exhausts heartbeats rather than failing fast. |
| Control | `Aborts`, `ControlForms`, `LoopControlErrors`, `LoopInvariantErrors`, `LoopInvariants`, `Loops`, `LoopVerification` | `Aborts`: a false contract (intended). `LoopInvariantErrors`: an invariant not established at entry and at an iteration. |
| References | `BorrowCertificates`, `BorrowChecker`, `BorrowErrors`, `BorrowGlobalErrors`, `CorePrimitives`, `Freeze`, `Loans`, `Prophecies`, `References`, `ReturnedMutRefErrors`, `ReturnedMutRefs` | `BorrowCertificates` asserts certificates, no `verify`. `BorrowChecker`: twelve rejections at preparation, the accepted programs verified. |
| Storage | `CrossInv`, `GlobalBorrows`, `GlobalInv`, `LooseFrame`, `Normalized`, `Read`, `ResourceComposition`, `Storage`, `StorageSpecErrors` | `LooseFrame` carries an authored proof. |
| Calls | `AbstractClauses`, `Callees`, `Calls`, `Composition`, `InlinedCallees`, `Modules`, `Summaries` | Intended negatives: a caller does not see a `[concrete]` result (`AbstractClauses`), an opaque callee's body (`InlinedCallees`), a postcondition a callee of another module refutes (`Modules`). |
| Generics | `GenericCycles`, `GenericFunctions`, `GenericScalarCalls`, `Generics`, `GenericStorage` | |
| Specifications | `ContractErrors`, `DomainQuantifiers`, `Increment`, `RecursiveSpecFunctions`, `SpecFunctionErrors`, `SpecFunctions`, `WrongIncrement` | `DomainQuantifiers`: an existential no index satisfies and one over an empty vector (intended). `RecursiveSpecFunctions`: a lemma by induction and a `verify … by` using it. |
| Modules | `Attributes`, `EmptyModule`, `IntrinsicErrors`, `LoweringErrors`, `PreparationRetry`, `Rust` | `Attributes` and `EmptyModule` have no `verify` targets. |
| Examples | `Account`, `Corpus`, `OrderedMap`, `Quicksort` | `OrderedMap` and `Quicksort` verify through authored lemmas over arrays; `Quicksort`'s `partition` runs at a raised cap of 400k heartbeats (277M in total). |

### Conventions

A Check file is LeanerLang source with contracts, theorems, authored
proofs, and execution or diagnostic assertions. The driver discovers every
`Check/**/*.lean`, runs each in its own Lean process at the driver's caps,
and compares all diagnostics to the adjacent `.exp` (no `.exp` means empty
output). Run it from `leaner-e2e-tests` with
`LEANER_E2E_SUITE=check lake test`; `UB=1` regenerates baselines, and every
regenerated diff is reviewed.

- A baseline records intended behavior. A negative case's expected
  diagnostic names the construct or clause, and its line carries a
  trailing `-- error: <reason>`; an unsupported positive proof is never
  recorded as an expected failure.
- A file is promoted only by the driver at the unchanged caps; a passing
  pilot promotes nothing. Caps are not raised to count a port as done.
- Every `verify` audits its artifacts (denotation route, approved axioms
  only); a fixture adds no audit of its own.
- A module lays out each function as its `fun`, its `spec`, the
  `spec fun`s that specification needs (at their first use), the theorems
  its proof uses, and its `verify … by`, in this order; a function with a
  `spec` verifies without a `verify` item. Larger modules separate groups
  of functions with `-- ## Title` headers.
- Assertion-style IR, Move, and Rust tests stay in their owning packages.
  The deprecated packages are reference material and are not run.
- Source verification is not a compiler-correctness theorem for emitted
  bytecode.

## Out-of-band items

- **Upstream rustc ask, filed.** The two Rustc Public API gaps blocking
  the Rust M0 gate (`FnDef` exposes no predicates; no const-fn binder type
  query) are
  [rust-lang/rust#161892](https://github.com/rust-lang/rust/issues/161892).
  Until it lands the generic trait RawUnit fixture cannot satisfy the
  gate; the answer stays an upstream query, not a private `rustc_middle`
  read.
- **Security boundary.** Lean-source package discovery executes arbitrary
  host code at compile time; see the TODO in
  [`lir-design.md`](lir-design.md#todo-secure-lean-source-discovery-and-elaboration).
  It must be fixed before Lean-source discovery is a production compiler
  feature.

## Deliberately not scheduled

Phase 0 of [`lir-design.md`](lir-design.md) is a multi-party freeze with
one owner on both sides: the "no construct unclassified" gate is mechanized
by [`Capability.lean`](../leaner-ir/LeanerIR/Validation/Capability.lean),
and publishing RawUnit JSON v1 becomes work only when a consumer outside
this repository depends on it.

## Historical designs

[`historical/`](historical/) holds executed or superseded designs and
archives. They keep their rationale and measurements and are not updated:
[`verification-v2.md`](historical/verification-v2.md),
[`certifying-execution.md`](historical/certifying-execution.md),
[`generic-route.md`](historical/generic-route.md), and
[`verification-perf-audit.md`](historical/verification-perf-audit.md),
replaced by [`denotation.md`](denotation.md);
[`test-organization.md`](historical/test-organization.md) and
[`test-organization-history.md`](historical/test-organization-history.md),
the check ledger's earlier per-file notes, chronology, and v0 mappings,
now kept [here](#tests).
