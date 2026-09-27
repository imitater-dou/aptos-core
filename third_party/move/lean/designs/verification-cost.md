# Verification cost: measurement notes

Status: 2026-09-27. A working log for whoever next works on verification
cost (roadmap §1, **Cost**). It covers how to measure, what was changed
and why, what was tried and rejected, and where the time still goes.
The design rules themselves are in [`denotation.md`](denotation.md)
("Principles that yield performance" and the closer notes). Update the
numbers in the roadmap, not here.

## Where the time went (2026-09-27 round)

The work happened on branch `wrwg/leaner-check-speed` (commits `c14bdd0e`
through `be7b87ea`). The Check fixtures below are the 76 files under
`leaner-e2e-tests/LeanerE2ETests/Check`. Times are summed per file, with
four files running at once on four cores.

| Step | Check suite total | Kernel (type checking) |
|---|---|---|
| Start | 821s | 274s |
| Bounds asserted once per leaf | | |
| Incremental normalization (closer −19%) | | |
| Denotation rewritten by its equations (kernel −14%, closer −20%) | | |
| Preparation certificates without array indexing (kernel −19%) | 660s | 191s |
| Erasure analysis read through arena indexes | 621s | |

The table leaves a cell empty where that step was not measured on its own.
`ReturnedMutRefs`, the slowest fixture, took 98s before the last two steps
and 86s after them. Its kernel time went from 68s to 47s to 31s.

## How to measure

Heartbeats do not show the largest cost: the kernel checks without
heartbeats, and a kernel stall shows up as time inside whichever `simp`
first waits for a certificate. Use all four instruments below.

1. **Wall time and exactness per fixture.** Run every Check file from
   `leaner-e2e-tests`. Use the driver caps
   (`-DmaxHeartbeats=180000 -Dweak.leaner.verifyHeartbeats=180000`), run
   four files at once with `xargs -P 4`, and compare each output with its
   `.exp` file; a missing `.exp` means the output must be empty. Any
   difference in output is a regression, even when a change is meant only
   to be faster.
2. **Closer heartbeats by stage.** Add `-Dweak.leaner.denoteDebug=true`.
   Every target then prints a line of the form
   `closer: <N>k … bind ×k Nk; exit …; leaf …`. Sum each stage across the
   suite and compare two runs stage by stage.
3. **Time by category.** Add `-Dprofiler=true -Dprofiler.threshold=100000`
   to get the per-file totals:
   - `type checking` is the kernel;
   - `interpretation` is the closer and elaboration;
   - `simp` is simp.

   `-Dtrace.profiler=true` adds per-declaration `[Kernel]` times.
   Certificates the first verify has to wait for show up as the `addDecl`
   time of an auxiliary such as `_simp_2`.
4. **Kernel unfolds of one certificate.** Paste this command into a copy
   of a fixture (below `import LeanerE2ETests.CheckSupport`). Then add
   `#kdiag <theorem>` before the fixture's final `end` for each
   certificate, for example
   `«0x42».returned_mut_refs.borrow_first_after_break.compiled_eq`:

   ```lean
   open Lean Elab Command in
   elab "#kdiag " id:ident : command => liftTermElabM do
     let some info := (← getEnv).find? id.getId | throwError "no {id}"
     let .thmInfo t := info | throwError "not a theorem"
     let tv : TheoremVal := { t with name := id.getId ++ `recheck }
     let kenv := ((← getEnv).toKernelEnv).enableDiag true
     let t0 ← IO.monoMsNow
     match Lean.Kernel.Environment.addDeclCore kenv 0 (.thmDecl tv) none with
     | .ok kenv' =>
       let counts := kenv'.getDiagnostics.unfoldCounter.toList.toArray.qsort
         (fun a b => a.2 > b.2)
       logInfo m!"{id.getId}: {(← IO.monoMsNow) - t0}ms, top {(counts.extract 0 40).toList}"
     | .error _ => logInfo m!"kernel error"
   ```

   A high count of `List.get`, `List.rec`, or `List.length._f` means array
   indexing inside a kernel-evaluated computation (see below). Do not
   compute a checksum over a big structure with `Array.foldl` in the
   kernel; one such attempt ran out of memory at 13.6 GB.

`perf record` on `lean` works if a statically linked Lean binary exposes
the kernel symbols. It showed the same hot spots as the instruments above,
so they are enough in practice.

Before committing a change, run everything that `CLAUDE.md` lists:
- the Check suite, with exact output;
- `leaner-ir` `lake test`, including the `DenotePerformance` and
  `CompositionPerformance` gates, re-recorded only for a deliberate cost
  change and with the diff reviewed;
- the stdlib verify baseline (`LEANER_E2E_SUITE=verify`);
- `leaner-move` and `leaner-rust` `lake test`.

Run nothing else in parallel with a timing comparison. Never rebuild
`leaner-ir` while a suite run is reading its `.olean` files.

## What was learned

- **An array read in a kernel-evaluated computation costs a list walk.**
  In the kernel, an `Array` is a structure over a `List`:
  - `a[i]?` walks `i` cells;
  - `a.size` walks the whole list;
  - `Array.foldl`, `find?`, and `contains` over an index range are
    quadratic.

  The preparation certificates (`marked_eq`, the erasure chunks) and
  `compiled_eq` are evaluated by the kernel, so they must:
  - iterate `toList`;
  - read arenas through an `IndexedArena`, a balanced tree built in one
    pass by `IndexedArena.build`;
  - count sizes once.

  The native path keeps its arrays; an `_eq` lemma connects the indexed
  form to the native one (`sharedReferenceErasureChunksIndexed_eq`,
  `IndexedArena.get?_ofArray`).
- **Unfolding a big recursive definition leaves the kernel to redo it.**
  `simp` unfolding `Term.denote` records no proof steps, so the kernel
  re-reduces its 61-way matcher, some 27k nodes. Rewriting with the
  equation lemmas (`lir_denote_equations`) makes each step an instance the
  kernel only checks. The `call` equation has an index
  (`ResultShape.bodyType`) that does not match at reducible transparency,
  so plain unfolding stays as the fallback.
- **In `simp`, the cost is per node, not per rule.** Each lookup reduces
  the reducible carriers in implicit arguments (`NTy.carrier`, `HEnv`) by
  smart unfolding; this is about half of every normalization. The closer
  therefore normalizes only what a step creates (`normalizeAround` with
  known-normal subterms) instead of renormalizing the goal.
- **Repeated leaf work.** Saturation used to reassert bounds that an
  ancestor goal had already asserted. It now records them by goal content,
  compared without regard to hypothesis order.

## Tried and rejected

| Experiment | Result |
|---|---|
| `dsimp := false` in the normalizer | 8 fixtures stopped verifying |
| `index := false` for the normalization simp set | slower |
| Precompiling `LeanerIR` (`precompileModules`) | no gain; cross-library dynlib load error |
| Equation lemmas without the unfolding fallback | `break_with_returned_pair` fails (the `call` index mismatch above) |
| A per-view table of native types in `CompileNamespace`, so `compiled_eq` would stop re-deriving types | 1% fewer unfolds in `compiled_eq`, same time; the Check suite went from 621s to 633s, because the view certificate derives every type, including unused ones |

## Where the cost is now

For the three slowest fixtures (kernel / closer and elaboration / simp):

| Fixture | Kernel | Closer and elaboration | Simp |
|---|---|---|---|
| `ReturnedMutRefs` | 31s | 40s | 11s |
| `VectorOperations` | 16s | 12s | 1s |
| `OrderedMap` | 11s | 15s | 12s |

Leads, most promising first:

1. **`compiled_eq`**, up to 1s per function, for example
   `borrow_first_after_break`: about 80k unfolds, dominated by `List.rec`,
   and about 4.4k `List.get` with 2.7k `instDecidableEqList` and
   `List.length`. Some of the remaining lookups are still array reads:
   - `unit.namespaces[…]?` and `calleeNs.functions[…]?` for calls and
     constants;
   - `targetNs.structs[…]?` and the names table in `ntyOfFuel`;
   - `loanFacts[…]?`;
   - `declaration.locals`.

   The list equality probably comes from comparing the evaluated function
   with its literal, or from the `List.Nodup` decisions of enum types.
   Split the certificate's cost into evaluation and comparison before
   changing anything.
2. **`marked_eq`**, about 2.6s per module.
3. **Carrier unfolding in `simp`.** Carriers whose instances are stated at
   the row type would avoid smart unfolding, which is a deeper change to
   `Types.lean`.
4. **Leaves that no decider closes.** Each saturation round over a large
   context costs 8–18M heartbeats.

## Resume here (2026-09-27, quantifier automation in progress)

The branch has moved on from cost to roadmap §1 **Quantifier automation**.
The commit "Decide quantified leaves at an instance" is validated:
`bit_vector::set` and `unset` verify, and the Check suite, the gates and the
stdlib baseline were all rerun for it.

The WIP commit after it is **not validated**. It has not been through the
Check suite, the `leaner-ir` gates, the stdlib baseline, or the
`leaner-move`/`leaner-rust` tests. It contains:

- **`ResultShape.bodyType` is `@[reducible]`** (`Types.lean`). A callee's
  result type reached instance arguments (a lookup's `GetElem?` instance at
  `(ResultShape.one τ).bodyType`), which simp matches at instance
  transparency only. So `Array.getElem?_eq_none_iff` and similar never
  fired. This fixes the `aborts_if` and the `index - 1` invariant of
  `bit_vector::longest_set_sequence_starting_at`. It may also let the
  `call` equation lemma match, so that `Term.lean` can drop the unfolding
  fallback of `lir_denote_equations` (the `Term.denote`/`Args.denote`
  attribute); try that, since it is a cost win if it holds.
- **`Bool.not_eq_false'` and `Bool.not_eq_true'` in `lir_denote_norm`.**
  This is a global normalization change; check the gates.
- **`leaner_denote_range_instance`** (`Close.lean`). It handles a goal one
  position past the range of a quantified hypothesis, which extends a range
  invariant by one iteration:
  1. apply the hypothesis;
  2. require exactly one premise, a comparison, that omega does not prove;
  3. split on that premise;
  4. in the branch where the premise fails, pin the position to the bound
     by omega, substitute, and decide the goal by the normalized context.

  It is tried after `leaner_denote_instance` in two places:
  `leaner_denote_decide_residual`, and the budgeted fallback of
  `leaner_denote_leaf`. There it runs first as stated and then after
  `leaner_denote_prepare`.

What this WIP commit achieves: `longest_set_sequence_starting_at`'s
`ensures ∀ (i in start_index .. result)` now verifies. **Open:** its loop
invariant `∀ (j in start_index .. index), self.is_index_set(j)` is still
"not preserved" in automatic mode, although on the prepared leaf
(`verify … by all_goals first | leaner_denote_instance |
leaner_denote_range_instance`) the tactic closes it. Two causes are likely:
- the fallback's heartbeat budget (`instanceAttemptHeartbeats`, 20M) is
  exhausted by the pipeline before the prepared attempt runs;
- the automatic leaf's goal is not the prepared leaf.

To find out, time the stages with `-Dweak.leaner.denoteDebug=true`, and
consider trying the prepared instance attempt before the pipeline.

Method: build a scratch LeanerLang file from the rendered module
(`leaner-e2e-tests/LeanerE2ETests/MoveToLeanerLang/MoveStdlib/sources/*.exp.lean`,
concatenating `error`, `mem`, `vector` for `acl`), and run it with
`lake env lean` from `leaner-e2e-tests`:
- `bit_vector` takes 40s; the one function alone takes 16s.
- `verify f by trace_state; all_goals sorry` shows the prepared leaves.
- A copy of a closer tactic inside the scratch file, logging with
  `IO.eprintln` (a `logInfo` is undone by `saveState.restore`), shows why
  it fails.

Before merging, validate (see "How to measure"):
- the Check suite, exact;
- `leaner-ir` `lake test`, with any gate diff reviewed;
- the stdlib baseline, regenerated with `UB=1` and its diff reviewed;
- `leaner-move` and `leaner-rust` tests.

Then update the roadmap (Quantifier automation, the `bit_vector` item) and
`denotation.md`. After `longest_set_sequence_starting_at`, the next goals
are:
- `shift_left_for_verification_only` (budget), and the `bit_vector` struct
  invariant after it;
- `acl` (an injectivity invariant over two indices, and the kernel type
  mismatch in the generic `contains` loop).
