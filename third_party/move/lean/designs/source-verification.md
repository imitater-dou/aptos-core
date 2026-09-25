# Verifying Move and Rust sources

Status: implemented for Move files, Move packages whose modules link the
modules they use (the Move standard library is verified this way), and
single Rust files. Open work is listed in [`roadmap.md`](roadmap.md),
section 3.

A Move or Rust file is verified by compiling it to LeanerLang and verifying
that rendering; every message is reported in the coordinates of the file it
came from.

```text
foo.move ─ compiler-v2 XAST ─┐
                             ├─ validated LIR ─ LeanerLang rendering ─ elaboration ─ messages
foo.rs ─── rustc MIR ────────┘                  (+ foo.spec.lean items)                  │
                                                                                          ▼
                                                           foo.move / foo.rs / foo.spec.lean positions
```

## Commands

```bash
cd leaner-move && lake build leaner-move
lake env .lake/build/bin/leaner-move verify foo.move [--output foo.move.lean]

cd leaner-rust && lake build leaner-rust
lake env .lake/build/bin/leaner-rust verify foo.rs [--spec foo.spec.lean] \
  [--output foo.rs.lean] [-- <rustc arguments>]
```

`lake exe` works as well but replays the build log first. The Move command
needs the exchange frontend (`APTOS_MOVE_CLI`, see the tree's `CLAUDE.md`).
Each command writes the rendering beside the source (`foo.move.lean`,
`foo.rs.lean`) for inspection, prints one `file:line:column: severity:
message` line per message, and exits non-zero when any is an error.

## Specifications

A Move file's specifications are its own `spec` blocks. A Rust file has none;
they are LeanerLang items — `spec f where …` blocks, specification functions,
module invariants — in `foo.spec.lean` beside `foo.rs`, or in the file
`--spec` names:

```lean
spec max where
  ensures result >= left && result >= right
  ensures result == left || result == right
```

The items are appended to the rendered namespace, indented one level, so
they may name every declaration of the crate.

### Move frames

A LeanerLang frame is closed: without `modifies` a function changes no global
memory. A Move specification frames only the resource families it names
targets for. The Move frontend states Move's reading explicitly
(`LeanerMove/Frontend/Frames.lean`): no targets and a transitive global write
become `modifies *`; targets on a non-`opaque` function become
`modifies <targets>, *`.

## Mapping messages

The shared driver is `LeanerLang.SourceVerify` in `leaner-ir`. The rendering
is elaborated in the command's own process, so the elaborators run natively,
and a message is mapped by the first rule that applies:

1. A position in the appended specification items maps line by line to the
   specification file.
2. Otherwise the source's validated namespace and the one elaborated from the
   rendering are aligned: declarations by name, then node by node while the
   two shapes agree — expressions, patterns, places, and contract clauses by
   kind and occurrence. The position takes the source range of the innermost
   aligned node around it. A contract's location is its whole `spec` item, so
   the summary a failed function reports at its `spec` lands on the source's
   `spec` block.
3. A position outside every aligned node stays in the generated file.

## Tests

`leaner-e2e-tests/LeanerE2ETests/SourceVerify/` holds the examples: every
`.move` and `.rs` file there is verified as the commands do it, and its
messages are the baseline `<name>.exp` (none when it verifies). The Move
standard library of the Move corpus is verified as a package, its modules
rendered in dependency order and each linking the modules it uses; its
baseline `MoveStdlib.exp` lists what does not verify yet.

## Known gaps

- A residual obligation no clause marker locates (for example an
  unprovable intermediate fact) lands on the enclosing module, in authored
  LeanerLang as well.
- A clause's message quotes its LeanerLang rendering, not the source text.
