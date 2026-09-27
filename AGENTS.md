# Working in lie-lean

Instructions for contributors, human or AI. They are self-contained: this repository, Mathlib,
and the references in `ROADMAP.md` are all that is needed.

## Scope

- Lie theory and the representation-theoretic structures used in categorification: Lie algebras,
  their enveloping algebras and representations, Kac–Moody algebras, root systems, Weyl and
  Coxeter groups, Iwahori–Hecke algebras and Kazhdan–Lusztig theory, category `𝒪`, Lie algebra
  homology, crystals, and quantum groups (Phase 2 of `ROADMAP.md`). Nothing farther afield.
- Use Mathlib wherever it already has the concept or result. Before defining anything, search
  Mathlib (at the pinned version) for an existing definition; extend it rather than duplicating it.
- Everything should be written so it can be upstreamed to Mathlib with minimal changes.

## Environment

```sh
# elan (Lean version manager), if not installed:
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source ~/.elan/env
lake exe cache get      # prebuilt Mathlib; never rebuild Mathlib from source
lake build              # whole library
lake build LieLean.Algebra.Lie.Foo   # a single module
```

- The toolchain comes from `lean-toolchain`; do not rely on a global default.
- Do not run `lake update` except as a deliberate Mathlib bump (see below).
- Diagnose tool, download and memory failures separately from proof errors.

## Layout and naming (Mathlib-ready)

- Files live under `LieLean/` and mirror the path they would have in Mathlib:
  `LieLean/Algebra/Lie/UniversalEnveloping/PBW.lean` is intended for
  `Mathlib/Algebra/Lie/UniversalEnveloping/PBW.lean`. Import new files from `LieLean.lean`.
- Declarations use the namespaces Mathlib would use (e.g. `UniversalEnvelopingAlgebra`,
  `LieAlgebra`, `LieModule`, `Matrix`), not a project namespace. Before introducing a name,
  `grep` Mathlib for it. Name clashes with later Mathlib versions are resolved at bump time.
- Follow the Mathlib style guide and naming conventions
  (https://leanprover-community.github.io/contribute/style.html,
  https://leanprover-community.github.io/contribute/naming.html): lines ≤ 100 characters,
  `/-! … -/` module docstrings with a "Main definitions / Main results / References" structure,
  docstrings on every definition and main theorem, `theorem` for Prop-valued results.
- File header:

  ```lean
  /-
  Copyright (c) 2026 Alex Ellis. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Alex Ellis
  -/
  ```

- Prefer general hypotheses as Mathlib does: commutative rings where the argument allows,
  fields of characteristic zero only where needed (state it as `[CharZero K]`).
- Keep files focused and reasonably short (Mathlib files are typically under ~1000 lines).

## Mathematical standards

- Record the source of every main result in its docstring: book, edition, chapter/section and
  theorem/equation number (e.g. "Kac, *Infinite dimensional Lie algebras*, 3rd ed., Thm. 9.11").
  If you could not consult the source and reconstructed an argument, say so.
- State theorems faithfully: keep the source's hypotheses (field, characteristic, symmetrizability,
  finiteness) unless you prove a more general version; never weaken or silently alter a statement
  to make it compile. If a printed statement or proof is wrong, record the correction explicitly.
- Completed results have no `sorry`, `admit`, or new `axiom`. Check headline declarations with
  `scripts/check_axioms.sh Decl.name …`; the only acceptable axioms are `propext`,
  `Classical.choice` and `Quot.sound`.
- Audit statements as well as proofs: non-vacuous hypotheses, correct quantifiers, no accidental
  specialization.

## Workflow

- `ROADMAP.md` is the plan; keep its status markers current when a milestone lands.
- Work in small, complete steps: each commit should build (`lake build` green, warnings are
  errors) and contain no `sorry`.
- Commits may go directly to `main` after a green full `lake build` and the axiom check.
  Never force-push.
- Commit messages: a short summary line naming the mathematical content, then details.
- Mathlib bumps: move to a newer Mathlib release tag with `lake update` in a dedicated commit, fix
  breakages, and note in `ROADMAP.md` anything that Mathlib has meanwhile added (delete our
  duplicate and use theirs).
- When a self-contained piece is Mathlib-ready (e.g. PBW), note it in `ROADMAP.md` under
  "Upstreaming candidates".
