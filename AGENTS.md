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

### Priority: classical foundations and clearly scoped generality

- The primary goal is to formalize existing classical and well-known quantum Lie theory
  as a stable foundation for downstream work. More generality is welcome, not a problem;
  keep the classical target and any stronger extension clearly distinguished.
- When an extension fails, explicitly report it as a boundary on extra generality unless
  it actually obstructs the classical target. Do not imply a published theorem is false
  or the main programme is blocked merely because a generalized encoding fails.
- Use bounded cases when they supply an identified lemma or construction needed for a
  roadmap theorem, not merely to accumulate examples or confidence in known mathematics.
- Run concrete confidence probes only to address a specific uncertainty about the formal
  statement, encoding or implementation. Kernel compilation, axiom checks and statement
  review remain required; established mathematical results do not need rediscovery by tests.
- If a generalized encoding fails to support a classical theorem, preserve a source-faithful
  route to the main target and state separately what is known about the extension.

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
- Sandboxed environments: if `lake exe cache get` cannot reach the Mathlib cache,
  `lake build <Module>` builds just the Mathlib files that module needs (slow but fine; never
  rebuild Mathlib wholesale). If elan's installer is blocked, download the toolchain release
  from GitHub and register it with `elan toolchain link`.
- Run `lake`/`lean` with stdin redirected (`< /dev/null`) in non-interactive shells; otherwise
  they can hang.
- Parallel work: use separate `git worktree`s (symlink `.lake/packages`, copy `.lake/build`),
  one Lean process per worktree at a time. When merging, `LieLean.lean` import conflicts are
  resolved by regenerating the sorted import list from the files under `LieLean/`. Check new
  top-level names against the whole library before merging: independent branches have clashed
  (e.g. `CartanDatum`, `antiInvolution`, `IsCategoryO.lieSubmodule`).

## Citations

- Cite section, theorem, equation and page numbers of the edition listed in the file's references,
  and only numbers you have checked there; otherwise cite the work without a locator.
- Give the most precise item ("Prop. 3.12 (d)", "proof of Thm. 9.11"); use "cf." when the source
  states a closely related but different result.
- When the source states a result under narrower hypotheses than the Lean statement (over `ℂ`, in
  finite type, for symmetrizable `A`), say so in the docstring. Kac and Kumar work over `ℂ`,
  Lusztig over `ℚ(v)`, Jantzen's *Lectures on quantum groups* in finite type throughout.
- Kac–Kazhdan, Adv. Math. 34 (1979), is cited together with Kumar's account (§2.3), which proves
  and credits its results.
- A proof note saying "reconstructed" or "our own" means the Lean proof does not follow the
  source's argument.

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

- Prefer general hypotheses as Mathlib does when the proof naturally allows them without
  detouring from the classical target; retain source hypotheses otherwise. State needed
  characteristic-zero assumptions explicitly as `[CharZero K]`.
- Keep files focused and reasonably short (Mathlib files are typically under ~1000 lines).

## Mathematical standards

- Record the source of every main result in its docstring: book, edition, chapter/section and
  theorem/equation number (e.g. "Kac, *Infinite dimensional Lie algebras*, 3rd ed., Thm. 9.11").
  If the proof is your own rather than the source's, say so.
- State theorems faithfully: keep the source's hypotheses (field, characteristic, symmetrizability,
  finiteness) unless you prove a more general version; never weaken or silently alter a statement
  to make it compile. If a printed statement or proof is wrong, record the correction explicitly.
- Completed results have no `sorry`, `admit`, or new `axiom`. The only acceptable axioms are
  `propext`, `Classical.choice` and `Quot.sound`. `lake env lean -DwarningAsError=true
  scripts/AxiomAudit.lean` checks this for every declaration of the library (CI runs it after
  the build); `scripts/check_axioms.sh Decl.name …` prints the axioms of individual declarations.
- Audit statements as well as proofs: non-vacuous hypotheses, correct quantifiers, no accidental
  specialization.

## Workflow

- `ROADMAP.md` is the plan; keep its status markers current when a milestone lands.
- Work in small, complete steps: each commit should build (`lake build` green, warnings are
  errors) and contain no `sorry`.
- Commits may go directly to `master` after a green full `lake build` and the axiom check.
  Never force-push.
- Commit messages: a short summary line naming the mathematical content, then details.
- Mathlib bumps: move to a newer Mathlib release tag with `lake update` in a dedicated commit, fix
  breakages, and note in `ROADMAP.md` anything that Mathlib has meanwhile added (delete our
  duplicate and use theirs).
- When a self-contained piece is Mathlib-ready (e.g. PBW), note it in `ROADMAP.md` under
  "Upstreaming candidates".
