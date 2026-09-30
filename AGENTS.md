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

## Pending maintainer decisions (ask at the start of a session)

The decisions below belong to the maintainer, not to an agent. At the start of a session,
before other work, present each open item to the maintainer with the explanation given here
(what it is, the options, what each option involves, the recommendation), and ask for a decision.
Do not act on an item until the maintainer decides. When one is decided and carried out, delete
it from this list (and from the matching bullet in `ROADMAP.md`) in the same commit.

1. **Delete the empty `LieLean/Basic.lean`.**
   - What it is: a placeholder left over from the initial package skeleton. It imports
     `Mathlib.Algebra.Lie.Basic`, defines nothing, and is imported only by `LieLean.lean`.
     Mathlib has no corresponding file, so it would never be upstreamed.
   - Options: (a) delete the file and its import line in `LieLean.lean`; (b) keep it.
   - What (a) involves: two-line change, a full `lake build` to confirm nothing depends on it.
     No declarations are lost.
   - Recommendation: (a).

2. **Rename `LieLean/RingTheory/FormalCharacter.lean` to a Mathlib-style path and namespace.**
   - What it is: a small, purely combinatorial file (a sign-reversing involution proving that the
     coefficients of `∏(1 - xᵢ) · ∏(1 - xᵢ)⁻¹` in infinitely many variables are `1` at `0` and `0`
     elsewhere; main result `FormalCharacter.sum_neg_one_pow_card_eq_ite`). It is used once, by
     `KacMoody/CharacterDenominator.lean` (the proof that the Kac–Moody denominator is inverse to
     the character of `M(0)`). Its namespace `FormalCharacter` is project-style rather than
     Mathlib-style, and `RingTheory/` misdescribes the content, which is enumerative combinatorics.
   - Options: (a) move it to e.g. `LieLean/Combinatorics/Enumerative/SignReversingInvolution.lean`
     and rename the namespace to something Mathlib would accept (e.g. declarations about `Finset`
     / `Finsupp` in their own namespaces); (b) leave it as is.
   - What (a) involves: moving the file, renaming its declarations, updating the one importer and
     `LieLean.lean`, a full build. It changes public names (only used internally). It matters
     only if the file is to be upstreamed (it is listed under "Upstreaming candidates").
   - Recommendation: (a), when convenient.

3. **Verify the "(check)" citations against the books.**
   - What it is: agents could not consult the sources, so section/theorem/equation numbers were
     reconstructed from memory and marked "(check)" wherever uncertain. There are roughly 1000
     such marks in about 180 files (count with `grep -c "(check)"`), citing Kac, Humphreys (three
     books), Bourbaki, Björner–Brenti, Kazhdan–Lusztig, Kac–Kazhdan, Garland–Lepowsky, Kumar,
     Kashiwara, Littelmann, Lusztig, Jantzen, Deodhar, and others. Many proofs are also marked as
     "reconstructed", i.e. not checked against the published argument.
   - Options: (a) an agent generates a checklist file (for each mark: file, line, declaration,
     the claimed reference, and the statement it is attached to), grouped by source, for a human
     with the books to verify; corrections then get applied and the "(check)" marks removed;
     (b) leave the marks as honest placeholders.
   - What (a) involves: generating the checklist is mechanical and cheap; the verification itself
     needs a person with access to the books (the agents' environment has no web access to the
     papers). Mathlib reviewers will expect exact references before upstreaming.
   - Recommendation: (a) if someone can check the books; otherwise (b) for now.

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
- Commits may go directly to `master` after a green full `lake build` and the axiom check.
  Never force-push.
- Commit messages: a short summary line naming the mathematical content, then details.
- Mathlib bumps: move to a newer Mathlib release tag with `lake update` in a dedicated commit, fix
  breakages, and note in `ROADMAP.md` anything that Mathlib has meanwhile added (delete our
  duplicate and use theirs).
- When a self-contained piece is Mathlib-ready (e.g. PBW), note it in `ROADMAP.md` under
  "Upstreaming candidates".
