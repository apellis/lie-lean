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
- Changes land on `master` through PRs with green CI (full build and axiom audit). Push directly
  only when the maintainer has authorized it for that work. Never force-push.
- Commit messages: a short summary line naming the mathematical content, then details.
- Mathlib bumps: move to a newer Mathlib release tag with `lake update` in a dedicated commit, fix
  breakages, and note in `ROADMAP.md` anything that Mathlib has meanwhile added (delete our
  duplicate and use theirs).
- When a self-contained piece is Mathlib-ready (e.g. PBW), note it in `ROADMAP.md` under
  "Upstreaming candidates".

## Staying on course

These rules apply to every contributor and take precedence over local habits or private
instructions that conflict with them.

**Targets and scope**

- Every PR advances a specific numbered result of a cited source (theorem, proposition,
  corollary, lemma, definition or equation) or a roadmap item that one of them needs. The PR
  title or body names it. Supporting lemmas land with, or shortly before, the result that uses
  them.
- Formalize what the source states. Do not label results "original", and do not develop new
  theory when a source step is missing. When a cited proof relies on a reference that is not
  available, on a step that has a gap, or on a result outside the library, stop and record this
  in the tracking issue as a question for the maintainer. The options are: (a) obtain the
  reference; (b) take the missing input as an explicit, documented hypothesis of the dependent
  results; (c) build a replacement route. Do not start (c) without the maintainer's approval.
- Scope decisions are the maintainer's. These include declaring a numbered result out of scope,
  choosing between several valid conventions, and substituting a different object for the one
  the source uses (for example a crystal basis for a canonical basis). List them as open
  questions; do not decide them silently.
- Effort budget: suppose a sub-route has taken about five PRs, or about 3000 lines, without a
  numbered result landing. Stop and post in the tracking issue: what is done, what remains, and
  an honest estimate of the distance to the numbered result. Then wait for the maintainer before
  continuing that sub-route.
- Prove one form of a result. Restate it in another form (maps → bimodule maps → natural
  isomorphisms → mates, and so on) only when a named downstream result needs that form.

**Statements**

- A headline statement carries exactly the source's hypotheses, after any recorded erratum
  correction.
- An extra hypothesis that the current proof route needs is allowed only on an intermediate
  statement. Its docstring must say so, the README status must say so, and a roadmap item must
  track its removal.
- Names, docstrings and status tables never overstate. Do not use `_unconditional` on a
  conditional theorem, and do not use "full" or "complete" for a statement that assumes part of
  its conclusion.
- An erratum entry gives the printed statement, the corrected statement with the extra
  hypothesis or correction, the declarations, and a short paragraph that can be sent to the
  authors as is.

**Lean engineering**

- Elaboration trouble is not a mathematical obstruction. Examples: `whnf` or `isDefEq` timeouts
  on dependent transports, heartbeat limits, motive errors, slow instance search.
- After two failed attempts at the same proof, redesign the encoding. Possible changes: reindex
  so that the types agree definitionally, prove one generic lemma instead of many instances, or
  avoid nested casts. Do not raise `maxHeartbeats` or retry with a larger budget.
- Names of declarations, modules and PRs describe the mathematics. Avoid process adjectives
  ("actual", "genuine", "original", "native", "fixed", "frontier"), stage labels (`LegA`,
  `AdapterB7`, `PbwL3`) and "WIP". A PR whose title says WIP is not merged.

**Workflow and evidence**

- All proof work happens on topic branches of this repository and lands through PRs with green
  CI. Work that does not build yet may be pushed as a draft PR. Proof developments are not kept
  in private copies, scratch archives or other repositories.
- The evidence that a result is done is CI: full build with warnings as errors, plus the axiom
  audit. Agreement between reviewers, private sign-offs, hash manifests and log archives are not
  evidence. Do not commit logs, manifests, archives or review packets.
- The same PR updates the README/ROADMAP status row and the tracking issue. Close an issue when
  its goal is met.
