import LieLean
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Checks that every declaration defined in this library depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound` (so in particular on no `sorryAx` and no local
axiom). The library uses Mathlib-style namespaces rather than a `LieLean` name root, so
declarations are selected by their *module* name (`LieLean.*`), not by their name.

Run from the package root, after a full build:

    lake env lean -DwarningAsError=true scripts/AxiomAudit.lean

The command fails with an error naming the first offending declaration; on success it reports
the number of declarations and modules audited.
-/

open Lean Elab Command

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut modules : NameSet := {}
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some modName := moduleNames[idx.toNat]? | continue
    unless modName.getRoot == `LieLean do continue
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name} (module {modName})"
    count := count + 1
    modules := modules.insert modName
  logInfo m!"Audited {count} declarations in {modules.size} LieLean modules; \
    all transitive axioms are allowed."
