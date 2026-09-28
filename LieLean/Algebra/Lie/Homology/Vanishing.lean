/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Complex

/-!
# Vanishing of concrete Chevalley–Eilenberg homology

The concrete homology `H_k(L, M)` vanishes exactly when every cycle is a boundary.
In positive degrees this is equivalent to the usual range-equals-kernel criterion for
exactness of the Chevalley–Eilenberg differentials.

## Main results

* `LieModule.ChevalleyEilenberg.subsingleton_homology_iff`: vanishing in any degree is
  equivalent to equality of boundaries and cycles.
* `LieModule.ChevalleyEilenberg.subsingleton_homology_succ_iff`: positive-degree vanishing
  is equivalent to equality of the incoming range and outgoing kernel.

## References

These elementary consequences are reconstructed directly from the definitions in
`LieLean.Algebra.Lie.Homology.Complex`; no external source was consulted.
-/

namespace LieModule.ChevalleyEilenberg

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Homology vanishes exactly when every cycle is a boundary, including in degree zero.
Reconstructed directly from the concrete quotient-image definition of homology. -/
theorem subsingleton_homology_iff (k : ℕ) :
    Subsingleton (homology R L M k) ↔ boundaries R L M k = cycles R L M k := by
  rw [Submodule.subsingleton_iff_eq_bot, homology, ← LinearMap.le_ker_iff_map,
    Submodule.ker_mkQ]
  exact ⟨fun h ↦ le_antisymm (boundaries_le_cycles k) h, fun h ↦ h.ge⟩

/-- Positive-degree cycles are the image of the kernel of the outgoing differential.
Reconstructed from `incl_mem_cycles_succ_iff`. -/
theorem cycles_succ_eq_map_ker (k : ℕ) :
    cycles R L M (k + 1) = (LinearMap.ker (d R L M k)).map (incl R L M (k + 1)) := by
  ext c
  constructor
  · intro hc
    obtain ⟨t, rfl⟩ := hc.1
    exact ⟨t, incl_mem_cycles_succ_iff.mp hc, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact incl_mem_cycles_succ_iff.mpr ht

/-- Positive-degree homology vanishes exactly when the incoming range equals the outgoing
kernel. Reconstructed from the concrete descriptions of cycles and boundaries. -/
theorem subsingleton_homology_succ_iff (k : ℕ) :
    Subsingleton (homology R L M (k + 1)) ↔
      LinearMap.range (d R L M (k + 1)) = LinearMap.ker (d R L M k) := by
  rw [subsingleton_homology_iff, boundaries_eq_map_d, cycles_succ_eq_map_ker,
    (Submodule.map_injective_of_injective (incl_injective (k + 1))).eq_iff]

end LieModule.ChevalleyEilenberg
