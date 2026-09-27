/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryO

/-!
# Submodules of modules in category `𝒪`

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.lieSubmodule`: submodules of modules in `𝒪` lie
  in `𝒪`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.1.
-/

open Module LieModule

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

lemma mem_weightSpaceOfMap_lieSubmodule_iff {N : LieSubmodule K P.KacMoodyAlgebra V}
    {μ : Dual K H} {m : N} :
    m ∈ weightSpaceOfMap N (h P) μ ↔ (m : V) ∈ weightSpaceOfMap V (h P) μ := by
  simp only [mem_weightSpaceOfMap, Subtype.ext_iff, LieSubmodule.coe_bracket,
    LieSubmodule.coe_smul]

/-- Submodules of modules in the category `𝒪` lie in `𝒪` ([Kac] §9.1). -/
theorem IsCategoryO.lieSubmodule (hV : IsCategoryO P V) (N : LieSubmodule K P.KacMoodyAlgebra V) :
    IsCategoryO P N := by
  have hinj : Function.Injective N.toSubmodule.subtype := Submodule.injective_subtype _
  have hmap (μ : Dual K H) : (weightSpaceOfMap N (h P) μ).map N.toSubmodule.subtype ≤
      weightSpaceOfMap V (h P) μ := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_weightSpaceOfMap_lieSubmodule_iff.mp hm
  refine ⟨?_, fun μ ↦ ?_, ?_⟩
  · rw [eq_top_iff]
    rintro m -
    have hm : (m : V) ∈ N.toSubmodule ⊓ ⨆ μ ∈ Set.univ, weightSpaceOfMap V (h P) μ := by
      refine ⟨m.2, ?_⟩
      simp only [Set.mem_univ, iSup_pos]
      rw [hV.iSup_weightSpaceOfMap_eq_top]
      trivial
    have := inf_iSup_weightSpaceOfMap_le (h P) N.toSubmodule (fun a m hm ↦ N.lie_mem hm)
      Set.univ hm
    simp only [Set.mem_univ, iSup_pos] at this
    have hle : ⨆ μ, N.toSubmodule ⊓ weightSpaceOfMap V (h P) μ ≤
        (⨆ μ, weightSpaceOfMap N (h P) μ).map N.toSubmodule.subtype := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun μ x ⟨hxN, hxμ⟩ ↦
        ⟨⟨x, hxN⟩, mem_weightSpaceOfMap_lieSubmodule_iff.mpr hxμ, rfl⟩
    obtain ⟨m', hm', hmm'⟩ := hle this
    rwa [hinj hmm'] at hm'
  · have := hV.finiteDimensional_weightSpaceOfMap μ
    have : FiniteDimensional K ((weightSpaceOfMap N (h P) μ).map N.toSubmodule.subtype) :=
      Submodule.finiteDimensional_of_le (hmap μ)
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _).symm
  · obtain ⟨s, hs⟩ := hV.exists_finset
    refine ⟨s, fun μ hμ ↦ hs μ fun hbot ↦ hμ ?_⟩
    rw [eq_bot_iff]
    intro m hm
    have := mem_weightSpaceOfMap_lieSubmodule_iff.mp hm
    rw [hbot, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext this

end Matrix.Realization.KacMoodyAlgebra
