/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaPBW
import Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# The irreducible highest-weight modules `L(Λ)`

The Verma module `M(Λ)` over the Kac–Moody algebra `𝔤(A)` has a unique maximal proper
submodule `M'(Λ)`, the sum of all submodules not containing `v_Λ`; the quotient
`L(Λ) = M(Λ)/M'(Λ)` is irreducible, and `L(Λ) ≅ L(μ)` only if `Λ = μ` ([Kac] §9.2–9.3).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.maxSubmodule`: the maximal proper submodule
  `M'(Λ)` of `M(Λ)`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule`: the irreducible module `L(Λ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.le_maxSubmodule_iff`: a submodule of `M(Λ)` is
  proper iff it is contained in `M'(Λ)`; `isCoatom_maxSubmodule`: `M'(Λ)` is a maximal proper
  submodule.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.hwv_notMem_iff_inf_weightSpace_eq_bot`:
  a submodule does not contain `v_Λ` iff its `Λ`-weight space is zero.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.exists_eq_sub_of_mem_weightSpace`: the weights
  of any quotient of `M(Λ)` lie in `Λ - Q₊`.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.isIrreducible`: `L(Λ)` is irreducible.
* `Matrix.Realization.KacMoodyAlgebra.IrreducibleModule.eq_of_equiv`: `L(Λ) ≅ L(μ)` implies
  `Λ = μ`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.2–9.3.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (Λ : Dual K H)

omit [CharZero K] in
/-- A morphism of `𝔤(A)`-modules preserves weight spaces. -/
lemma map_mem_weightSpaceOfMap {V W : Type*} [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V] [AddCommGroup W]
    [Module K W] [LieRingModule P.KacMoodyAlgebra W] [LieModule K P.KacMoodyAlgebra W]
    (φ : V →ₗ⁅K,P.KacMoodyAlgebra⁆ W) {μ : Dual K H} {v : V}
    (hv : v ∈ weightSpaceOfMap V (h P) μ) : φ v ∈ weightSpaceOfMap W (h P) μ := fun a ↦ by
  rw [← LieModuleHom.map_lie, hv a, map_smul]

namespace VermaModule

/-- The maximal proper submodule `M'(Λ)` of `M(Λ)`: the sum of all submodules not containing
`v_Λ` ([Kac] §9.2). -/
def maxSubmodule : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ) :=
  sSup {N | hwv P Λ ∉ N}

/-- The sum of the weight spaces `M(Λ)_μ`, `μ ≠ Λ`. -/
abbrev lowerPart : Submodule K (VermaModule P Λ) := ⨆ (μ) (_ : μ ≠ Λ), weightSpace P Λ μ

lemma hwv_notMem_lowerPart : hwv P Λ ∉ lowerPart P Λ := fun hv ↦
  hwv_ne_zero P Λ (Submodule.disjoint_def.mp ((iSupIndep_weightSpaceOfMap (h P)) Λ) _
    (hwv_mem_weightSpace P Λ) hv)

lemma inf_weightSpace_self_eq_bot {N : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ)}
    (hN : hwv P Λ ∉ N) : N.toSubmodule ⊓ weightSpace P Λ Λ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxN, hx⟩
  rw [weightSpace_self] at hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  by_cases hc : c = 0
  · simp [hc]
  · exact absurd (by simpa [hc] using N.smul_mem c⁻¹ hxN) hN

/-- A Lie submodule of `M(Λ)` does not contain `v_Λ` iff it lies in the sum of the weight spaces
`M(Λ)_μ`, `μ ≠ Λ`. -/
theorem hwv_notMem_iff_le_lowerPart (N : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ)) :
    hwv P Λ ∉ N ↔ N.toSubmodule ≤ lowerPart P Λ := by
  refine ⟨fun hN ↦ ?_, fun hN hv ↦ hwv_notMem_lowerPart P Λ (hN hv)⟩
  have hle := inf_iSup_weightSpaceOfMap_le (h P) N.toSubmodule (fun a _ hm ↦ N.lie_mem hm)
    Set.univ
  have htop : ⨆ μ ∈ Set.univ, weightSpace P Λ μ = ⊤ := by
    rw [eq_top_iff, ← iSup_weightSpace_eq_top P Λ]
    exact iSup₂_le fun k _ ↦ le_biSup (fun μ ↦ weightSpace P Λ μ) (Set.mem_univ _)
  rw [htop, inf_top_eq] at hle
  refine hle.trans (iSup₂_le fun μ _ ↦ ?_)
  by_cases hμ : μ = Λ
  · subst hμ
    rw [inf_weightSpace_self_eq_bot P μ hN]
    exact bot_le
  · exact inf_le_right.trans (le_biSup (fun ν ↦ weightSpace P Λ ν) hμ)

/-- A Lie submodule of `M(Λ)` does not contain `v_Λ` iff its `Λ`-weight space is zero. -/
theorem hwv_notMem_iff_inf_weightSpace_eq_bot
    (N : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ)) :
    hwv P Λ ∉ N ↔ N.toSubmodule ⊓ weightSpace P Λ Λ = ⊥ := by
  refine ⟨inf_weightSpace_self_eq_bot P Λ, fun hN hv ↦ hwv_ne_zero P Λ ?_⟩
  rw [← Submodule.mem_bot K, ← hN]
  exact ⟨hv, hwv_mem_weightSpace P Λ⟩

lemma maxSubmodule_le_lowerPart : (maxSubmodule P Λ).toSubmodule ≤ lowerPart P Λ := by
  rw [maxSubmodule, LieSubmodule.sSup_toSubmodule]
  refine sSup_le ?_
  rintro _ ⟨N, hN, rfl⟩
  exact (hwv_notMem_iff_le_lowerPart P Λ N).mp hN

theorem hwv_notMem_maxSubmodule : hwv P Λ ∉ maxSubmodule P Λ :=
  (hwv_notMem_iff_le_lowerPart P Λ _).mpr (maxSubmodule_le_lowerPart P Λ)

theorem maxSubmodule_ne_top : maxSubmodule P Λ ≠ ⊤ := fun h ↦
  hwv_notMem_maxSubmodule P Λ (h ▸ LieSubmodule.mem_top _)

/-- A submodule of `M(Λ)` is proper iff it is contained in `M'(Λ)` ([Kac] §9.2). -/
theorem le_maxSubmodule_iff (N : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ)) :
    N ≤ maxSubmodule P Λ ↔ N ≠ ⊤ := by
  refine ⟨fun hN h ↦ maxSubmodule_ne_top P Λ (eq_top_iff.mpr (h ▸ hN)), fun hN ↦ ?_⟩
  exact le_sSup fun hv ↦ hN (eq_top_of_hwv_mem P Λ hv)

/-- `M'(Λ)` is a maximal proper submodule of `M(Λ)`. -/
theorem isCoatom_maxSubmodule : IsCoatom (maxSubmodule P Λ) :=
  ⟨maxSubmodule_ne_top P Λ, fun N hN ↦ by_contra fun h ↦
    hN.not_ge ((le_maxSubmodule_iff P Λ N).mpr h)⟩

/-- `M'(Λ)` is the unique maximal proper submodule of `M(Λ)` ([Kac] §9.2). -/
theorem eq_maxSubmodule_of_isCoatom {N : LieSubmodule K P.KacMoodyAlgebra (VermaModule P Λ)}
    (hN : IsCoatom N) : N = maxSubmodule P Λ :=
  ((hN.le_iff.mp ((le_maxSubmodule_iff P Λ N).mpr hN.1)).resolve_left
    (maxSubmodule_ne_top P Λ)).symm

omit [CharZero K] in
/-- The weights of a quotient of `M(Λ)` lie in `Λ - Q₊` ([Kac] §9.2). -/
theorem exists_eq_sub_of_mem_weightSpace {V : Type*} [AddCommGroup V] [Module K V]
    [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    {μ : Dual K H} {x : V} (hx : x ∈ weightSpaceOfMap V (h P) μ) (hx0 : x ≠ 0) :
    ∃ k : ι → ℤ, 0 ≤ k ∧ μ = Λ - P.rootOf k := by
  classical
  by_contra! hμ
  let S : Set (Dual K H) := {ν | ∃ k : ι → ℤ, 0 ≤ k ∧ ν = Λ - P.rootOf k}
  let N : Dual K H → Submodule K V := fun ν ↦ if ν ∈ S then weightSpaceOfMap V (h P) ν else ⊥
  have hN : ∀ ν, N ν ≤ weightSpaceOfMap V (h P) ν := fun ν ↦ by
    simp only [N]; split_ifs <;> simp
  obtain ⟨m, rfl⟩ := hφ x
  have hm : m ∈ ⨆ (k : ι → ℤ) (_ : 0 ≤ k), weightSpace P Λ (Λ - P.rootOf k) := by
    rw [iSup_weightSpace_eq_top]; trivial
  have hx' : φ m ∈ ⨆ ν, N ν := by
    have := Submodule.mem_map_of_mem (f := (φ : VermaModule P Λ →ₗ[K] V)) hm
    simp_rw [Submodule.map_iSup] at this
    refine (iSup₂_le fun k hk ↦ ?_ : _ ≤ ⨆ ν, N ν) this
    refine le_trans ?_ (le_iSup N (Λ - P.rootOf k))
    simp only [N, show Λ - P.rootOf k ∈ S from ⟨k, hk, rfl⟩, ite_true]
    rintro _ ⟨y, hy, rfl⟩
    exact map_mem_weightSpaceOfMap P φ hy
  have := mem_of_mem_iSup_of_le (h P) N hN hx hx'
  simp only [N, show μ ∉ S from fun ⟨k, hk, h⟩ ↦ hμ k hk h, ite_false,
    Submodule.mem_bot] at this
  exact hx0 this

end VermaModule

/-- The irreducible highest-weight module `L(Λ) = M(Λ)/M'(Λ)` ([Kac] §9.3). -/
abbrev IrreducibleModule : Type _ := VermaModule P Λ ⧸ VermaModule.maxSubmodule P Λ

namespace IrreducibleModule

/-- The highest-weight vector of `L(Λ)`, the image of `v_Λ`. -/
def hwv : IrreducibleModule P Λ :=
  LieSubmodule.Quotient.mk' _ (VermaModule.hwv P Λ)

theorem hwv_ne_zero : hwv P Λ ≠ 0 := by
  rw [hwv, ne_eq, LieSubmodule.Quotient.mk_eq_zero]
  exact VermaModule.hwv_notMem_maxSubmodule P Λ

omit [CharZero K] in
lemma hwv_mem_weightSpace : hwv P Λ ∈ weightSpaceOfMap (IrreducibleModule P Λ) (h P) Λ :=
  map_mem_weightSpaceOfMap P _ (VermaModule.hwv_mem_weightSpace P Λ)

instance : Nontrivial (IrreducibleModule P Λ) := ⟨⟨_, _, hwv_ne_zero P Λ⟩⟩

/-- `L(Λ)` is irreducible ([Kac] §9.3). -/
theorem isIrreducible : IsIrreducible K P.KacMoodyAlgebra (IrreducibleModule P Λ) := by
  refine IsIrreducible.mk fun N hN ↦ ?_
  set π' := LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P Λ)
  have hle : VermaModule.maxSubmodule P Λ ≤ N.comap π' := fun m hm ↦ by
    rw [LieSubmodule.mem_comap, (LieSubmodule.Quotient.mk_eq_zero _).mpr hm]
    exact N.zero_mem
  rcases (VermaModule.isCoatom_maxSubmodule P Λ).le_iff.mp hle with h | h
  · rw [eq_top_iff]
    intro q _
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ q
    have : m ∈ N.comap π' := h ▸ LieSubmodule.mem_top m
    exact this
  · refine absurd ?_ hN
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ q
    rw [LieSubmodule.mem_bot, LieSubmodule.Quotient.mk_eq_zero, ← h]
    exact hq

/-- `L(Λ) ≅ L(μ)` only if `Λ = μ` ([Kac] §9.3). -/
theorem eq_of_equiv {Λ μ : Dual K H}
    (e : IrreducibleModule P Λ ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P μ) : Λ = μ := by
  -- `Λ` is a weight of `L(μ)` and `μ` is a weight of `L(Λ)`
  obtain ⟨k, hk, hΛ⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P μ
    (LieSubmodule.Quotient.mk' _) (LieSubmodule.Quotient.surjective_mk' _)
    (map_mem_weightSpaceOfMap P e.toLieModuleHom (hwv_mem_weightSpace P Λ))
    (by simpa using hwv_ne_zero P Λ)
  obtain ⟨l, hl, hμ⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P Λ
    (LieSubmodule.Quotient.mk' _) (LieSubmodule.Quotient.surjective_mk' _)
    (map_mem_weightSpaceOfMap P e.symm.toLieModuleHom (hwv_mem_weightSpace P μ))
    (by simpa using hwv_ne_zero P μ)
  have h1 : P.rootOf k = μ - Λ := by rw [hΛ]; abel
  have h2 : P.rootOf l = Λ - μ := by rw [hμ]; abel
  have hkl : k + l = 0 := P.rootOf_injective (by rw [map_add, h1, h2, map_zero]; abel)
  have hk0 : k = 0 := by
    ext i
    have := congrFun hkl i
    have := hk i
    have := hl i
    simp only [Pi.add_apply, Pi.zero_apply] at *
    omega
  rw [hΛ, hk0, map_zero, sub_zero]

end IrreducibleModule

end Matrix.Realization.KacMoodyAlgebra

end
