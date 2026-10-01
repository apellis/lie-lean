/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationFacet
import LieLean.Algebra.Lie.KacMoody.FiniteDimensional
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The dual of a finite-dimensional simple module

For `A` of finite type and `ν` dominant integral, the contragredient dual `L(ν)^*` (the module
`Module.Dual K L(ν)` with `⁅x, f⁆ = -f ∘ x`) is isomorphic to `L(ν*)`, where `ν* = z(-ν)` is the
dominant integral weight in the Weyl orbit of `-ν` (so `ν* = -w₀ν`, `w₀` the longest element;
Humphreys, GSM 94, §7.2 (check); Humphreys, GTM 9, §21 Exercise (check)).

## Main results

* `LieModule.dualEquiv`, `LieModule.evalEquiv`: functoriality of the dual and the double-dual
  isomorphism, as equivalences of Lie modules.
* `LieModule.isIrreducible_dual`: the dual of a finite-dimensional irreducible module is
  irreducible.
* `IrreducibleModule.exists_norm_eq_add`: for a weight `μ` of `L(Λ)`, `|Λ|² = |μ|² + n` with
  `n ∈ ℕ`, and `n = 0` only if `μ ∈ W Λ` (for the positive definite form of finite type).
* `IrreducibleModule.exists_equiv_dual`: `L(ν)^* ≅ L(z(-ν))` with `z ∈ W`, `z(-ν)` dominant.

The argument (reconstructed): `L(ν)^*` is irreducible and finite-dimensional, so it is some
`L(Λ)` by Weyl's theorem. Weights of a dual are negatives of weights, so `-Λ` is a weight of
`L(ν)` and `-ν` a weight of `L(Λ)`; the norm inequality in both directions forces equality, hence
`-ν ∈ W Λ`. The longest element `w₀` is not used.
-/

noncomputable section

open Module

namespace LieModule

section Dual

variable {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- The dual of an equivalence of Lie modules, `f ↦ f ∘ e`. -/
def dualEquiv (e : M ≃ₗ⁅R,L⁆ N) : Module.Dual R N ≃ₗ⁅R,L⁆ Module.Dual R M where
  toFun f := f ∘ₗ e.toLinearEquiv.toLinearMap
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  map_lie' {x f} := by
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, Module.Dual.lie_apply]
    exact congrArg (fun y ↦ -f y) (e.toLieModuleHom.map_lie x m).symm
  invFun f := f ∘ₗ e.symm.toLinearEquiv.toLinearMap
  left_inv f := by ext; simp
  right_inv f := by ext; simp

@[simp] lemma dualEquiv_apply (e : M ≃ₗ⁅R,L⁆ N) (f : Module.Dual R N) (m : M) :
    dualEquiv e f m = f (e m) := rfl

end Dual

section Field

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- The double-dual isomorphism `M ≅ M^{**}` of a finite-dimensional Lie module. -/
def evalEquiv [FiniteDimensional K M] : M ≃ₗ⁅K,L⁆ Module.Dual K (Module.Dual K M) :=
  LieModuleEquiv.ofBijective
    { toLinearMap := (Module.evalEquiv K M).toLinearMap
      map_lie' := fun {x m} ↦ by
        ext f
        simp [Module.Dual.lie_apply] }
    (Module.evalEquiv K M).bijective

@[simp] lemma evalEquiv_apply [FiniteDimensional K M] (m : M) (f : Module.Dual K M) :
    evalEquiv (L := L) m f = f m := rfl

/-- The dual of a finite-dimensional irreducible Lie module is irreducible. -/
theorem isIrreducible_dual [FiniteDimensional K M] [IsIrreducible K L M] :
    IsIrreducible K L (Module.Dual K M) := by
  have : Nontrivial M := nontrivial_of_isIrreducible K L M
  have : Nontrivial (Module.Dual K M) := Module.nontrivial_of_finrank_pos
    (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_pos)
  refine IsIrreducible.mk fun N hN ↦ ?_
  let C : LieSubmodule K L M :=
    { toSubmodule := N.toSubmodule.dualCoannihilator
      lie_mem := fun {x v} hv ↦ by
        change v ∈ N.toSubmodule.dualCoannihilator at hv
        change ⁅x, v⁆ ∈ N.toSubmodule.dualCoannihilator
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have := hv _ (N.lie_mem (x := x) hf)
        rwa [Module.Dual.lie_apply, neg_eq_zero] at this }
  rcases IsSimpleOrder.eq_bot_or_eq_top C with hC | hC
  · have hC' : N.toSubmodule.dualCoannihilator = ⊥ := congrArg LieSubmodule.toSubmodule hC
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := N.toSubmodule)
    rw [hC', Submodule.dualAnnihilator_bot] at this
    exact LieSubmodule.toSubmodule_injective (by rw [← this]; rfl)
  · refine absurd ?_ hN
    rw [eq_bot_iff]
    intro f hf
    rw [LieSubmodule.mem_bot]
    ext v
    have hv : v ∈ C := hC ▸ LieSubmodule.mem_top v
    exact (Submodule.mem_dualCoannihilator v).mp hv f hf

end Field

end LieModule

namespace Matrix.Realization.KacMoodyAlgebra

open LieModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V W : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]
  [AddCommGroup W] [Module K W] [LieRingModule P.KacMoodyAlgebra W]
  [LieModule K P.KacMoodyAlgebra W]

omit [CharZero K] in
/-- Equivalent modules have the same weights. -/
theorem weightSpaceOfMap_ne_bot_of_equiv (e : V ≃ₗ⁅K,P.KacMoodyAlgebra⁆ W) {μ : Dual K H}
    (hμ : weightSpaceOfMap V (h P) μ ≠ ⊥) : weightSpaceOfMap W (h P) μ ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  refine fun hbot ↦ hx0 (e.injective ?_)
  have := map_mem_weightSpaceOfMap P e.toLieModuleHom hx
  rw [hbot, Submodule.mem_bot] at this
  rw [map_zero]
  exact this

omit [CharZero K] in
/-- The weights of a dual are the negatives of weights: if `V` is spanned by weight vectors and
`V^*` has a nonzero vector of weight `μ`, then `-μ` is a weight of `V`. -/
theorem weightSpaceOfMap_neg_ne_bot_of_dual (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    {μ : Dual K H} (hμ : weightSpaceOfMap (Module.Dual K V) (h P) μ ≠ ⊥) :
    weightSpaceOfMap V (h P) (-μ) ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  intro hbot
  refine hf0 (LinearMap.ext fun v ↦ ?_)
  have hv : v ∈ ⨆ κ, weightSpaceOfMap V (h P) κ := hV ▸ Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem κ v hv =>
    by_cases hκ : κ = -μ
    · subst hκ
      rw [hbot, Submodule.mem_bot] at hv
      simp [hv]
    · obtain ⟨a, ha⟩ : ∃ a, κ a ≠ (-μ) a := by
        by_contra hc
        push Not at hc
        exact hκ (LinearMap.ext hc)
      have h1 := congrArg (fun g : Module.Dual K V ↦ g v) (hf a)
      simp only [Module.Dual.lie_apply, hv a, map_smul, LinearMap.smul_apply,
        smul_eq_mul] at h1
      have h2 : (κ a - (-μ) a) * f v = 0 := by
        rw [LinearMap.neg_apply]
        linear_combination -h1
      rw [LinearMap.zero_apply]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]

section FiniteType

variable [FiniteDimensional K H] (hA : A.IsFiniteCartan)

open IrreducibleModule in
include hA in
/-- **Norm of weights**: for the positive definite form `B` of finite type (symmetrization
`diag(d) A`) and a weight `μ` of `L(Λ)`, `Λ` dominant integral, `B(Λ,Λ) = B(μ,μ) + n` with
`n ∈ ℕ`, and `n = 0` only if `μ ∈ W Λ`. Reconstructed; all comparisons are made in `ℤ`. -/
theorem IrreducibleModule.exists_norm_eq_add {d : ι → ℤ} (hd : ∀ i, 0 < d i)
    (hsymm : (diagonal d * A).IsSymm) (hpos : (diagonal d * A).PosDef) {Λ : Dual K H}
    (hΛ : P.IsDominantIntegral Λ) {μ : Dual K H}
    (hμ : weightSpace P (IrreducibleModule P Λ) μ ≠ ⊥) :
    ∃ n : ℕ, P.dualBilinForm (Symmetrization.ofDiagonal d hd hsymm) Λ Λ =
        P.dualBilinForm (Symmetrization.ofDiagonal d hd hsymm) μ μ + n ∧
      (n = 0 → ∃ w ∈ P.weylGroup hA.isGeneralizedCartan, μ = w Λ) := by
  classical
  have hA' := hA.isGeneralizedCartan
  have := P.finite_weylGroup hA
  set S := Symmetrization.ofDiagonal d hd hsymm
  set B := P.dualBilinForm S
  have hB (k : ι → ℤ) (x : Dual K H) := P.dualBilinForm_ofDiagonal_rootOf d hd hsymm k x
  have hBsymm (x x' : Dual K H) : B x x' = B x' x := (P.isSymm_dualBilinForm S).eq x x'
  have hμint : ∀ i, ∃ n : ℤ, μ (P.coroot i) = n := by
    obtain ⟨k, -, hk⟩ := exists_eq_sub_of_weightSpace_ne_bot (P := P) hμ
    intro i
    obtain ⟨n, hn⟩ := hΛ i
    refine ⟨n - (A *ᵥ k) i, ?_⟩
    rw [hk, LinearMap.sub_apply, hn, rootOf_apply_coroot]
    push_cast
    ring
  obtain ⟨u, hu⟩ := P.exists_dominantIntegral_weylGroup hA' hμint
  have hD : weightSpace P (IrreducibleModule P Λ) (u.val μ) ≠ ⊥ :=
    weightSpace_apply_ne_bot hA' hΛ u.property hμ
  obtain ⟨c, hc, hcD⟩ := exists_eq_sub_of_weightSpace_ne_bot (P := P) hD
  choose m hm using hu
  set Q : ℤ := c ⬝ᵥ (diagonal d * A) *ᵥ c with hQdef
  have hQ0 : 0 ≤ Q := by
    by_cases hc0 : c = 0
    · simp [hQdef, hc0]
    · have := hpos.dotProduct_mulVec_pos hc0
      simp only [star_trivial] at this
      exact this.le
  set N : ℤ := ∑ i, 2 * (c i * d i * m i) + Q with hNdef
  have hS0 : 0 ≤ ∑ i, 2 * (c i * d i * m i) := Finset.sum_nonneg fun i _ ↦ by
    have := mul_nonneg (hc i) (hd i).le
    positivity
  have hN0 : 0 ≤ N := add_nonneg hS0 hQ0
  have hBq : B (P.rootOf c) (P.rootOf c) = (Q : K) := by
    rw [hB, hQdef, ← mulVec_mulVec, dotProduct]
    simp only [mulVec_diagonal]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rootOf_apply_coroot]
    ring
  have hBD : B (P.rootOf c) (u.val μ) = ∑ i, ((c i * d i * m i : ℤ) : K) := by
    rw [hB]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hm i]
    push_cast
    ring
  have hΛD : Λ = u.val μ + P.rootOf c := by rw [hcD]; abel
  have hnorm : B Λ Λ = B μ μ + (N : K) := by
    have hW : B (u.val μ) (u.val μ) = B μ μ :=
      P.dualBilinForm_weylGroup hA' S u.property μ μ
    rw [hΛD]
    simp only [map_add, LinearMap.add_apply]
    rw [hBsymm (u.val μ) (P.rootOf c), hBD, hBq, hW, hNdef]
    push_cast
    rw [← Finset.mul_sum]
    ring
  refine ⟨N.toNat, ?_, fun hn ↦ ?_⟩
  · rw [hnorm]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hN0).symm
  · have hN : N = 0 := by omega
    have hQ : Q = 0 := by
      have : ∑ i, 2 * (c i * d i * m i) + Q = 0 := hN
      omega
    have hc0 : c = 0 := by
      by_contra hne
      have := hpos.dotProduct_mulVec_pos hne
      simp only [star_trivial] at this
      omega
    refine ⟨(u⁻¹ : P.weylGroup hA').val, (u⁻¹).property, ?_⟩
    rw [hΛD, hc0, map_zero, add_zero]
    change μ = u.val.symm (u.val μ)
    exact (u.val.symm_apply_apply μ).symm

include hA in
/-- **The dual of `L(ν)`** (finite type; Humphreys, GSM 94, §7.2 (check)): for `ν` dominant
integral there is `z ∈ W` with `z(-ν)` dominant integral and `L(ν)^* ≅ L(z(-ν))`. The weight
`z(-ν)` is the dominant weight of the orbit `W(-ν)`, i.e. `-w₀ν`. -/
theorem IrreducibleModule.exists_equiv_dual {ν : Dual K H} (hν : P.IsDominantIntegral ν) :
    ∃ z ∈ P.weylGroup hA.isGeneralizedCartan, P.IsDominantIntegral (z (-ν)) ∧
      Nonempty (Module.Dual K (IrreducibleModule P ν) ≃ₗ⁅K,P.KacMoodyAlgebra⁆
        IrreducibleModule P (z (-ν))) := by
  classical
  have hA' := hA.isGeneralizedCartan
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  have := IrreducibleModule.isIrreducible P ν
  have hirr : IsIrreducible K P.KacMoodyAlgebra (Module.Dual K (IrreducibleModule P ν)) :=
    isIrreducible_dual
  have : Nontrivial (Module.Dual K (IrreducibleModule P ν)) :=
    nontrivial_of_isIrreducible K P.KacMoodyAlgebra _
  -- Weyl's theorem: the dual is some `L(Λ)`.
  obtain ⟨s, hs, hsL⟩ := exists_isInternal_irreducibleModule_of_finiteDimensional (P := P)
    (Module.Dual K (IrreducibleModule P ν)) hA
  obtain ⟨N, hNs, hN⟩ : ∃ N ∈ s, N ≠ ⊥ := by
    by_contra hc
    push Not at hc
    have htop := hs.submodule_iSup_eq_top
    have hbot : ⨆ N : s, (N : Submodule K (Module.Dual K (IrreducibleModule P ν))) = ⊥ :=
      iSup_eq_bot.mpr fun N ↦ by rw [hc N N.property]; rfl
    rw [hbot] at htop
    exact bot_ne_top htop
  obtain ⟨Λ, hΛ, ⟨e₀⟩⟩ := hsL N hNs
  have hNtop : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
  let eN : N ≃ₗ⁅K,P.KacMoodyAlgebra⁆ Module.Dual K (IrreducibleModule P ν) :=
    LieModuleEquiv.ofBijective N.incl
      ⟨Subtype.val_injective, fun f ↦ ⟨⟨f, hNtop ▸ LieSubmodule.mem_top f⟩, rfl⟩⟩
  let e : Module.Dual K (IrreducibleModule P ν) ≃ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ :=
    eN.symm.trans e₀
  -- `-Λ` is a weight of `L(ν)` and `-ν` is a weight of `L(Λ)`.
  have h1 : weightSpace P (IrreducibleModule P ν) (-Λ) ≠ ⊥ :=
    weightSpaceOfMap_neg_ne_bot_of_dual P (IrreducibleModule.isCategoryO P ν).1
      (weightSpaceOfMap_ne_bot_of_equiv P e.symm (weightSpace_self_ne_bot (P := P) Λ))
  have h2 : weightSpace P (IrreducibleModule P Λ) (-ν) ≠ ⊥ :=
    weightSpaceOfMap_neg_ne_bot_of_dual P (IrreducibleModule.isCategoryO P Λ).1
      (weightSpaceOfMap_ne_bot_of_equiv P (evalEquiv.trans (dualEquiv e).symm)
        (weightSpace_self_ne_bot (P := P) ν))
  -- The norm argument.
  obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  set B := P.dualBilinForm (Symmetrization.ofDiagonal d hdpos hsymm)
  have hneg (x : Dual K H) : B (-x) (-x) = B x x := by simp
  obtain ⟨n₁, hn₁, -⟩ := IrreducibleModule.exists_norm_eq_add P hA hdpos hsymm hpos hν h1
  obtain ⟨n₂, hn₂, hn₂0⟩ := IrreducibleModule.exists_norm_eq_add P hA hdpos hsymm hpos hΛ h2
  rw [hneg] at hn₁ hn₂
  have hsum : ((n₁ + n₂ : ℕ) : K) = 0 := by
    push_cast
    linear_combination -hn₁ - hn₂
  have hn : n₁ + n₂ = 0 := by exact_mod_cast hsum
  obtain ⟨w, hw, hwΛ⟩ := hn₂0 (by omega)
  have hz : w⁻¹ ∈ P.weylGroup hA' := inv_mem hw
  have hzν : w⁻¹ (-ν) = Λ := by
    rw [hwΛ]
    change w.symm (w Λ) = Λ
    exact w.symm_apply_apply Λ
  exact ⟨w⁻¹, hz, hzν ▸ hΛ, ⟨hzν ▸ e⟩⟩

end FiniteType

end Matrix.Realization.KacMoodyAlgebra
