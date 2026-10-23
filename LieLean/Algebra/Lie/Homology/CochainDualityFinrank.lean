/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.CochainDuality
import LieLean.Algebra.Lie.Homology.Weights
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dimensions of weight cohomology by duality with homology

In the setting of `LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_subsingleton_homology`
(an invariant pairing `B : N × X → K` identifying `N` with the weight functionals on `X`, with `L`
and `X` sums of weight spaces), the cochains of degree `k` and weight `μ` with values in `N` are
the dual of the chains of degree `k` and weight `-μ` with coefficients in `X`
(`LieModule.ChevalleyEilenberg.DerivAction.cochainPieceEquiv`), and under this identification
the codifferential is the transpose of the differential. Hence, when these chain spaces are
finite-dimensional, `dim H^k(L, N)_μ = dim H_k(L, X)_{-μ}`
(`LieModule.ChevalleyEilenberg.DerivAction.finrank_weightComplex_homology`).

## Main definitions

* `LieModule.ChevalleyEilenberg.DerivAction.chainPiece`: the chains of degree `k` and weight `ν`.
* `LieModule.ChevalleyEilenberg.DerivAction.cochainPiecePair`: the pairing of cochains of weight
  `μ` with chains of weight `-μ`.

## Main results

* `CategoryTheory.ShortComplex.finrank_homology_add_add`:
  `dim H(S) + rank f + rank g = dim S.X₂` for a short complex of vector spaces.
* `LieModule.ChevalleyEilenberg.DerivAction.finrank_weightComplex_homology`: the duality above.

## References

Elementary linear algebra (the transpose argument); this is the dimension form of the duality
used in Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
§6.6 and §6.15. The argument here is our own.
-/

open Module TensorProduct CategoryTheory

noncomputable section

namespace CategoryTheory.ShortComplex

variable {K : Type*} [Field K]

/-- `dim H(S) + rank f + rank g = dim S.X₂` for a short complex `S` of vector spaces with `S.X₂`
finite-dimensional. -/
theorem finrank_homology_add_add (S : ShortComplex (ModuleCat K)) [FiniteDimensional K S.X₂] :
    finrank K S.homology + finrank K (LinearMap.range S.f.hom) +
        finrank K (LinearMap.range S.g.hom) = finrank K S.X₂ := by
  have h₁ : finrank K S.homology =
      finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  have h₂ := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have h₃ : finrank K (LinearMap.range S.f.hom) =
      finrank K (LinearMap.range S.moduleCatToCycles) := by
    have e : (LinearMap.ker S.g.hom).subtype ∘ₗ S.moduleCatToCycles = S.f.hom :=
      LinearMap.ext fun _ ↦ rfl
    rw [← Submodule.finrank_map_subtype_eq, ← LinearMap.range_comp, e]
  have h₄ := LinearMap.finrank_range_add_finrank_ker S.g.hom
  omega

end CategoryTheory.ShortComplex

namespace LieModule.ChevalleyEilenberg.DerivAction

variable {K H L X N : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup X] [Module K X] [LieRingModule L X] [LieModule K L X] (ρ : DerivAction K H L X)
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N] (ρN : DerivAction K H L N)

/-! ### Chains of a given degree and weight -/

/-- The chains of degree `k` and weight `ν`. -/
def chainPiece (k : ℕ) (ν : Dual K H) : Submodule K (ExteriorAlgebra K L ⊗[K] X) :=
  chainsIn K L X k ⊓ ρ.chainWeightSpace ν

variable {ρ} in
lemma diff_mem_chainPiece {k : ℕ} {ν : Dual K H} {c : ExteriorAlgebra K L ⊗[K] X}
    (hc : c ∈ ρ.chainPiece (k + 1) ν) : diff K L X c ∈ ρ.chainPiece k ν :=
  ⟨diff_mem_chainsIn hc.1, ρ.diff_mem_chainWeightSpace hc.2⟩

/-- The differential `d : C_{k+1}(L, X)_ν → C_k(L, X)_ν`. -/
def diffPiece (k : ℕ) (ν : Dual K H) : ρ.chainPiece (k + 1) ν →ₗ[K] ρ.chainPiece k ν :=
  (diff K L X).restrict fun _ hc ↦ diff_mem_chainPiece hc

@[simp] lemma coe_diffPiece (k : ℕ) (ν : Dual K H) (c : ρ.chainPiece (k + 1) ν) :
    (ρ.diffPiece k ν c : ExteriorAlgebra K L ⊗[K] X) = diff K L X c := rfl

lemma map_diff_chainPiece (k : ℕ) (ν : Dual K H) :
    (ρ.chainPiece (k + 1) ν).map (diff K L X) =
      (LinearMap.range (ρ.diffPiece k ν)).map (ρ.chainPiece k ν).subtype := by
  have e : (ρ.chainPiece k ν).subtype ∘ₗ ρ.diffPiece k ν =
      diff K L X ∘ₗ (ρ.chainPiece (k + 1) ν).subtype := LinearMap.ext fun _ ↦ rfl
  rw [← LinearMap.range_comp, e, LinearMap.range_comp, Submodule.range_subtype]

variable (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤)
  (hX : ⨆ ν, Module.End.weightSpaceOf ρ.φ ν = ⊤)

include hL hX in
/-- The boundaries of weight `ν` are the differentials of the chains of weight `ν`. -/
lemma boundaries_inf_chainWeightSpace (k : ℕ) (ν : Dual K H) :
    boundaries K L X k ⊓ ρ.chainWeightSpace ν = (ρ.chainPiece (k + 1) ν).map (diff K L X) := by
  refine le_antisymm (fun b ⟨hb, hbw⟩ ↦ ?_)
    fun _ ⟨c, hc, hb⟩ ↦ hb ▸ ⟨⟨c, hc.1, rfl⟩, ρ.diff_mem_chainWeightSpace hc.2⟩
  have hT := ρ.iSup_chainWeightSpace hL hX
  obtain ⟨c, hc, rfl⟩ := hb
  -- the weight-`ν` component of `c`
  set Pr := Module.End.weightProj hT ν
  have hPr : ∀ c ∈ chainsIn K L X (k + 1),
      Pr c ∈ ρ.chainPiece (k + 1) ν ∧ Pr (diff K L X c) = diff K L X (Pr c) := by
    intro c hc
    rw [← ρ.iSup_inf_chainWeightSpace hL hX (chainsIn K L X (k + 1))
      (fun a _ hc ↦ ρ.θ_mem_chainsIn a hc)] at hc
    induction hc using Submodule.iSup_induction' with
    | mem γ c hc =>
      have hdc := ρ.diff_mem_chainWeightSpace hc.2
      by_cases hγ : γ = ν
      · subst hγ
        rw [Module.End.weightProj_of_mem hT hc.2, Module.End.weightProj_of_mem hT hdc]
        exact ⟨hc, rfl⟩
      · rw [Module.End.weightProj_of_mem_ne hT hγ hc.2,
          Module.End.weightProj_of_mem_ne hT hγ hdc, map_zero]
        exact ⟨zero_mem _, rfl⟩
    | zero => exact ⟨by rw [map_zero]; exact zero_mem _, by simp only [map_zero]⟩
    | add c c' _ _ h h' =>
      simp only [map_add]
      exact ⟨add_mem h.1 h'.1, by rw [h.2, h'.2]⟩
  obtain ⟨h₁, h₂⟩ := hPr c hc
  exact ⟨Pr c, h₁, by rw [← h₂, Module.End.weightProj_of_mem hT hbw]⟩

include hL hX in
/-- `dim H_k(L, X)_ν + rank(d : C_{k+1,ν} → C_{k,ν}) + rank(d|C_{k,ν}) = dim C_k(L, X)_ν`. -/
theorem finrank_homologyWeightSpace_add_add (k : ℕ) (ν : Dual K H)
    [FiniteDimensional K (ρ.chainPiece k ν)] :
    finrank K (ρ.homologyWeightSpace k ν) + finrank K (LinearMap.range (ρ.diffPiece k ν)) +
        finrank K ((ρ.chainPiece k ν).map (diff K L X)) = finrank K (ρ.chainPiece k ν) := by
  have hZ : cycles K L X k ⊓ ρ.chainWeightSpace ν =
      (LinearMap.ker ((diff K L X).domRestrict (ρ.chainPiece k ν))).map
        (ρ.chainPiece k ν).subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
    exact le_antisymm (fun c ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨⟨h₁, h₃⟩, h₂⟩)
      fun c ⟨⟨h₁, h₃⟩, h₂⟩ ↦ ⟨⟨h₁, h₂⟩, h₃⟩
  have : FiniteDimensional K ↥(cycles K L X k ⊓ ρ.chainWeightSpace ν) :=
    Submodule.finiteDimensional_of_le (fun c ⟨⟨h₁, _⟩, h₃⟩ ↦ ⟨h₁, h₃⟩ :
      cycles K L X k ⊓ ρ.chainWeightSpace ν ≤ ρ.chainPiece k ν)
  have h₁ := ρ.finrank_homologyWeightSpace_add k ν
  have h₂ : finrank K ↥(boundaries K L X k ⊓ ρ.chainWeightSpace ν) =
      finrank K (LinearMap.range (ρ.diffPiece k ν)) := by
    rw [ρ.boundaries_inf_chainWeightSpace hL hX, map_diff_chainPiece,
      Submodule.finrank_map_subtype_eq]
  have h₃ : finrank K ↥(cycles K L X k ⊓ ρ.chainWeightSpace ν) =
      finrank K (LinearMap.ker ((diff K L X).domRestrict (ρ.chainPiece k ν))) := by
    rw [hZ, Submodule.finrank_map_subtype_eq]
  let _ : AddCommGroup (ρ.chainPiece k ν) := Module.addCommMonoidToAddCommGroup K
  have h₄ := LinearMap.finrank_range_add_finrank_ker ((diff K L X).domRestrict (ρ.chainPiece k ν))
  rw [LinearMap.range_domRestrict] at h₄
  omega

/-! ### Cochains as functionals on chains -/

variable {B : N →ₗ[K] X →ₗ[K] K}

variable (B) in
/-- The pairing `f ↦ (t ↦ B(f t))` of cochains of degree `k` and weight `μ` with values in `N`
with chains of degree `k` and weight `-μ`. -/
def cochainPiecePair (k : ℕ) (μ : Dual K H) :
    ρN.cochainWeightSpace k μ →ₗ[K] Dual K (ρ.chainPiece k (-μ)) :=
  LinearMap.lcomp K K (ρ.chainPiece k (-μ)).subtype ∘ₗ cochainPair B ∘ₗ
    LinearMap.lcomp K N (degProj K L k) ∘ₗ (ρN.cochainWeightSpace k μ).subtype

omit [LieModule K L X] [LieModule K L N] in
lemma cochainPiecePair_apply (k : ℕ) (μ : Dual K H) (f : ρN.cochainWeightSpace k μ)
    (t : ρ.chainPiece k (-μ)) :
    ρ.cochainPiecePair ρN B k μ f t =
      cochainPair B ((f : Cochains K L N k) ∘ₗ degProj K L k) t := rfl

variable (hD : ∀ a, ρN.D a = ρ.D a)
  (hBφ : ∀ (a : H) (n : N) (m : X), B (ρN.φ a n) m = -B n (ρ.φ a m))
include hD hBφ

omit [LieModule K L X] [LieModule K L N] in
/-- A cochain of weight `μ` pairs to zero with the chains of weight `ν ≠ -μ`. -/
lemma cochainPair_eq_zero_of_ne {k : ℕ} {μ ν : Dual K H} (h : ν ≠ -μ) {f : Cochains K L N k}
    (hf : f ∈ ρN.cochainWeightSpace k μ) {t : ExteriorAlgebra K L ⊗[K] X}
    (ht : t ∈ ρ.chainPiece k ν) : cochainPair B (f ∘ₗ degProj K L k) t = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, ν a ≠ -μ a := by
    by_contra h'
    push Not at h'
    exact h (LinearMap.ext fun a ↦ (h' a).trans (LinearMap.neg_apply μ a).symm)
  have h1 := cochainPair_θ ρ ρN hD hBφ hf a ht.1
  rw [mem_chainWeightSpace.mp ht.2 a, map_smul, smul_eq_mul] at h1
  have h2 : (ν a - -μ a) * cochainPair B (f ∘ₗ degProj K L k) t = 0 := by
    rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

omit [LieModule K L X] [LieModule K L N] in
include hL hX in
/-- A cochain of weight `μ` pairing to zero with the chains of weight `-μ` pairs to zero with all
chains of its degree. -/
lemma cochainPair_eq_zero_of_chainPiece {k : ℕ} {μ : Dual K H} {f : Cochains K L N k}
    (hf : f ∈ ρN.cochainWeightSpace k μ)
    (h0 : ∀ t ∈ ρ.chainPiece k (-μ), cochainPair B (f ∘ₗ degProj K L k) t = 0)
    {t : ExteriorAlgebra K L ⊗[K] X} (ht : t ∈ chainsIn K L X k) :
    cochainPair B (f ∘ₗ degProj K L k) t = 0 := by
  rw [← ρ.iSup_inf_chainWeightSpace hL hX (chainsIn K L X k)
    (fun a _ hc ↦ ρ.θ_mem_chainsIn a hc)] at ht
  induction ht using Submodule.iSup_induction' with
  | mem ν t ht =>
    by_cases hν : ν = -μ
    · exact h0 t (hν ▸ ht)
    · exact ρ.cochainPair_eq_zero_of_ne ρN hD hBφ hν hf ht
  | zero => exact map_zero _
  | add t t' _ _ h h' => rw [map_add, h, h', add_zero]

variable (hinj : Function.Injective B)
  (hrep : ∀ (γ : Dual K H) (ψ : X →ₗ[K] K), (∀ a m, ψ (ρ.φ a m) = γ a * ψ m) →
    ψ ∈ LinearMap.range B)

omit [LieModule K L X] [LieModule K L N] in
include hL hX hinj hrep in
/-- The cochains of degree `k` and weight `μ` with values in `N` are the dual of the chains of
degree `k` and weight `-μ` with coefficients in `X`. -/
theorem bijective_cochainPiecePair (k : ℕ) (μ : Dual K H) :
    Function.Bijective (ρ.cochainPiecePair ρN B k μ) := by
  refine ⟨fun f f' hff' ↦ ?_, fun χ ↦ ?_⟩
  · rw [← sub_eq_zero, ← map_sub] at hff'
    rw [← sub_eq_zero]
    set g := f - f'
    refine Subtype.ext (LinearMap.ext fun ω ↦ hinj (LinearMap.ext fun m ↦ ?_))
    have := ρ.cochainPair_eq_zero_of_chainPiece ρN hL hX hD hBφ g.2
      (fun t ht ↦ LinearMap.congr_fun hff' ⟨t, ht⟩) (tmul_mem_chainsIn ω.2 m)
    rw [cochainPair_tmul, LinearMap.comp_apply, degProj_subtype] at this
    rw [this, ZeroMemClass.coe_zero, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
  · have hT := ρ.iSup_chainWeightSpace hL hX
    obtain ⟨χ', hχ'⟩ := LinearMap.exists_extend χ
    set Pr := Module.End.weightProj hT (-μ)
    obtain ⟨g, hg, hpair⟩ := exists_cochain_of_weight ρ ρN hD hBφ hinj hrep hL (k := k)
      (μ := μ) (χ' ∘ₗ Pr) fun a t ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Module.End.weightProj_comm hT,
          mem_chainWeightSpace.mp (Module.End.weightProj_mem hT _ t) a, map_smul, smul_eq_mul,
          LinearMap.neg_apply]
    refine ⟨⟨g, hg⟩, LinearMap.ext fun t ↦ ?_⟩
    rw [cochainPiecePair_apply, hpair _ t.2.1, LinearMap.comp_apply,
      Module.End.weightProj_of_mem hT t.2.2]
    exact LinearMap.congr_fun hχ' t

include hL hX hinj hrep in
/-- The identification of the cochains of degree `k` and weight `μ` with the dual of the chains
of degree `k` and weight `-μ`. -/
def cochainPieceEquiv (k : ℕ) (μ : Dual K H) :
    ρN.cochainWeightSpace k μ ≃ₗ[K] Dual K (ρ.chainPiece k (-μ)) :=
  LinearEquiv.ofBijective _ (ρ.bijective_cochainPiecePair ρN hL hX hD hBφ hinj hrep k μ)

omit hD hBφ in
/-- `B((δf)(t)) = B(f(dt))` on the chains of degree `k + 1`. -/
lemma cochainPair_δ (hB : ∀ (x : L) (n : N) (m : X), B ⁅x, n⁆ m = -B n ⁅x, m⁆) (k : ℕ)
    (f : Cochains K L N k) {t : ExteriorAlgebra K L ⊗[K] X} (ht : t ∈ chainsIn K L X (k + 1)) :
    cochainPair B (δ K L N k f ∘ₗ degProj K L (k + 1)) t =
      cochainPair B (f ∘ₗ degProj K L k) (diff K L X t) := by
  obtain ⟨s, rfl⟩ := ht
  rw [← cochainPair_cochainDiff hB]
  induction s with
  | tmul ω m =>
    rw [incl_tmul, cochainPair_tmul, cochainPair_tmul, LinearMap.comp_apply, degProj_subtype,
      δ_apply]
  | add s s' h h' => rw [map_add, map_add, map_add, h, h']

omit hD hBφ in
/-- The codifferential is the transpose of the differential. -/
lemma cochainPiecePair_δWeight (hB : ∀ (x : L) (n : N) (m : X), B ⁅x, n⁆ m = -B n ⁅x, m⁆)
    (k : ℕ) (μ : Dual K H) (f : ρN.cochainWeightSpace k μ) :
    ρ.cochainPiecePair ρN B (k + 1) μ (ρN.δWeight k μ f) =
      (ρ.diffPiece k (-μ)).dualMap (ρ.cochainPiecePair ρN B k μ f) := by
  refine LinearMap.ext fun t ↦ ?_
  rw [LinearMap.dualMap_apply, cochainPiecePair_apply, cochainPiecePair_apply, coe_diffPiece,
    coe_δWeight]
  exact cochainPair_δ hB k f t.2.1

include hL hX hinj hrep in
/-- **Dimension of weight cohomology by duality**: if the chains of weight `-μ` are
finite-dimensional in each degree, then `dim H^k(L, N)_μ = dim H_k(L, X)_{-μ}`. -/
theorem finrank_weightComplex_homology
    (hB : ∀ (x : L) (n : N) (m : X), B ⁅x, n⁆ m = -B n ⁅x, m⁆) {μ : Dual K H}
    (hfin : ∀ j, FiniteDimensional K (ρ.chainPiece j (-μ))) (k : ℕ) :
    finrank K ((ρN.weightComplex μ).homology k) = finrank K (ρ.homologyWeightSpace k (-μ)) := by
  set e := ρ.cochainPieceEquiv ρN hL hX hD hBφ hinj hrep
  -- `δ` is `e⁻¹ ∘ dᵀ ∘ e`
  have hδ : ∀ j, finrank K (LinearMap.range (ρN.δWeight j μ)) =
      finrank K (LinearMap.range (ρ.diffPiece j (-μ))) := fun j ↦ by
    have : ρN.δWeight j μ = (e (j + 1) μ).symm.toLinearMap ∘ₗ
        (ρ.diffPiece j (-μ)).dualMap ∘ₗ (e j μ).toLinearMap := by
      refine LinearMap.ext fun f ↦ (e (j + 1) μ).injective ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact ρ.cochainPiecePair_δWeight ρN hB j μ f
    rw [this, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      LinearEquiv.finrank_map_eq]
    let _ : AddCommGroup (ρ.chainPiece j (-μ)) := Module.addCommMonoidToAddCommGroup K
    let _ : AddCommGroup (ρ.chainPiece (j + 1) (-μ)) := Module.addCommMonoidToAddCommGroup K
    exact LinearMap.finrank_range_dualMap_eq_finrank_range (ρ.diffPiece j (-μ))
  have hX₂ : finrank K ((ρN.weightComplex μ).sc k).X₂ = finrank K (ρ.chainPiece k (-μ)) :=
    let _ : AddCommGroup (ρ.chainPiece k (-μ)) := Module.addCommMonoidToAddCommGroup K
    ((e k μ).finrank_eq).trans (Subspace.dual_finrank_eq)
  have : FiniteDimensional K ((ρN.weightComplex μ).sc k).X₂ :=
    let _ : AddCommGroup (ρ.chainPiece k (-μ)) := Module.addCommMonoidToAddCommGroup K
    LinearEquiv.finiteDimensional (e k μ).symm
  have hS := ((ρN.weightComplex μ).sc k).finrank_homology_add_add
  have hC := ρ.finrank_homologyWeightSpace_add_add hL hX k (-μ)
  have hg : finrank K (LinearMap.range ((ρN.weightComplex μ).sc k).g.hom) =
      finrank K (LinearMap.range (ρ.diffPiece k (-μ))) := by
    change finrank K (LinearMap.range
      ((ρN.weightComplex μ).d k ((ComplexShape.up ℕ).next k)).hom) = _
    rw [CochainComplex.next, weightComplex_d]
    exact hδ k
  have hf : finrank K (LinearMap.range ((ρN.weightComplex μ).sc k).f.hom) =
      finrank K ((ρ.chainPiece k (-μ)).map (diff K L X)) := by
    cases k with
    | zero =>
      have h0 : (ρ.chainPiece 0 (-μ)).map (diff K L X) = ⊥ :=
        le_bot_iff.mp (Submodule.map_le_iff_le_comap.mpr fun c hc ↦
          diff_eq_zero_of_mem_chainsIn_zero hc.1)
      change finrank K (LinearMap.range
        ((ρN.weightComplex μ).d ((ComplexShape.up ℕ).prev 0) 0).hom) = _
      rw [h0, finrank_bot, CochainComplex.prev_nat_zero,
        (ρN.weightComplex μ).shape 0 0 (by simp), ModuleCat.hom_zero, LinearMap.range_zero,
        finrank_bot]
    | succ j =>
      change finrank K (LinearMap.range
        ((ρN.weightComplex μ).d ((ComplexShape.up ℕ).prev (j + 1)) (j + 1)).hom) = _
      rw [map_diff_chainPiece, Submodule.finrank_map_subtype_eq, CochainComplex.prev_nat_succ,
        weightComplex_d]
      exact hδ j
  change finrank K ((ρN.weightComplex μ).sc k).homology = _
  omega

end LieModule.ChevalleyEilenberg.DerivAction
