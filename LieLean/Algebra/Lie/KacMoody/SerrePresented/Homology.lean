/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.ChevalleyEilenberg
import LieLean.Algebra.Lie.KacMoody.SerrePresented

/-!
# A lowest weight vector of `𝔯̂₋` gives a nontrivial class in `H₂(𝔫₋)`

Let `A` be a generalized Cartan matrix, `K` a field of characteristic zero, `𝔤̂ = 𝔤̂(A)` the
Serre-presented algebra, `𝔫̂₋ ⊆ 𝔤̂` and `𝔫₋ ⊆ 𝔤(A)` the negative nilpotent subalgebras, and
`𝔯̂₋ = 𝔯̂ ∩ 𝔫̂₋` the kernel of the projection `𝔫̂₋ → 𝔫₋`. This file contains the homological step of
the proof of the Gabber–Kac theorem ([Kac] Thm. 9.11, [GK]):

Let `x ∈ 𝔯̂₋` be a nonzero weight vector of weight `-β`, `β ∈ Q₊ \ {0}`, such that `𝔯̂₋` has no
nonzero weight vectors of weight `-γ` with `ht γ < ht β`. Then there is a two-cycle
`z ∈ (⋀²𝔫₋)_{-β}` of the Chevalley–Eilenberg complex of `𝔫₋` which is not a boundary; that is,
`H₂(𝔫₋)_{-β} ≠ 0`.

The argument (reconstructed; it is the five-term exact sequence
`H₂(𝔫̂₋) → H₂(𝔫₋) → 𝔯̂₋/[𝔫̂₋, 𝔯̂₋] → H₁(𝔫̂₋) → H₁(𝔫₋) → 0` of the extension
`0 → 𝔯̂₋ → 𝔫̂₋ → 𝔫₋ → 0`, made explicit):

* `β` is not a simple root, since `𝔯̂ ∩ 𝔤̂_{-αᵢ} = 𝔯̂ ∩ K fᵢ = 0`. As `𝔫̂₋` is spanned by the `fᵢ`
  and `[𝔫̂₋, 𝔫̂₋]`, we get `x = ∑ₖ [aₖ, bₖ]` with `aₖ, bₖ ∈ 𝔫̂₋` weight vectors whose weights add
  up to `-β`.
* Put `t = -∑ₖ aₖ ∧ bₖ ∈ ⋀²𝔫̂₋`, so `∂₂ t = x`, and let `z ∈ ⋀²𝔫₋` be its image. Then
  `∂₂ z = π(x) = 0`, and `z` has weight `-β`.
* If `z` were a boundary, then `x ∈ [𝔫̂₋, 𝔯̂₋]`
  (`LieAlgebra.ChevalleyEilenberg.d₂_mem_lie_ker_of_map_mem_range_d₃`), so `x` would be a sum of
  brackets `[a, r]` of weight vectors `a ∈ 𝔫̂₋`, `r ∈ 𝔯̂₋` whose weights add up to `-β`; by
  minimality every such `r` vanishes, so `x = 0`.

## Main definitions

* `Matrix.Realization.SerrePresentedAlgebra.negProj`: the surjection `𝔫̂₋ → 𝔫₋`.
* `Matrix.Realization.KacMoodyAlgebra.wedgeWeightSpace`: the weight space `(⋀²𝔫₋)_ν`, spanned
  by the `a ∧ b` with `a, b ∈ 𝔫₋` weight vectors whose weights add up to `ν`.
* `LieModule.lieWeightSpan`: the span of brackets of weight vectors with prescribed weights.

## Main results

* `Matrix.Realization.SerrePresentedAlgebra.exists_cycle_not_boundary`: the statement above.
* `Matrix.Realization.SerrePresentedAlgebra.radicalNeg_inf_rootSpace_eq_bot`: contrapositive
  form: if all two-cycles of `⋀²𝔫₋` of weight `-β` are boundaries and `𝔯̂₋` vanishes in weights
  of smaller height, then `𝔯̂₋` vanishes in weight `-β`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.11 (check).
* [GK] O. Gabber, V. G. Kac, *On defining relations of certain infinite-dimensional Lie
  algebras*, Bull. Amer. Math. Soc. (N.S.) **5** (1981), 185–189.
-/

open FreeLieAlgebra Module LieModule LieAlgebra LieAlgebra.ChevalleyEilenberg

noncomputable section

/-! ### Brackets of weight vectors -/

namespace LieModule

variable {K H L : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  (φ : H →ₗ[K] L)

/-- The span of the brackets `[a, b]` with `a ∈ A ∩ L_μ`, `b ∈ B ∩ L_{μ'}`, `μ ∈ S`, `μ' ∈ T` and
`μ + μ' = ν`. -/
def lieWeightSpan (A B : Submodule K L) (S T : Set (Dual K H)) (ν : Dual K H) :
    Submodule K L :=
  Submodule.span K {x | ∃ a b, (∃ μ ∈ S, ∃ μ' ∈ T, μ + μ' = ν ∧
    a ∈ A ⊓ weightSpaceOfMap L φ μ ∧ b ∈ B ⊓ weightSpaceOfMap L φ μ') ∧ x = ⁅a, b⁆}

lemma lieWeightSpan_le (A B : Submodule K L) (S T : Set (Dual K H)) (ν : Dual K H) :
    lieWeightSpan φ A B S T ν ≤ weightSpaceOfMap L φ ν := by
  rw [lieWeightSpan, Submodule.span_le]
  rintro _ ⟨a, b, ⟨μ, -, μ', -, rfl, ⟨-, ha⟩, ⟨-, hb⟩⟩, rfl⟩
  exact lie_mem_weightSpaceOfMap φ ha hb

/-- If `A`, `B` are `φ(H)`-stable and contained in the sums of the weight spaces `L_μ`, `μ ∈ S`,
resp. `μ ∈ T`, then `[A, B]` is contained in the sum of the `lieWeightSpan φ A B S T ν`. -/
theorem span_lie_le_iSup_lieWeightSpan {A B : Submodule K L}
    (hA : ∀ a, ∀ x ∈ A, ⁅φ a, x⁆ ∈ A) (hB : ∀ a, ∀ x ∈ B, ⁅φ a, x⁆ ∈ B)
    {S T : Set (Dual K H)} (hAS : A ≤ ⨆ μ ∈ S, weightSpaceOfMap L φ μ)
    (hBT : B ≤ ⨆ μ ∈ T, weightSpaceOfMap L φ μ) :
    Submodule.span K {x | ∃ a b, (a ∈ A ∧ b ∈ B) ∧ x = ⁅a, b⁆} ≤
      ⨆ ν, lieWeightSpan φ A B S T ν := by
  rw [Submodule.span_le]
  rintro _ ⟨a, b, ⟨ha, hb⟩, rfl⟩
  have ha' : a ∈ ⨆ μ ∈ S, (A ⊓ weightSpaceOfMap L φ μ) :=
    inf_iSup_weightSpaceOfMap_le φ A hA S ⟨ha, hAS ha⟩
  have hb' : b ∈ ⨆ μ ∈ T, (B ⊓ weightSpaceOfMap L φ μ) :=
    inf_iSup_weightSpaceOfMap_le φ B hB T ⟨hb, hBT hb⟩
  rw [← iSup_subtype''] at ha' hb'
  refine Submodule.iSup_induction _ (motive := fun a ↦ ⁅a, b⁆ ∈ _) ha' (fun μ a ha ↦ ?_)
    (by simp) (fun a₁ a₂ h₁ h₂ ↦ by rw [add_lie]; exact Submodule.add_mem _ h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun b ↦ ⁅a, b⁆ ∈ _) hb' (fun μ' b hb ↦ ?_)
    (by simp) (fun b₁ b₂ h₁ h₂ ↦ by rw [lie_add]; exact Submodule.add_mem _ h₁ h₂)
  exact Submodule.mem_iSup_of_mem ((μ : Dual K H) + μ')
    (Submodule.subset_span ⟨a, b, ⟨μ, μ.2, μ', μ'.2, rfl, ha, hb⟩, rfl⟩)

/-- A weight vector of weight `ν` in `[A, B]` lies in `lieWeightSpan φ A B S T ν`. -/
theorem mem_lieWeightSpan_of_mem {A B : Submodule K L}
    (hA : ∀ a, ∀ x ∈ A, ⁅φ a, x⁆ ∈ A) (hB : ∀ a, ∀ x ∈ B, ⁅φ a, x⁆ ∈ B)
    {S T : Set (Dual K H)} (hAS : A ≤ ⨆ μ ∈ S, weightSpaceOfMap L φ μ)
    (hBT : B ≤ ⨆ μ ∈ T, weightSpaceOfMap L φ μ) {ν : Dual K H} {x : L}
    (hx : x ∈ Submodule.span K {x | ∃ a b, (a ∈ A ∧ b ∈ B) ∧ x = ⁅a, b⁆})
    (hxν : x ∈ weightSpaceOfMap L φ ν) : x ∈ lieWeightSpan φ A B S T ν :=
  mem_of_mem_iSup_of_le φ _ (lieWeightSpan_le φ A B S T) hxν
    (span_lie_le_iSup_lieWeightSpan φ hA hB hAS hBT hx)

end LieModule

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

omit [DecidableEq ι] in
lemma height_add (k l : ι → ℤ) : height (k + l) = height k + height l := by
  simp [height, Finset.sum_add_distrib]

omit [DecidableEq ι] in
lemma height_pos {k : ι → ℤ} (hk : k ∈ posCone ι) : 0 < height k := by
  obtain ⟨hk0, hk⟩ := hk
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra! h; exact hk (funext h)
  exact Finset.sum_pos' (fun j _ ↦ hk0 j) ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hk0 i) hi.symm⟩

/-! ### The weight spaces of `⋀²𝔫₋` -/

namespace KacMoodyAlgebra

/-- The weight space `(⋀²𝔫₋)_ν`: the span of the `a ∧ b` with `a, b ∈ 𝔫₋` weight vectors whose
weights add up to `ν`. -/
def wedgeWeightSpace (ν : Dual K H) : Submodule K (⋀[K]^2 (fHom P).range) :=
  Submodule.span K {t | ∃ a b : (fHom P).range, (∃ μ μ', μ + μ' = ν ∧
    (a : P.KacMoodyAlgebra) ∈ rootSpace P μ ∧ (b : P.KacMoodyAlgebra) ∈ rootSpace P μ') ∧
      t = wedge₂ K _ a b}

end KacMoodyAlgebra

namespace SerrePresentedAlgebra

/-! ### The subalgebra `𝔫̂₋` and the projection `𝔫̂₋ → 𝔫₋` -/

lemma lie_h_mem_range_fHom (a : H) {x : P.SerrePresentedAlgebra}
    (hx : x ∈ LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra)) :
    ⁅h P a, x⁆ ∈ LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', hy'⟩ := AuxLieAlgebra.lie_h_fHom P a y
  refine ⟨y', ?_⟩
  change π P (AuxLieAlgebra.fHom P y') = ⁅π P (AuxLieAlgebra.h P a), π P (AuxLieAlgebra.fHom P y)⁆
  rw [← LieHom.map_lie, hy']

lemma range_fHom_le :
    LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) ≤
      ⨆ μ ∈ P.negWeights, rootSpace P μ := by
  rintro _ ⟨y, rfl⟩; exact fHom_mem P y

/-- `𝔫̂₋` is spanned by the `fᵢ` and `[𝔫̂₋, 𝔫̂₋]`; more precisely, it is contained in the sum over
`ν` of the span of the `fᵢ` with `-αᵢ = ν` and of the brackets of weight vectors of `𝔫̂₋` of
total weight `ν`. -/
lemma range_fHom_le_iSup :
    LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) ≤
      ⨆ ν, (Submodule.span K (f P '' {i | -P.root i = ν}) ⊔
        lieWeightSpan (h P)
          (LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra))
          (LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra))
          P.negWeights P.negWeights ν) := by
  rintro _ ⟨y, rfl⟩
  induction y using FreeLieAlgebra.induction_on with
  | of i =>
    refine Submodule.mem_iSup_of_mem (-P.root i) (Submodule.mem_sup_left ?_)
    exact Submodule.subset_span ⟨i, rfl, by simp⟩
  | zero => simp
  | add y z hy hz => simpa using Submodule.add_mem _ hy hz
  | smul c y hy => simpa using Submodule.smul_mem _ c hy
  | lie y z _ _ =>
    have := span_lie_le_iSup_lieWeightSpan (h P)
      (fun a x hx ↦ lie_h_mem_range_fHom P a hx) (fun a x hx ↦ lie_h_mem_range_fHom P a hx)
      (range_fHom_le P) (range_fHom_le P)
      (Submodule.subset_span ⟨fHom P y, fHom P z, ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩, rfl⟩)
    simp only [LieHom.coe_toLinearMap, LieHom.map_lie]
    exact SetLike.le_def.mp (iSup_mono fun ν ↦ le_sup_right) this

variable [CharZero K] (hA : A.IsGeneralizedCartan)

/-- The projection `𝔫̂₋ → 𝔫₋` induced by `𝔤̂(A) → 𝔤(A)`. -/
def negProj : (fHom P).range →ₗ⁅K⁆ (KacMoodyAlgebra.fHom P).range where
  toFun x := ⟨toKacMoody P hA x, by
    obtain ⟨y, hy⟩ := (LieHom.mem_range _ _).mp x.2
    exact ⟨y, by rw [← hy]; rfl⟩⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  map_lie' {x y} := by ext; simp

@[simp] lemma coe_negProj (x : (fHom P).range) :
    (negProj P hA x : P.KacMoodyAlgebra) = toKacMoody P hA x := rfl

lemma negProj_surjective : Function.Surjective (negProj P hA) := by
  rintro ⟨_, y, rfl⟩
  exact ⟨⟨fHom P y, LieHom.mem_range_self _ y⟩, rfl⟩

lemma negProj_eq_zero_iff {x : (fHom P).range} :
    negProj P hA x = 0 ↔ (x : P.SerrePresentedAlgebra) ∈ radicalNeg P := by
  rw [← LieSubmodule.mem_toSubmodule, radicalNeg_toSubmodule P hA, Submodule.mem_inf,
    LieSubmodule.mem_toSubmodule, mem_radical_iff, ← coe_negProj, ZeroMemClass.coe_eq_zero]
  exact ⟨fun h ↦ ⟨h, x.2⟩, fun h ↦ h.1⟩

lemma toKacMoody_mem_rootSpace {μ : Dual K H} {x : P.SerrePresentedAlgebra}
    (hx : x ∈ rootSpace P μ) : toKacMoody P hA x ∈ KacMoodyAlgebra.rootSpace P μ := by
  intro a
  rw [← toKacMoody_h P hA, ← LieHom.map_lie, hx a, map_smul]

/-- `𝔯̂ ∩ 𝔤̂_{-αᵢ} = 0`. -/
lemma radical_inf_rootSpace_neg_root (i : ι) :
    (radical P hA).toSubmodule ⊓ rootSpace P (-P.root i) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  rw [rootSpace_neg_root] at hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx'
  have : c • KacMoodyAlgebra.f P i = 0 := by
    rw [← toKacMoody_f P hA, ← map_smul]; exact (mem_radical_iff P hA).mp hx
  rw [smul_eq_zero] at this
  rcases this with rfl | h
  · simp
  · exact absurd h (KacMoodyAlgebra.f_ne_zero P i)

include hA in
lemma radicalNeg_le_range_fHom :
    (radicalNeg P).toSubmodule ≤
      LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) := by
  rw [radicalNeg_toSubmodule P hA]; exact inf_le_right

/-! ### The main result -/

omit [CharZero K] in
variable {P} in
/-- `a, b ∈ 𝔫̂₋` are weight vectors of weights `μ, μ' ∈ -(Q₊ \ {0})` with `μ + μ' = ν`. -/
def IsWeightPair (ν : Dual K H) (a b : (fHom P).range) : Prop :=
  ∃ μ ∈ P.negWeights, ∃ μ' ∈ P.negWeights, μ + μ' = ν ∧
    (a : P.SerrePresentedAlgebra) ∈ rootSpace P μ ∧ (b : P.SerrePresentedAlgebra) ∈ rootSpace P μ'

include hA in
/-- Step 1 of the proof of `exists_cycle_not_boundary`: a nonzero weight vector of `𝔯̂₋` of weight
`-β` is a sum of brackets of weight vectors of `𝔫̂₋` of total weight `-β`, since `β` is not a
simple root. -/
lemma exists_mem_span_lie_isWeightPair {k : ι → ℤ} {x : P.SerrePresentedAlgebra}
    (hx : x ∈ radicalNeg P) (hxk : x ∈ rootSpace P (-P.rootOf k)) (hx0 : x ≠ 0) :
    ∃ x' : (fHom P).range, (x' : P.SerrePresentedAlgebra) = x ∧
      x' ∈ Submodule.span K {y | ∃ a b, IsWeightPair (-P.rootOf k) a b ∧ y = ⁅a, b⁆} := by
  have hxN := radicalNeg_le_range_fHom P hA hx
  have hxr : x ∈ radical P hA := radicalNeg_le_radical P hA hx
  set Nm := LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra)
  have hx1 : x ∈ lieWeightSpan (h P) Nm Nm P.negWeights P.negWeights (-P.rootOf k) := by
    have := mem_of_mem_iSup_of_le (h P) _ (fun ν ↦ sup_le ?_ (lieWeightSpan_le _ _ _ _ _ ν))
      hxk (range_fHom_le_iSup P hxN)
    · rw [Submodule.mem_sup] at this
      obtain ⟨u, hu, v, hv, huv⟩ := this
      suffices u = 0 by rwa [← huv, this, zero_add]
      refine (Submodule.span_le.mpr ?_ : _ ≤ ⊥) hu
      rintro _ ⟨i, hi, rfl⟩
      exfalso
      have hi' : -P.root i = -P.rootOf k := hi
      rw [neg_inj, ← rootOf_single, P.rootOf_injective.eq_iff] at hi'
      subst hi'
      rw [rootOf_single] at hxk
      exact hx0 ((Submodule.eq_bot_iff _).mp (radical_inf_rootSpace_neg_root P hA i) x ⟨hxr, hxk⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact hi ▸ f_mem_rootSpace P i
  have : lieWeightSpan (h P) Nm Nm P.negWeights P.negWeights (-P.rootOf k) =
      (Submodule.span K {y | ∃ a b, IsWeightPair (-P.rootOf k) a b ∧ y = ⁅a, b⁆}).map
        (fHom P).range.incl.toLinearMap := by
    rw [lieWeightSpan, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨a, b, ⟨μ, hμ, μ', hμ', hμμ', ha, hb⟩, rfl⟩
      exact ⟨⁅(⟨a, ha.1⟩ : (fHom P).range), ⟨b, hb.1⟩⁆, ⟨⟨a, ha.1⟩, ⟨b, hb.1⟩,
        ⟨μ, hμ, μ', hμ', hμμ', ha.2, hb.2⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, b, ⟨μ, hμ, μ', hμ', hμμ', ha, hb⟩, rfl⟩, rfl⟩
      exact ⟨a, b, ⟨μ, hμ, μ', hμ', hμμ', ⟨a.2, ha⟩, ⟨b.2, hb⟩⟩, rfl⟩
  rw [this] at hx1
  obtain ⟨x', hx', rfl⟩ := hx1
  exact ⟨x', rfl, hx'⟩

include hA in
/-- Step 3 of the proof of `exists_cycle_not_boundary`: the image in `⋀²𝔫₋` of a combination of
wedges of weight vectors of total weight `ν` lies in `(⋀²𝔫₋)_ν`. -/
lemma map_mem_wedgeWeightSpace {ν : Dual K H} {t : ⋀[K]^2 (fHom P).range}
    (ht : t ∈ Submodule.span K {y | ∃ a b, IsWeightPair ν a b ∧ y = wedge₂ K _ a b}) :
    exteriorPower.map 2
        (negProj P hA : (fHom P).range →ₗ[K] (KacMoodyAlgebra.fHom P).range) t ∈
      KacMoodyAlgebra.wedgeWeightSpace P ν := by
  have hle : (Submodule.span K {y | ∃ a b, IsWeightPair ν a b ∧ y = wedge₂ K _ a b}).map
      (exteriorPower.map 2
        (negProj P hA : (fHom P).range →ₗ[K] (KacMoodyAlgebra.fHom P).range)) ≤
      KacMoodyAlgebra.wedgeWeightSpace P ν := by
    rw [Submodule.map_span, KacMoodyAlgebra.wedgeWeightSpace, Submodule.span_le]
    rintro _ ⟨_, ⟨a, b, ⟨μ, -, μ', -, hμμ', ha, hb⟩, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨negProj P hA a, negProj P hA b, ⟨μ, μ', hμμ', ?_, ?_⟩, ?_⟩
    · exact toKacMoody_mem_rootSpace P hA ha
    · exact toKacMoody_mem_rootSpace P hA hb
    · rw [map_wedge₂]; rfl
  exact hle (Submodule.mem_map_of_mem ht)

include hA in
/-- Step 4 of the proof of `exists_cycle_not_boundary`: under the minimality hypothesis,
`[𝔫̂₋, 𝔯̂₋]` vanishes in weight `-β`. -/
lemma eq_zero_of_mem_span_lie_radicalNeg {k : ι → ℤ}
    (hmin : ∀ l ∈ posCone ι, height l < height k →
      (radicalNeg P).toSubmodule ⊓ rootSpace P (-P.rootOf l) = ⊥)
    {x : P.SerrePresentedAlgebra} (hxk : x ∈ rootSpace P (-P.rootOf k))
    (hx : x ∈ Submodule.span K {y | ∃ a b, (a ∈ LinearMap.range
      (fHom P : FreeLieAlgebra K ι →ₗ[K] P.SerrePresentedAlgebra) ∧
        b ∈ (radicalNeg P).toSubmodule) ∧ y = ⁅a, b⁆}) : x = 0 := by
  have h6 := mem_lieWeightSpan_of_mem (h P) (fun a x hx ↦ lie_h_mem_range_fHom P a hx)
    (fun a x hx ↦ (radicalNeg P).lie_mem hx) (range_fHom_le P)
    ((radicalNeg_le_range_fHom P hA).trans (range_fHom_le P)) hx hxk
  refine (Submodule.span_le.mpr ?_ : _ ≤ ⊥) h6
  rintro _ ⟨a, r, ⟨μ, ⟨m, hm, rfl⟩, μ', ⟨l, hl, rfl⟩, hml, -, hr⟩, rfl⟩
  have hkl : m + l = k := by
    apply P.rootOf_injective
    rw [map_add, ← neg_inj, neg_add]; exact hml
  have hlt : height l < height k := by
    rw [← hkl, height_add]; linarith [height_pos hm]
  have hr0 := (Submodule.eq_bot_iff _).mp (hmin l hl hlt) r hr
  simp [hr0]

include hA in
/-- Let `x ∈ 𝔯̂₋` be a nonzero weight vector of weight `-β`, `β = ∑ kᵢ αᵢ ∈ Q₊ \ {0}`, such that
`𝔯̂₋` has no nonzero weight vectors of weight `-γ` with `ht γ < ht β`. Then there is a two-cycle
`z ∈ (⋀²𝔫₋)_{-β}` which is not a boundary, i.e. `H₂(𝔫₋)_{-β} ≠ 0`. This is the homological step
of the proof of the Gabber–Kac theorem ([Kac] §9.11 (check), [GK]); the argument is reconstructed,
see the module docstring. -/
theorem exists_cycle_not_boundary {k : ι → ℤ}
    (hmin : ∀ l ∈ posCone ι, height l < height k →
      (radicalNeg P).toSubmodule ⊓ rootSpace P (-P.rootOf l) = ⊥)
    {x : P.SerrePresentedAlgebra} (hx : x ∈ radicalNeg P) (hxk : x ∈ rootSpace P (-P.rootOf k))
    (hx0 : x ≠ 0) :
    ∃ z ∈ KacMoodyAlgebra.wedgeWeightSpace P (-P.rootOf k),
      d₂ K _ z = 0 ∧ z ∉ LinearMap.range (d₃ K (KacMoodyAlgebra.fHom P).range) := by
  -- Step 1: `x` is a sum of brackets of weight vectors of `𝔫̂₋` of total weight `-β`.
  obtain ⟨x', rfl, hx'⟩ := exists_mem_span_lie_isWeightPair P hA hx hxk hx0
  -- Step 2: lift to `t ∈ ⋀²𝔫̂₋` with `∂₂ t = x`.
  rw [← map_d₂_span_wedge₂] at hx'
  obtain ⟨t, ht, htx⟩ := hx'
  -- Step 3: the cycle `z`.
  refine ⟨_, map_mem_wedgeWeightSpace P hA ht, ?_, ?_⟩
  · rw [d₂_map, htx, (negProj_eq_zero_iff P hA).mpr hx]
  -- Step 4: if `z` is a boundary, then `x ∈ [𝔫̂₋, 𝔯̂₋]`, which vanishes in weight `-β`.
  intro hz
  have h4 := d₂_mem_lie_ker_of_map_mem_range_d₃ (negProj_surjective P hA) hz
  rw [htx, ← LieSubmodule.mem_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at h4
  apply hx0
  refine eq_zero_of_mem_span_lie_radicalNeg P hA hmin hxk ?_
  have := Submodule.mem_map_of_mem (f := (fHom P).range.incl.toLinearMap) h4
  rw [Submodule.map_span] at this
  refine (Submodule.span_mono ?_) this
  rintro _ ⟨_, ⟨a, -, r, hr, rfl⟩, rfl⟩
  exact ⟨a, r, ⟨a.2, (negProj_eq_zero_iff P hA).mp hr⟩, rfl⟩

include hA in
/-- Contrapositive form of `exists_cycle_not_boundary`: if every two-cycle of `⋀²𝔫₋` of weight
`-β` is a boundary, and `𝔯̂₋` vanishes in the weights `-γ` with `ht γ < ht β`, then `𝔯̂₋` vanishes
in weight `-β`. -/
theorem radicalNeg_inf_rootSpace_eq_bot {k : ι → ℤ}
    (hmin : ∀ l ∈ posCone ι, height l < height k →
      (radicalNeg P).toSubmodule ⊓ rootSpace P (-P.rootOf l) = ⊥)
    (hH₂ : ∀ z ∈ KacMoodyAlgebra.wedgeWeightSpace P (-P.rootOf k),
      d₂ K _ z = 0 → z ∈ LinearMap.range (d₃ K (KacMoodyAlgebra.fHom P).range)) :
    (radicalNeg P).toSubmodule ⊓ rootSpace P (-P.rootOf k) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxk⟩
  by_contra hx0
  obtain ⟨z, hz, hz2, hz3⟩ := exists_cycle_not_boundary P hA hmin hx hxk hx0
  exact hz3 (hH₂ z hz hz2)

end SerrePresentedAlgebra

end Matrix.Realization

end
