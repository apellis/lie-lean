/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.SelfDualProjective
import LieLean.Algebra.Lie.KacMoody.ProjectiveCharacter
import LieLean.Algebra.Lie.KacMoody.VermaHomFiniteType
import LieLean.Algebra.Lie.KacMoody.DualIrreducible
import LieLean.Algebra.Lie.KacMoody.VermaEmbedding

/-!
# Tensoring with a dominant Verma module

For a dominant weight `λ` (`⟨λ + ρ, β^∨⟩ ∉ ℤ_{<0}` for all positive roots `β`) the Verma module
`M(λ)` is projective in `𝒪`, and so is `M(λ) ⊗ L` for every finite-dimensional `L`. This file
computes the Hom spaces from `M(λ) ⊗ L` into Verma modules, and proves the weight estimate used
for Humphreys' Theorem 10.2 (which modules `P(μ)` occur in `M(λ) ⊗ L`).

## Main results

* `VermaModule.multiplicity_of_isDominant`: `[M(ξ) : L(λ)] = δ_{ξλ}` for `λ` dominant.
* `IsStdFiltered.finrank_hom_verma_of_isDominant`: `dim Hom(M(λ), N)` is the number of
  occurrences of `M(λ)` in a standard filtration of `N`.
* `finrank_hom_tensor_verma_of_isDominant`: **Humphreys, §3.9, Remark (∗)**:
  `dim Hom(M(λ) ⊗ L, M(μ)) = dim L_{μ - λ}`.
* `weightSpace_irreducibleModule_eq_bot_of_kacKazhdanStep`: under condition (c) of
  Theorem 10.2, no Kac–Kazhdan step `μ → λ'` gives a weight `λ' - λ` of `L(ν)`.

Finite type, finite-dimensional Cartan subalgebra, algebraically closed field of characteristic
zero. Humphreys works over `ℂ`.

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category `𝒪`*,
  GSM 94, §3.9 (Remark), §10.2–10.3.
-/

noncomputable section

open Module LieModule TensorProduct

universe u₁ u₂ w

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

section Dual

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- Restriction of a weight-`μ` vector of `V^*` to `V_{-μ}`. -/
def dualWeightRestrict (μ : Dual K H) :
    weightSpaceOfMap (Module.Dual K V) (h P) μ →ₗ[K]
      Module.Dual K (weightSpaceOfMap V (h P) (-μ)) :=
  (weightSpaceOfMap V (h P) (-μ)).subtype.dualMap ∘ₗ
    (weightSpaceOfMap (Module.Dual K V) (h P) μ).subtype


/-- A weight-`μ` vector of `V^*` vanishes on weight vectors of weight `κ ≠ -μ`. -/
theorem apply_eq_zero_of_mem_weightSpaceOfMap_dual {μ κ : Dual K H} {f : Module.Dual K V}
    (hf : f ∈ weightSpaceOfMap (Module.Dual K V) (h P) μ) {v : V}
    (hv : v ∈ weightSpaceOfMap V (h P) κ) (hκ : κ ≠ -μ) : f v = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, κ a ≠ (-μ) a := by
    by_contra hc
    push Not at hc
    exact hκ (LinearMap.ext hc)
  have h1 := congrArg (fun g : Module.Dual K V ↦ g v) (hf a)
  simp only [Module.Dual.lie_apply, hv a, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at h1
  have h2 : (κ a - (-μ) a) * f v = 0 := by
    rw [LinearMap.neg_apply]
    linear_combination -h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

/-- Restriction of weight-`μ` vectors of `V^*` to `V_{-μ}` is injective if `V` is spanned by
weight vectors. -/
theorem dualWeightRestrict_injective (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (μ : Dual K H) : Function.Injective (dualWeightRestrict P (V := V) μ) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ hfg
  refine Subtype.ext (LinearMap.ext fun v ↦ ?_)
  have hv : v ∈ ⨆ κ, weightSpaceOfMap V (h P) κ := hV ▸ Submodule.mem_top
  induction hv using Submodule.iSup_induction' with
  | mem κ v hv =>
    by_cases hκ : κ = -μ
    · subst hκ
      exact LinearMap.congr_fun hfg ⟨v, hv⟩
    · simp only
      rw [apply_eq_zero_of_mem_weightSpaceOfMap_dual P hf hv hκ,
        apply_eq_zero_of_mem_weightSpaceOfMap_dual P hg hv hκ]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

/-- `dim (V^*)_μ ≤ dim V_{-μ}` if `V` is finite-dimensional and spanned by weight vectors. -/
theorem finrank_weightSpaceOfMap_dual_le [FiniteDimensional K V]
    (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤) (μ : Dual K H) :
    finrank K (weightSpaceOfMap (Module.Dual K V) (h P) μ) ≤
      finrank K (weightSpaceOfMap V (h P) (-μ)) := by
  rw [← Subspace.dual_finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective (dualWeightRestrict_injective P hV μ)

/-- `dim (V^*)_μ = dim V_{-μ}` if `V` is finite-dimensional and `V`, `V^*` are spanned by weight
vectors. -/
theorem finrank_weightSpaceOfMap_dual [FiniteDimensional K V]
    (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (hV' : ⨆ μ, weightSpaceOfMap (Module.Dual K V) (h P) μ = ⊤) (μ : Dual K H) :
    finrank K (weightSpaceOfMap (Module.Dual K V) (h P) μ) =
      finrank K (weightSpaceOfMap V (h P) (-μ)) := by
  refine le_antisymm (finrank_weightSpaceOfMap_dual_le P hV μ) ?_
  have h1 := finrank_weightSpaceOfMap_dual_le P hV' (-μ)
  rwa [neg_neg, ← finrank_weightSpaceOfMap_equiv P
    (LieModule.evalEquiv (L := P.KacMoodyAlgebra) (M := V)) (-μ)] at h1

end Dual

section Generic

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- The subquotient `N' / (N ∩ N')` is the image of `N'` in `M / N`. -/
theorem LieSubmodule.nonempty_subquotientEquivMap (N N' : LieSubmodule R L M) :
    Nonempty (N.Subquotient N' ≃ₗ⁅R,L⁆ N'.map (LieSubmodule.Quotient.mk' N)) := by
  let θ : N' →ₗ⁅R,L⁆ N'.map (LieSubmodule.Quotient.mk' N) :=
    ((LieSubmodule.Quotient.mk' N).comp N'.incl).codRestrict _ fun x ↦ ⟨x, x.2, rfl⟩
  have hθ : Function.Surjective θ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine LieSubmodule.Quotient.nonempty_lieModuleEquiv_of_surjective _ θ hθ ?_
  ext x
  rw [LieModuleHom.mem_ker, LieSubmodule.mem_comap]
  change (⟨_, _⟩ : N'.map (LieSubmodule.Quotient.mk' N)) = 0 ↔ _
  rw [Subtype.ext_iff]
  exact LieSubmodule.Quotient.mk_eq_zero'

end Generic

section Dominant

variable {ι : Type u₁} {H : Type u₂} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- For `λ` dominant, `[M(ξ) : L(λ)] = δ_{ξλ}`: `L(λ)` is a composition factor of no Verma module
other than `M(λ)` (Humphreys, GSM 94, §3.9, Remark, last step). -/
theorem VermaModule.multiplicity_of_isDominant [DecidableEq (Dual K H)] {Λ : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) (ξ : Dual K H) :
    (isCategoryO P ξ).multiplicity Λ = if ξ = Λ then 1 else 0 := by
  split_ifs with hξ
  · subst hξ
    exact multiplicity_self ξ
  · by_contra hne
    obtain ⟨d, hdpos, hpos⟩ := hA.exists_posDef
    have hsymm : (diagonal d * A).IsSymm := by
      simpa [IsHermitian, IsSymm] using hpos.isHermitian
    obtain ⟨w, hw⟩ := exists_weylDot_of_multiplicity_ne_zero P hA
      (Symmetrization.ofDiagonal d hdpos hsymm) hne
    obtain ⟨k, hk, hkΛ⟩ := mem_cone_of_multiplicity_ne_zero hne
    have hwk : ((w⁻¹ : P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H)
        (Λ + P.rho) = Λ + P.rho + P.rootOf k := by
      have h1 := P.weylDot_add_rho hA.isGeneralizedCartan w ξ
      rw [← hw] at h1
      rw [h1, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
        LinearEquiv.coe_one, id, ← h1, hkΛ]
      abel
    have hk0 := hΛ.eq_zero_of_apply_eq P hA (w⁻¹).2 hk hwk
    apply hξ
    rw [hkΛ, hk0, map_zero, sub_zero]

include hA in
/-- For `λ` dominant and `N ⊆ X ∈ 𝒪` with a standard filtration with weights `s`,
`dim Hom(M(λ), N)` is the number of times `M(λ)` occurs in the filtration (Humphreys, GSM 94,
§3.9, Remark). -/
theorem IsStdFiltered.finrank_hom_verma_of_isDominant [DecidableEq (Dual K H)] {Λ : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) {X : Type w} [AddCommGroup X] [Module K X]
    [LieRingModule 𝔤 X] [LieModule K 𝔤 X] (hX : IsCategoryO P X)
    {N : LieSubmodule K 𝔤 X} {s : Multiset (Dual K H)} (hN : IsStdFiltered P N s) :
    finrank K (VermaModule P Λ →ₗ⁅K,𝔤⁆ N) = s.count Λ := by
  have hπ := VermaModule.isProjectiveCover P Λ
  induction hN with
  | bot =>
    have : Subsingleton (VermaModule P Λ →ₗ⁅K,𝔤⁆ (⊥ : LieSubmodule K 𝔤 X)) :=
      ⟨fun f g ↦ LieModuleHom.ext fun x ↦ Subtype.ext
        (((LieSubmodule.mem_bot _).mp (f x).2).trans ((LieSubmodule.mem_bot _).mp (g x).2).symm)⟩
    simp [Module.finrank_zero_of_subsingleton]
  | @step N N' s μ _ hle he ih =>
    obtain ⟨e⟩ := he
    obtain ⟨e'⟩ := LieSubmodule.nonempty_subquotientEquivMap N N'
    rw [hπ.finrank_hom_eq_add (VermaModule.isProjectiveO.{w} P hA hΛ) hX hle, ih,
      (lieModuleHomCongr P LieModuleEquiv.refl (e'.trans e.symm)).finrank_eq,
      hπ.finrank_hom_eq_multiplicity (VermaModule.isProjectiveO P hA hΛ) (isCategoryO P μ),
      VermaModule.multiplicity_of_isDominant P hA hΛ, Multiset.count_cons]
    by_cases hμ : μ = Λ
    · simp [hμ]
    · simp [hμ, Ne.symm hμ]

include hA in
/-- **Humphreys, GSM 94, §3.9, Remark (∗).** For `λ` dominant and `L` finite-dimensional,
`dim Hom(M(λ) ⊗ L, M(μ)) = dim L_{μ - λ}`. -/
theorem finrank_hom_tensor_verma_of_isDominant {Λ : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) {L : Type*} [AddCommGroup L] [Module K L]
    [LieRingModule 𝔤 L] [LieModule K 𝔤 L] [FiniteDimensional K L] (μ : Dual K H) :
    finrank K (VermaModule P Λ ⊗[K] L →ₗ⁅K,𝔤⁆ VermaModule P μ) =
      finrank K (weightSpaceOfMap L (h P) (μ - Λ)) := by
  classical
  have hL : IsCategoryO P L := isCategoryO_of_finiteDimensional hA
  have hL' : IsCategoryO P (Module.Dual K L) := isCategoryO_of_finiteDimensional hA
  obtain ⟨s, hs, hcount⟩ := exists_isStdFiltered_tensorVerma P hL'.1 μ
  have hX := (VermaModule.isCategoryO P μ).tensorProduct hL'
  have etop : (⊤ : LieSubmodule K 𝔤 (VermaModule P μ ⊗[K] Module.Dual K L)) ≃ₗ⁅K,𝔤⁆
      VermaModule P μ ⊗[K] Module.Dual K L :=
    LieModuleEquiv.ofBijective (⊤ : LieSubmodule K 𝔤 _).incl
      ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, trivial⟩, rfl⟩⟩
  have hc : (s.map (μ + ·)).count Λ = s.count (Λ - μ) := by
    rw [show Λ = μ + (Λ - μ) by abel, Multiset.count_map_eq_count' _ _ (add_right_injective μ),
      add_sub_cancel_left]
  rw [(tensorHomAdjunction P).finrank_eq,
    ← (lieModuleHomCongr P LieModuleEquiv.refl etop).finrank_eq,
    hs.finrank_hom_verma_of_isDominant P hA hΛ hX, hc, hcount,
    finrank_weightSpaceOfMap_dual P hL.1 hL'.1, neg_sub]

omit [IsAlgClosed K] in
/-- `2 (x | v αᵢ) = ⟨x, (v αᵢ)^∨⟩ (αᵢ | αᵢ)` for the invariant form. -/
theorem two_mul_dualBilinForm_eq_corootPairing_mul (S : A.Symmetrization) (x : Dual K H)
    (v : P.weylGroup hA.isGeneralizedCartan) (i : ι) :
    2 * P.dualBilinForm S x ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) =
      P.corootPairing hA.isGeneralizedCartan x v i * P.dualBilinForm S (P.root i) (P.root i) := by
  have h₁ := P.dualBilinForm_weylGroup hA.isGeneralizedCartan S v.2
    (((v⁻¹ : P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) x) (P.root i)
  have hx : (v : Dual K H ≃ₗ[K] Dual K H)
      (((v⁻¹ : P.weylGroup hA.isGeneralizedCartan) : Dual K H ≃ₗ[K] Dual K H) x) = x := by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      LinearEquiv.coe_one, id]
  rw [hx] at h₁
  rw [h₁]
  exact (VermaModule.two_mul_dualBilinForm_root_eq_iff P hA.isGeneralizedCartan S _ i _).mpr rfl

omit [IsAlgClosed K] in
/-- In finite type, a Kac–Kazhdan step `λ → λ - n α` is a step along a positive real root
`α = v αᵢ` with `⟨λ + ρ, α^∨⟩ = n`. -/
theorem KacKazhdanStep.exists_isPosRoot (S : A.Symmetrization) {Λ μ : Dual K H}
    (hstep : KacKazhdanStep P S Λ μ) :
    ∃ (v : P.weylGroup hA.isGeneralizedCartan) (i : ι), P.IsPosRoot hA.isGeneralizedCartan v i ∧
      ∃ n : ℕ, 0 < n ∧ μ = Λ - n • (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ∧
        P.corootPairing hA.isGeneralizedCartan (Λ + P.rho) v i = n := by
  obtain ⟨α, hα, hroot, n, hn, rfl, hKK⟩ := hstep
  have hα0 : α ≠ 0 := fun h0 ↦ P.zero_notMem_posWeights (h0 ▸ hα)
  have hreal : α ∈ P.realRoots hA.isGeneralizedCartan := by
    rw [← roots_eq_realRoots P hA]
    exact ⟨hα0, hroot⟩
  obtain ⟨u, hu, i, rfl⟩ := hreal
  refine ⟨⟨u, hu⟩, i, ?_, n, hn, rfl, ?_⟩
  · obtain ⟨k, hk, hkα⟩ := hα
    exact ⟨k, hk.1, hkα.symm⟩
  · have h := two_mul_dualBilinForm_eq_corootPairing_mul P hA S (Λ + P.rho) ⟨u, hu⟩ i
    have h₂ := P.dualBilinForm_weylGroup hA.isGeneralizedCartan S hu (P.root i) (P.root i)
    change 2 * P.dualBilinForm S (Λ + P.rho) (u (P.root i)) = _ at h
    rw [hKK, h₂] at h
    have hne : P.dualBilinForm S (P.root i) (P.root i) ≠ 0 := by
      rw [dualBilinForm_root_self S hA.isGeneralizedCartan]
      have := S.ε_pos i
      exact_mod_cast (by positivity : (2 / S.ε i : ℚ) ≠ 0)
    exact (mul_right_cancel₀ hne h).symm

omit [IsAlgClosed K] in
include hA in
/-- Steps (4)–(7) of the proof of Humphreys, GSM 94, Theorem 10.2, (c) ⇒ (b), in the form used
here: let `λ` be dominant, `μ - λ` integral, `ν` the dominant integral weight in `W(μ - λ)`, and
assume condition (c). If `μ → λ'` is a Kac–Kazhdan step, then `λ' - λ` is not a weight of `L(ν)`.
Reconstructed: `λ' - λ = (μ - λ) - n α` has norm `(μ - λ | μ - λ) + n ⟨λ + ρ, α^∨⟩ (α | α)`,
which exceeds `(ν | ν) = (μ - λ | μ - λ)` since `⟨λ + ρ, α^∨⟩ > 0` by dominance and (c); this
replaces Humphreys' use of the strong linkage principle (Theorem 5.1) and of a second module
`L(ν')`. -/
theorem weightSpace_irreducibleModule_eq_bot_of_kacKazhdanStep {Λ μ Λ' ν : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) (hint : ∀ j, ∃ z : ℤ, (μ - Λ) (P.coroot j) = z)
    (hc : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (Λ + P.rho) v i = 0 →
      ∀ n : ℤ, P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = n → n ≤ 0)
    (hν : P.IsDominantIntegral ν) {w : Dual K H ≃ₗ[K] Dual K H}
    (hw : w ∈ P.weylGroup hA.isGeneralizedCartan) (hνw : ν = w (μ - Λ)) (S : A.Symmetrization)
    (hstep : KacKazhdanStep P S μ Λ') :
    weightSpace P (IrreducibleModule P ν) (Λ' - Λ) = ⊥ := by
  by_contra hx
  have hA' := hA.isGeneralizedCartan
  obtain ⟨d, hd, hpos⟩ := hA.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  obtain ⟨v, i, hv, n, hn, rfl, hpair⟩ := hstep.exists_isPosRoot P hA S
  set S' := Symmetrization.ofDiagonal d hd hsymm
  set B := P.dualBilinForm S'
  set β := (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)
  obtain ⟨c, hcγ⟩ := exists_int_corootPairing_of_integral P hA' hint v i
  have hΛc : P.corootPairing hA' (Λ + P.rho) v i = ((n - c : ℤ) : K) := by
    have h := corootPairing_sub (P := P) (hA := hA') (μ + P.rho) (Λ + P.rho) v i
    rw [add_sub_add_right_eq_sub, hcγ, hpair] at h
    push_cast
    linear_combination h
  have h0 : 0 ≤ (n : ℤ) - c := hΛ v i hv _ hΛc
  have h1 : (n : ℤ) - c ≠ 0 := by
    intro h1
    have := hc v i hv (by rw [hΛc, h1, Int.cast_zero]) n (by rw [hpair]; push_cast; rfl)
    omega
  obtain ⟨m, hm, -⟩ := IrreducibleModule.exists_norm_eq_add P hA hd hsymm hpos hν hx
  have hνν : B ν ν = B (μ - Λ) (μ - Λ) := by
    rw [hνw]
    exact P.dualBilinForm_weylGroup hA' S' hw (μ - Λ) (μ - Λ)
  have hββ : B β β = B (P.root i) (P.root i) :=
    P.dualBilinForm_weylGroup hA' S' v.2 (P.root i) (P.root i)
  have hγβ : 2 * B (μ - Λ) β = (c : K) * B (P.root i) (P.root i) := by
    have := two_mul_dualBilinForm_eq_corootPairing_mul P hA S' (μ - Λ) v i
    rwa [hcγ] at this
  have key : ∀ x y : Dual K H,
      B (x - (n : K) • y) (x - (n : K) • y) = B x x - 2 * n * B x y + n ^ 2 * B y y := by
    intro x y
    have hs : B y x = B x y := (P.isSymm_dualBilinForm S').eq y x
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hs]
    ring
  have hx' : μ - n • β - Λ = (μ - Λ) - (n : K) • β := by
    rw [Nat.cast_smul_eq_nsmul]
    abel
  rw [hx', hνν, key, hββ, dualBilinForm_root_self S' hA'] at hm
  rw [dualBilinForm_root_self S' hA'] at hγβ
  have hε := S'.ε_pos i
  have hq : ((((n : ℚ) * ((n : ℚ) - c) * (2 / S'.ε i) + m : ℚ)) : K) = 0 := by
    push_cast at hm hγβ ⊢
    linear_combination -hm + (n : K) * hγβ
  have hq' : ((n : ℚ) * ((n : ℚ) - c) * (2 / S'.ε i) + m : ℚ) = 0 := by exact_mod_cast hq
  have hnc : (0 : ℚ) < (n : ℚ) - c := by
    have : (0 : ℤ) < n - c := lt_of_le_of_ne h0 (Ne.symm h1)
    exact_mod_cast this
  have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
  have : (0 : ℚ) < (n : ℚ) * ((n : ℚ) - c) * (2 / S'.ε i) + m := by positivity
  linarith

end Dominant

end Matrix.Realization.KacMoodyAlgebra
