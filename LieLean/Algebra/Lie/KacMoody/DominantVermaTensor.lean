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
* `tfae_projectiveCover_tensor_verma`: **Humphreys, Theorem 10.2**: for `λ` dominant and
  `μ - λ` integral, `P(μ)` is a summand of some `M(λ) ⊗ L` iff `Hom(M(λ) ⊗ L, L(μ)) ≠ 0` for some
  `L` iff `⟨μ + ρ, α^∨⟩ ≤ 0` for all `α > 0` with `⟨λ + ρ, α^∨⟩ = 0`. The two main implications
  are `hom_tensor_verma_irreducibleModule_eq_zero` and
  `finrank_hom_tensor_verma_irreducibleModule_eq_one` (multiplicity one for `L = L(ν)`).

The proof of (c) ⇒ (b) avoids the strong linkage principle (Theorem 5.1), which is not
formalized: a composition factor `L(μ')` of `M(μ)`, `μ' ≠ μ`, lies below a Kac–Kazhdan step
`μ → λ'`, and a norm estimate shows that `λ' - λ` is not a weight of `L(ν)`.

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

/-- Left composition with `f`, as a linear map `Hom(Q, M) → Hom(Q, N)`. -/
def _root_.LieModuleHom.homCompLeftₗ {Q N : Type*} [AddCommGroup Q] [Module R Q] [LieRingModule L Q]
    [LieModule R L Q] [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
    (f : M →ₗ⁅R,L⁆ N) : (Q →ₗ⁅R,L⁆ M) →ₗ[R] (Q →ₗ⁅R,L⁆ N) where
  toFun g := f.comp g
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp

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

omit [IsAlgClosed K] in
include hA in
/-- `L(ν)_x` is one-dimensional for `x` in the Weyl group orbit of a dominant integral `ν`. -/
theorem finrank_weightSpace_irreducibleModule_of_apply_eq {ν x : Dual K H}
    (hν : P.IsDominantIntegral ν) {w : Dual K H ≃ₗ[K] Dual K H}
    (hw : w ∈ P.weylGroup hA.isGeneralizedCartan) (hx : w x = ν) :
    finrank K (weightSpaceOfMap (IrreducibleModule P ν) (h P) x) = 1 := by
  have := IrreducibleModule.finiteDimensional hA hν
  have h := rank_weightSpace_weylGroup hA.isGeneralizedCartan
    (isIntegrable_of_finiteDimensional hA (V := IrreducibleModule P ν)) hw x
  rw [hx] at h
  rw [← IrreducibleModule.finrank_weightSpace_self P ν]
  exact congrArg Cardinal.toNat h.symm

include hA in
/-- For `λ` dominant and `L` finite-dimensional, `M(λ) ⊗ L` is a finitely generated projective
module in `𝒪` (Humphreys, GSM 94, §3.8 and §10.2). -/
theorem isFGProjectiveO_tensor_verma {Λ : Dual K H} (hΛ : P.IsDominant hA.isGeneralizedCartan Λ)
    {L : Type (max u₁ u₂)} [AddCommGroup L] [Module K L] [LieRingModule 𝔤 L] [LieModule K 𝔤 L]
    [FiniteDimensional K L] : IsFGProjectiveO P (VermaModule P Λ ⊗[K] L) where
  isProjectiveO := IsProjectiveO.tensorProduct P (VermaModule.isProjectiveO P hA hΛ)
    (isCategoryO_of_finiteDimensional hA)
  isCategoryO := (VermaModule.isCategoryO P Λ).tensorProduct (isCategoryO_of_finiteDimensional hA)
  fg := exists_finset_lieSpan_tmul_eq_top
    (VermaModule.lieSpan_map_hwv_eq_top (P := P) (Λ := Λ) LieModuleHom.id Function.surjective_id)

include hA in
/-- A nonzero morphism `g` from a finitely generated `V ∈ 𝒪` to `Y ∈ 𝒪` gives a simple quotient
`L(ξ)` of `V` that is a composition factor of `Y` (step (4) of Humphreys, GSM 94, §10.3): take a
simple quotient of the image of `g`. -/
theorem exists_surjective_irreducibleModule_of_ne_zero {V Y : Type*} [AddCommGroup V]
    [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V] [AddCommGroup Y] [Module K Y]
    [LieRingModule 𝔤 Y] [LieModule K 𝔤 Y] {S : Finset V}
    (hS : LieSubmodule.lieSpan K 𝔤 (S : Set V) = ⊤) (hY : IsCategoryO P Y)
    {g : V →ₗ⁅K,𝔤⁆ Y} (hg : g ≠ 0) :
    ∃ ξ : Dual K H, ∃ φ : V →ₗ⁅K,𝔤⁆ IrreducibleModule P ξ, Function.Surjective φ ∧
      hY.multiplicity ξ ≠ 0 := by
  classical
  let g' : V →ₗ⁅K,𝔤⁆ g.range :=
    g.codRestrict g.range fun m ↦ (LieModuleHom.mem_range _ _).mpr ⟨m, rfl⟩
  have hg' : Function.Surjective g' := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := (LieModuleHom.mem_range _ _).mp hy
    exact ⟨m, rfl⟩
  have : Nontrivial g.range := by
    obtain ⟨v, hv⟩ : ∃ v, g v ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (LieModuleHom.ext h)
    exact ⟨⟨g' v, 0, fun h ↦ hv (congrArg Subtype.val h)⟩⟩
  have hSR : LieSubmodule.lieSpan K 𝔤 ((S.image g' : Finset g.range) : Set g.range) = ⊤ := by
    have hle : LieSubmodule.lieSpan K 𝔤 (S : Set V) ≤
        (LieSubmodule.lieSpan K 𝔤 ((S.image g' : Finset g.range) : Set g.range)).comap g' :=
      LieSubmodule.lieSpan_le.mpr fun s hs ↦ LieSubmodule.subset_lieSpan
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem g' (Finset.mem_coe.mp hs)))
    rw [hS] at hle
    rw [eq_top_iff]
    rintro y -
    obtain ⟨v, rfl⟩ := hg' y
    exact hle (LieSubmodule.mem_top v)
  obtain ⟨ξ, φ, hφ⟩ := (hY.lieSubmodule g.range).exists_surjective_irreducibleModule P hA hSR
  refine ⟨ξ, φ.comp g', hφ.comp hg', ?_⟩
  have h1 := hY.multiplicity_eq_add g.range ξ
  have h2 := IsCategoryO.multiplicity_eq_add_of_exact ((hY.lieSubmodule g.range).lieSubmodule φ.ker)
    (hY.lieSubmodule g.range) (IrreducibleModule.isCategoryO P ξ) φ.ker.incl φ
    Subtype.val_injective (LieSubmodule.range_incl _).symm hφ ξ
  simp only [IrreducibleModule.multiplicity_eq, ↓reduceIte] at h2
  omega

include hA in
/-- If a finitely generated projective `V ∈ 𝒪` maps onto `L(ξ)` and `[Y : L(ξ)] ≠ 0`, then
`Hom(V, Y) ≠ 0`: `P(ξ)` is a summand of `V` and `dim Hom(P(ξ), Y) = [Y : L(ξ)]` (Humphreys,
GSM 94, Theorem 3.9). -/
theorem IsFGProjectiveO.finrank_hom_ne_zero_of_multiplicity {V : Type (max u₁ u₂)}
    [AddCommGroup V] [Module K V] [LieRingModule 𝔤 V] [LieModule K 𝔤 V]
    (hV : IsFGProjectiveO P V) {ξ : Dual K H} {φ : V →ₗ⁅K,𝔤⁆ IrreducibleModule P ξ}
    (hφ : Function.Surjective φ) {Y : Type*} [AddCommGroup Y] [Module K Y] [LieRingModule 𝔤 Y]
    [LieModule K 𝔤 Y] (hY : IsCategoryO P Y) (hξ : hY.multiplicity ξ ≠ 0) :
    finrank K (V →ₗ⁅K,𝔤⁆ Y) ≠ 0 := by
  obtain ⟨s, r, hrs⟩ := hV.exists_retract hA φ hφ
  rw [hV.finrank_hom_eq_add hA hrs hY, ProjectiveCover.finrank_hom_eq_multiplicity P ξ hA hY]
  omega

include hA in
/-- **Humphreys, GSM 94, Theorem 10.2, (c) ⇒ (b), with multiplicity one** (steps (3)–(7) of
§10.3). Let `λ` be dominant with `μ - λ` integral, and suppose `⟨μ + ρ, α^∨⟩ ≤ 0` for every
positive root `α` with `⟨λ + ρ, α^∨⟩ = 0`. If `ν` is the dominant integral weight in `W(μ - λ)`,
then `dim Hom(M(λ) ⊗ L(ν), L(μ)) = 1`; by Theorem 3.9 (b) this is the number of summands
`P(μ)` of `M(λ) ⊗ L(ν)`. The proof replaces Humphreys' appeal to the strong linkage principle
(Theorem 5.1) by a Kac–Kazhdan step and the norm estimate
`weightSpace_irreducibleModule_eq_bot_of_kacKazhdanStep` (reconstructed). -/
theorem finrank_hom_tensor_verma_irreducibleModule_eq_one {Λ μ ν : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) (hint : ∀ j, ∃ z : ℤ, (μ - Λ) (P.coroot j) = z)
    (hc : ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
      P.corootPairing hA.isGeneralizedCartan (Λ + P.rho) v i = 0 →
      ∀ n : ℤ, P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = n → n ≤ 0)
    (hν : P.IsDominantIntegral ν) {w : Dual K H ≃ₗ[K] Dual K H}
    (hw : w ∈ P.weylGroup hA.isGeneralizedCartan) (hνw : ν = w (μ - Λ)) :
    finrank K (VermaModule P Λ ⊗[K] IrreducibleModule P ν →ₗ⁅K,𝔤⁆ IrreducibleModule P μ) =
      1 := by
  classical
  have := IrreducibleModule.finiteDimensional hA hν
  have hV := isFGProjectiveO_tensor_verma P hA hΛ (L := IrreducibleModule P ν)
  have h1 : finrank K (VermaModule P Λ ⊗[K] IrreducibleModule P ν →ₗ⁅K,𝔤⁆ VermaModule P μ) =
      1 := by
    rw [finrank_hom_tensor_verma_of_isDominant P hA hΛ μ]
    exact finrank_weightSpace_irreducibleModule_of_apply_eq P hA hν hw hνw.symm
  let π : VermaModule P μ →ₗ⁅K,𝔤⁆ IrreducibleModule P μ :=
    LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P μ)
  have hπ : Function.Surjective π := LieSubmodule.Quotient.surjective_mk' _
  have hsurj : Function.Surjective
      (π.homCompLeftₗ (Q := VermaModule P Λ ⊗[K] IrreducibleModule P ν)) := fun φ ↦
    hV.isProjectiveO (VermaModule.isCategoryO P μ) (IrreducibleModule.isCategoryO P μ) π hπ φ
  have := hV.finiteDimensional_hom (VermaModule.isCategoryO P μ)
  have := hV.finiteDimensional_hom (IrreducibleModule.isCategoryO P μ)
  have hle := LinearMap.finrank_range_le
    (π.homCompLeftₗ (Q := VermaModule P Λ ⊗[K] IrreducibleModule P ν))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, h1] at hle
  have hne : finrank K (VermaModule P Λ ⊗[K] IrreducibleModule P ν →ₗ⁅K,𝔤⁆
      IrreducibleModule P μ) ≠ 0 := by
    intro h0
    have hsub := Module.finrank_zero_iff.mp h0
    obtain ⟨g, hg⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (h1 ▸ Nat.one_pos)
    obtain ⟨ξ, φ, hφ, hξ⟩ := exists_surjective_irreducibleModule_of_ne_zero P hA
      hV.fg.choose_spec (VermaModule.isCategoryO P μ) hg
    have hξμ : ξ ≠ μ := by
      rintro rfl
      obtain ⟨x, hx⟩ := hφ (IrreducibleModule.hwv P ξ)
      rw [Subsingleton.elim φ 0, _root_.zero_apply] at hx
      exact IrreducibleModule.hwv_ne_zero P ξ hx.symm
    obtain ⟨d, hd, hpos⟩ := hA.exists_posDef
    have hsymm : (diagonal d * A).IsSymm := by
      simpa [IsHermitian, IsSymm] using hpos.isHermitian
    obtain ⟨Λ', hstep, hΛ'⟩ := VermaModule.exists_kacKazhdanStep_of_multiplicity_ne_zero P
      (Symmetrization.ofDiagonal d hd hsymm) hA.isGeneralizedCartan hξμ hξ
    have h2 := hV.finrank_hom_ne_zero_of_multiplicity P hA hφ (VermaModule.isCategoryO P Λ') hΛ'
    rw [finrank_hom_tensor_verma_of_isDominant P hA hΛ Λ'] at h2
    apply h2
    rw [show weightSpaceOfMap (IrreducibleModule P ν) (h P) (Λ' - Λ) = ⊥ from
      weightSpace_irreducibleModule_eq_bot_of_kacKazhdanStep P hA hΛ hint hc hν hw hνw _ hstep]
    exact finrank_bot K _
  omega

include hA in
/-- **Humphreys, GSM 94, Theorem 10.2, (b) ⇒ (c)** (steps (1)–(2) of §10.3). Let `λ` be dominant,
`L` finite-dimensional and `α > 0` a root with `⟨λ + ρ, α^∨⟩ = 0` and `⟨μ + ρ, α^∨⟩ = n > 0`.
Then every morphism `M(λ) ⊗ L → L(μ)` vanishes: by Remark 3.9 (∗) and `W`-invariance of weight
multiplicities, composition with the embedding `M(μ - nα) ↪ M(μ)` of Theorem 4.6 is a bijection
on Hom spaces out of `M(λ) ⊗ L`, so every morphism to `M(μ)` lands in `N(μ)`. -/
theorem hom_tensor_verma_irreducibleModule_eq_zero {Λ μ : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) {L : Type*} [AddCommGroup L] [Module K L]
    [LieRingModule 𝔤 L] [LieModule K 𝔤 L] [FiniteDimensional K L]
    {v : P.weylGroup hA.isGeneralizedCartan} {i : ι} (hv : P.IsPosRoot hA.isGeneralizedCartan v i)
    (hΛ0 : P.corootPairing hA.isGeneralizedCartan (Λ + P.rho) v i = 0) {n : ℕ} (hn : 0 < n)
    (hμn : P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = n)
    (φ : VermaModule P Λ ⊗[K] L →ₗ⁅K,𝔤⁆ IrreducibleModule P μ) : φ = 0 := by
  classical
  have hA' := hA.isGeneralizedCartan
  set α := (v : Dual K H ≃ₗ[K] Dual K H) (P.root i)
  have hL : IsCategoryO P L := isCategoryO_of_finiteDimensional hA
  have hL' : IsCategoryO P (Module.Dual K L) := isCategoryO_of_finiteDimensional hA
  have hVp := IsProjectiveO.tensorProduct.{max u₁ u₂} P (VermaModule.isProjectiveO P hA hΛ) hL'
  have hVO : IsCategoryO P (VermaModule P Λ ⊗[K] L) :=
    (VermaModule.isCategoryO P Λ).tensorProduct hL
  obtain ⟨S, hS⟩ := exists_finset_lieSpan_tmul_eq_top (W := L)
    (VermaModule.lieSpan_map_hwv_eq_top (P := P) (Λ := Λ) LieModuleHom.id Function.surjective_id)
  obtain ⟨ψ, hψ⟩ := VermaModule.exists_injective_reflectionOf P hA hv hμn
  -- `s_α (μ - λ) = μ - n α - λ`
  have hpair : P.corootPairing hA' (μ - Λ) v i = n := by
    have h := corootPairing_sub (P := P) (hA := hA') (μ + P.rho) (Λ + P.rho) v i
    rw [add_sub_add_right_eq_sub, hμn, hΛ0, sub_zero] at h
    exact h
  have hrefl : ((P.reflectionOf hA' v i : P.weylGroup hA') : Dual K H ≃ₗ[K] Dual K H) (μ - Λ) =
      μ - n • α - Λ := by
    rw [reflectionOf_apply', hpair, Nat.cast_smul_eq_nsmul]
    abel
  have hdim : finrank K (VermaModule P Λ ⊗[K] L →ₗ⁅K,𝔤⁆ VermaModule P (μ - n • α)) =
      finrank K (VermaModule P Λ ⊗[K] L →ₗ⁅K,𝔤⁆ VermaModule P μ) := by
    rw [finrank_hom_tensor_verma_of_isDominant P hA hΛ, finrank_hom_tensor_verma_of_isDominant P hA
      hΛ, ← hrefl]
    exact congrArg Cardinal.toNat (rank_weightSpace_weylGroup hA'
      (isIntegrable_of_finiteDimensional hA (V := L)) (P.reflectionOf hA' v i).2 (μ - Λ))
  have := hVO.finiteDimensional_hom P hS (VermaModule.isCategoryO P μ)
  have := hVO.finiteDimensional_hom P hS (VermaModule.isCategoryO P (μ - n • α))
  have hinj : Function.Injective (ψ.homCompLeftₗ (Q := VermaModule P Λ ⊗[K] L)) :=
    fun g g' hgg ↦ LieModuleHom.ext fun x ↦ hψ (LieModuleHom.congr_fun hgg x)
  have hbij := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  -- the image of `ψ` is a proper submodule of `M(μ)`
  have hne : ψ.range ≠ ⊤ := by
    intro htop
    let e := LieModuleEquiv.ofBijective ψ ⟨hψ, (LieModuleHom.range_eq_top _).mp htop⟩
    have hm := IsCategoryO.multiplicity_congr (VermaModule.isCategoryO P (μ - n • α))
      (VermaModule.isCategoryO P μ) e μ
    rw [VermaModule.multiplicity_self] at hm
    have hc1 : μ ∈ cone P (μ - n • α) :=
      VermaModule.mem_cone_of_multiplicity_ne_zero (by rw [hm]; exact one_ne_zero)
    obtain ⟨k₀, hk₀, hαk⟩ := hv
    have hc2 : μ - n • α ∈ cone P μ := ⟨n • k₀, nsmul_nonneg hk₀ n, by rw [map_nsmul, ← hαk]⟩
    have h0 : n • α = 0 := by
      have := eq_of_mem_cone_of_mem_cone hc2 hc1
      rwa [sub_eq_self] at this
    rw [smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · omega
    · exact P.linearIndependent_root.ne_zero i
        ((v : Dual K H ≃ₗ[K] Dual K H).map_eq_zero_iff.mp h0)
  have hrange : ψ.range ≤ VermaModule.maxSubmodule P μ :=
    (VermaModule.le_maxSubmodule_iff P μ _).mpr hne
  let π : VermaModule P μ →ₗ⁅K,𝔤⁆ IrreducibleModule P μ :=
    LieSubmodule.Quotient.mk' (VermaModule.maxSubmodule P μ)
  obtain ⟨g, rfl⟩ := hVp (VermaModule.isCategoryO P μ) (IrreducibleModule.isCategoryO P μ) π
    (LieSubmodule.Quotient.surjective_mk' _) φ
  obtain ⟨g', rfl⟩ := hbij g
  ext x
  change π (ψ (g' x)) = 0
  exact LieSubmodule.Quotient.mk_eq_zero'.mpr
    (hrange ((LieModuleHom.mem_range _ _).mpr ⟨g' x, rfl⟩))

include hA in
/-- **Humphreys, GSM 94, Theorem 10.2.** Let `λ` be dominant and `μ - λ` integral. Then the
following are equivalent:
(a) for some finite-dimensional `L`, `P(μ)` is a direct summand of `M(λ) ⊗ L`;
(b) for some finite-dimensional `L`, `Hom(M(λ) ⊗ L, L(μ)) ≠ 0`;
(c) `⟨μ + ρ, α^∨⟩ ≤ 0` for every positive root `α` with `⟨λ + ρ, α^∨⟩ = 0`.
A direct summand is recorded as a retraction `r ∘ s = id`. The multiplicity statement (`P(μ)`
occurs once in `M(λ) ⊗ L(ν)`) is `finrank_hom_tensor_verma_irreducibleModule_eq_one`. Humphreys
works over `ℂ`; here the field is algebraically closed of characteristic zero. -/
theorem tfae_projectiveCover_tensor_verma {Λ μ : Dual K H}
    (hΛ : P.IsDominant hA.isGeneralizedCartan Λ) (hint : ∀ j, ∃ z : ℤ, (μ - Λ) (P.coroot j) = z) :
    List.TFAE [
      ∃ (L : Type (max u₁ u₂)) (_ : AddCommGroup L) (_ : Module K L) (_ : LieRingModule 𝔤 L)
        (_ : LieModule K 𝔤 L) (_ : FiniteDimensional K L)
        (s : ProjectiveCover P hA μ →ₗ⁅K,𝔤⁆ VermaModule P Λ ⊗[K] L)
        (r : VermaModule P Λ ⊗[K] L →ₗ⁅K,𝔤⁆ ProjectiveCover P hA μ), r.comp s = LieModuleHom.id,
      ∃ (L : Type (max u₁ u₂)) (_ : AddCommGroup L) (_ : Module K L) (_ : LieRingModule 𝔤 L)
        (_ : LieModule K 𝔤 L) (_ : FiniteDimensional K L)
        (φ : VermaModule P Λ ⊗[K] L →ₗ⁅K,𝔤⁆ IrreducibleModule P μ), φ ≠ 0,
      ∀ v i, P.IsPosRoot hA.isGeneralizedCartan v i →
        P.corootPairing hA.isGeneralizedCartan (Λ + P.rho) v i = 0 →
        ∀ n : ℤ, P.corootPairing hA.isGeneralizedCartan (μ + P.rho) v i = n → n ≤ 0] := by
  tfae_have 1 → 2 := by
    rintro ⟨L, _, _, _, _, _, s, r, hrs⟩
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      (ProjectiveCover.π P hA μ).comp r, fun h0 ↦ ?_⟩
    obtain ⟨x, hx⟩ := ProjectiveCover.surjective_π P hA μ (IrreducibleModule.hwv P μ)
    have h := LieModuleHom.congr_fun h0 (s x)
    rw [LieModuleHom.comp_apply, ← LieModuleHom.comp_apply r s, hrs, LieModuleHom.id_apply, hx,
      _root_.zero_apply] at h
    exact IrreducibleModule.hwv_ne_zero P μ h
  tfae_have 2 → 3 := by
    rintro ⟨L, _, _, _, _, _, φ, hφ⟩ v i hv hΛ0 n hn
    by_contra hlt
    push Not at hlt
    refine hφ (hom_tensor_verma_irreducibleModule_eq_zero P hA hΛ hv hΛ0 (n := n.toNat)
      (by omega) ?_ φ)
    rw [hn, ← Int.cast_natCast, Int.toNat_of_nonneg hlt.le]
  tfae_have 3 → 1 := by
    intro hc
    have := P.finite_weylGroup hA
    obtain ⟨w, hw⟩ := exists_dominantIntegral_weylGroup P hA.isGeneralizedCartan hint
    have h1 := finrank_hom_tensor_verma_irreducibleModule_eq_one P hA hΛ hint hc hw w.2 rfl
    have := IrreducibleModule.finiteDimensional hA hw
    have hV := isFGProjectiveO_tensor_verma P hA hΛ (L := IrreducibleModule P (w.val (μ - Λ)))
    have := hV.finiteDimensional_hom (IrreducibleModule.isCategoryO P μ)
    obtain ⟨φ, hφ⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (h1 ▸ Nat.one_pos)
    obtain ⟨s, r, hrs⟩ := hV.exists_retract hA φ
      (surjective_of_ne_zero_irreducibleModule P hφ)
    exact ⟨IrreducibleModule P (w.val (μ - Λ)), inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, s, r, hrs⟩
  tfae_finish

end Dominant

end Matrix.Realization.KacMoodyAlgebra
