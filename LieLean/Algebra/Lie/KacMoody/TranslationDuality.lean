/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.RestrictedDual
import LieLean.Algebra.Lie.KacMoody.TranslationFunctor

/-!
# Duality, central blocks and translation of dual Verma modules

In finite type, the transpose antiautomorphism `σ` of `U(𝔤)` fixes the centre pointwise, so the
duality functor `M ↦ M^∨` preserves generalized central characters. For `M` in category `𝒪`
this gives `(pr_χ M)^∨ ≅ pr_χ (M^∨)`; combined with `(M ⊗ L(ν))^∨ ≅ M^∨ ⊗ L(ν)` it shows that
translation functors commute with duality, and hence translate dual Verma modules.

## Main results

* `unop_envTranspose_center`: `σ(z) = z` for `z` central (finite type; Humphreys, GSM 94, §3.2
  and the Exercise in §1.10).
* `restrictedDualCentralBlockEquiv`: `(pr_χ M)^∨ ≅ pr_χ (M^∨)` for `M` in `𝒪`.
* `restrictedDualCentralTranslationEquiv`: `(T M)^∨ ≅ T (M^∨)` for
  `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ L(ν))`, `ν` dominant integral, `M` in `𝒪`.
* `translation_dualVerma`: `T_λ^μ M(w·λ)^∨ ≅ M(w·μ)^∨` (Humphreys, GSM 94, Theorem 7.6,
  dual Verma part, integral weights, finite type).

The argument (reconstructed): for `z` central, `χ_Λ(σ z) = χ_Λ(z)` by contravariance of the
Shapovalov form at the highest weight vector, so `σ z = z` by injectivity of the Harish-Chandra
homomorphism. A weight-`μ` functional on `M` is then killed by `(z - χ(z))^n` as soon as
`(z - χ(z))^n` kills the finite-dimensional weight space `M_μ`.
-/

noncomputable section

open Module LieModule TensorProduct

/-- If every vector of a finitely generated submodule is killed by some power of `T`, then one
power of `T` kills the whole submodule. -/
theorem Module.End.exists_pow_apply_eq_zero_of_fg {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {T : Module.End K M} {S : Submodule K M} (hS : S.FG)
    (h : ∀ v ∈ S, ∃ m : ℕ, (T ^ m) v = 0) : ∃ n : ℕ, ∀ v ∈ S, (T ^ n) v = 0 := by
  classical
  obtain ⟨s, rfl⟩ := hS
  choose! m hm using fun v (hv : v ∈ (s : Set M)) ↦ h v (Submodule.subset_span hv)
  refine ⟨∑ v ∈ s, m v, fun v hv ↦ ?_⟩
  have hle : Submodule.span K (s : Set M) ≤ LinearMap.ker (T ^ ∑ v ∈ s, m v) := by
    rw [Submodule.span_le]
    intro v hv
    rw [SetLike.mem_coe, LinearMap.mem_ker,
      ← Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hv), pow_add,
      Module.End.mul_apply, hm v hv, map_zero]
  exact hle hv

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule TwistedDual

section Center

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

/-- `σ` maps the centre of `U(𝔤)` to itself. -/
theorem unop_envTranspose_mem_center (z : 𝓩) : (envTranspose P (z : 𝓤)).unop ∈ 𝓩 := by
  rw [Subalgebra.mem_center_iff]
  intro u
  have hz := Subalgebra.mem_center_iff.mp z.property (envTranspose P u).unop
  have := congrArg (fun a ↦ (envTranspose P a).unop) hz
  simp only [unop_envTranspose_mul, unop_envTranspose_unop_envTranspose] at this
  exact this.symm

/-- The transpose `σ(z)` of a central element, as a central element. -/
def centerTranspose (z : 𝓩) : 𝓩 := ⟨_, unop_envTranspose_mem_center P z⟩

/-- Central characters of Verma modules are `σ`-invariant: `χ_Λ(σ z) = χ_Λ(z)`, by
contravariance of the Shapovalov form at the highest weight vector. -/
theorem centralCharacter_centerTranspose (Λ : Dual K H) (z : 𝓩) :
    centralCharacter P Λ (centerTranspose P z) = centralCharacter P Λ z := by
  have h := contravariantForm_smul_left P Λ (z : 𝓤) (hwv P Λ) (hwv P Λ)
  have h1 : (z : 𝓤) • hwv P Λ = centralCharacter P Λ z • hwv P Λ :=
    centralCharacter_smul P Λ z _
  have h2 : (envTranspose P (z : 𝓤)).unop • hwv P Λ =
      centralCharacter P Λ (centerTranspose P z) • hwv P Λ :=
    centralCharacter_smul P Λ (centerTranspose P z) _
  rw [h1, h2, map_smul, LinearMap.smul_apply, map_smul, contravariantForm_hwv_hwv] at h
  simpa using h.symm

omit [CharZero K] in
/-- Central elements preserve weight spaces, together with their shifted powers. -/
theorem rep_center_sub_pow_mem_weightSpace (z : 𝓩) (c : K) (n : ℕ) {μ : Dual K H} {v : V}
    (hv : v ∈ weightSpaceOfMap V (h P) μ) :
    ((rep P V (z : 𝓤) - c • 1) ^ n) v ∈ weightSpaceOfMap V (h P) μ := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact Submodule.sub_mem _ (rep_center_mem_weightSpace P z μ ih) (Submodule.smul_mem _ _ ih)

omit [CharZero K] in
/-- A module equals its own generalized central block. -/
theorem centralBlock_centralBlock_eq_top (χ : 𝓩 →ₐ[K] K) :
    centralBlock P (centralBlock P V χ) χ = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  exact mem_centralBlock_of_injective P (centralBlock P V χ).incl Subtype.val_injective χ
    v.property

variable [FiniteDimensional K H] (hA : A.IsFiniteCartan)

include hA in
/-- **`σ` fixes the centre** of `U(𝔤)` in finite type (Humphreys, GSM 94, §3.2).
Reconstructed: `χ_Λ(σ z) = χ_Λ(z)` for all `Λ`, and the Harish-Chandra homomorphism is
injective. -/
theorem unop_envTranspose_center (z : 𝓩) : (envTranspose P (z : 𝓤)).unop = z := by
  have := harishChandra_injective P hA (a₁ := centerTranspose P z) (a₂ := z)
    (SymmetricAlgebra.eq_of_lift_eq fun Λ ↦ by
      change SymmetricAlgebra.lift Λ (harishChandraProjection P
          ((centerTranspose P z : 𝓩) : 𝓤)) =
        SymmetricAlgebra.lift Λ (harishChandraProjection P (z : 𝓤))
      rw [eval_harishChandraProjection_center, eval_harishChandraProjection_center,
        centralCharacter_centerTranspose])
  exact congrArg Subtype.val this

include hA in
/-- Central elements act on the twisted dual by the transpose of their action. -/
theorem toDual_rep_center_sub_pow (z : 𝓩) (c : K) (n : ℕ) (φ : TwistedDual P V) :
    TwistedDual.toDual P V (((rep P (TwistedDual P V) (z : 𝓤) - c • 1) ^ n) φ) =
      TwistedDual.toDual P V φ ∘ₗ (rep P V (z : 𝓤) - c • 1) ^ n := by
  have hz := unop_envTranspose_center P hA z
  induction n generalizing φ with
  | zero => ext v; simp
  | succ n ih =>
    ext v
    rw [pow_succ, Module.End.mul_apply, ih, LinearMap.comp_apply, LinearMap.comp_apply,
      pow_succ', Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, toDual_rep, hz, LinearMap.comp_apply]

include hA in
/-- If `M` is a weight module with finite-dimensional weight spaces lying in the generalized
central block `χ`, then so does every sum of weight vectors of its twisted dual. -/
theorem mem_centralBlock_twistedDual (hV : ⨆ μ, weightSpaceOfMap V (h P) μ = ⊤)
    (hfin : ∀ μ, FiniteDimensional K (weightSpaceOfMap V (h P) μ)) {χ : 𝓩 →ₐ[K] K}
    (hχ : centralBlock P V χ = ⊤) {φ : TwistedDual P V} (hφ : φ ∈ restrictedDual P V) :
    φ ∈ centralBlock P (TwistedDual P V) χ := by
  rw [mem_restrictedDual] at hφ
  induction hφ using Submodule.iSup_induction' with
  | mem μ φ hφ =>
    rw [mem_centralBlock]
    intro z
    obtain ⟨n, hn⟩ := Module.End.exists_pow_apply_eq_zero_of_fg
      (T := rep P V (z : 𝓤) - χ z • 1) ((Submodule.fg_iff_finiteDimensional _).mpr (hfin μ))
      (fun v _ ↦ (mem_centralBlock P χ v).mp (hχ ▸ LieSubmodule.mem_top v) z)
    refine ⟨n, TwistedDual.ext fun v ↦ ?_⟩
    rw [toDual_rep_center_sub_pow P hA, LinearMap.comp_apply, map_zero, LinearMap.zero_apply]
    have hv : v ∈ ⨆ ν, weightSpaceOfMap V (h P) ν := hV ▸ Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem ν v hv =>
      by_cases hνμ : μ = ν
      · subst hνμ
        rw [hn v hv, map_zero]
      · exact apply_eq_zero_of_ne hφ (rep_center_sub_pow_mem_weightSpace P z _ n hv) hνμ
    | zero => simp
    | add v w _ _ hv hw => rw [map_add, map_add, hv, hw, add_zero]
  | zero => exact zero_mem _
  | add φ ψ _ _ hφ hψ => exact add_mem hφ hψ

include hA in
/-- The dual of a module in `𝒪` lying in one generalized central block lies in the same block. -/
theorem centralBlock_restrictedDual_eq_top (hV : IsCategoryO P V) {χ : 𝓩 →ₐ[K] K}
    (hχ : centralBlock P V χ = ⊤) : centralBlock P (restrictedDual P V) χ = ⊤ := by
  rw [eq_top_iff]
  rintro φ -
  exact mem_centralBlock_of_injective P (restrictedDual P V).incl Subtype.val_injective χ
    (mem_centralBlock_twistedDual P hA hV.iSup_weightSpaceOfMap_eq_top
      hV.finiteDimensional_weightSpaceOfMap hχ φ.property)

include hA in
/-- A functional in the `χ`-block of `M^∨` kills every other block of `M`. -/
theorem restrictedDual_apply_eq_zero_of_ne (hV : IsCategoryO P V) {χ θ : 𝓩 →ₐ[K] K}
    (hne : θ ≠ χ) {ψ : restrictedDual P V} (hψ : ψ ∈ centralBlock P (restrictedDual P V) χ)
    {v : V} (hv : v ∈ centralBlock P V θ) : TwistedDual.toDual P V ψ.val v = 0 := by
  let r := restrictedDualMap P (centralBlock P V θ).incl
  have h1 : r ψ ∈ centralBlock P _ χ := map_mem_centralBlock P r χ hψ
  have h2 : r ψ ∈ centralBlock P _ θ :=
    (centralBlock_restrictedDual_eq_top P hA (hV.centralBlock P θ)
      (centralBlock_centralBlock_eq_top P θ)) ▸ LieSubmodule.mem_top _
  have h3 : r ψ = 0 := (LieSubmodule.mem_bot _).mp
    ((disjoint_centralBlock P hne.symm).le_bot ((LieSubmodule.mem_inf _ _ _).mpr ⟨h1, h2⟩))
  have := congrArg (fun φ : restrictedDual P (centralBlock P V θ) ↦
    TwistedDual.toDual P _ φ.val ⟨v, hv⟩) h3
  simpa [r] using this

variable [IsAlgClosed K]

/-- **Duality commutes with central blocks**: `(pr_χ M)^∨ ≅ pr_χ (M^∨)` for `M` in `𝒪`, in
finite type over an algebraically closed field of characteristic zero. The map sends `φ` to
`φ ∘ pr_χ`. -/
def restrictedDualCentralBlockEquiv (hV : IsCategoryO P V) (χ : 𝓩 →ₐ[K] K) :
    restrictedDual P (centralBlock P V χ) ≃ₗ⁅K,𝔤⁆ centralBlock P (restrictedDual P V) χ := by
  let hV' := hV.isCentralLocallyFinite P
  let proj : V →ₗ⁅K,𝔤⁆ centralBlock P V χ :=
    (centralBlockProjection P hV' χ).codRestrict _ (centralBlockProjection_mem P hV' χ)
  have htop := centralBlock_restrictedDual_eq_top P hA (hV.centralBlock P χ)
    (centralBlock_centralBlock_eq_top P χ)
  let F : restrictedDual P (centralBlock P V χ) →ₗ⁅K,𝔤⁆
      centralBlock P (restrictedDual P V) χ :=
    (restrictedDualMap P proj).codRestrict _ fun φ ↦
      map_mem_centralBlock P _ χ (htop ▸ LieSubmodule.mem_top φ)
  refine LieModuleEquiv.ofBijective F ⟨fun φ ψ hφψ ↦ ?_, fun ψ ↦
    ⟨restrictedDualMap P (centralBlock P V χ).incl ψ.val, ?_⟩⟩
  · apply restrictedDual_ext P
    intro v
    have := congrArg (fun ξ : centralBlock P (restrictedDual P V) χ ↦
      TwistedDual.toDual P V ξ.val.val v.val) hφψ
    have hv : proj v.val = v := Subtype.ext (centralBlockProjection_self P hV' χ v.property)
    simpa [F, hv] using this
  · apply Subtype.ext
    apply restrictedDual_ext P
    intro v
    change TwistedDual.toDual P V ψ.val.val (centralBlockProjection P hV' χ v) =
      TwistedDual.toDual P V ψ.val.val v
    have hv : v ∈ ⨆ θ, (centralBlock P V θ).toSubmodule := by
      rw [iSup_centralBlock_eq_top P hV']; trivial
    induction hv using Submodule.iSup_induction' with
    | mem θ v hv =>
      by_cases hθ : θ = χ
      · subst hθ
        rw [centralBlockProjection_self P hV' θ hv]
      · rw [centralBlockProjection_other P hV' hθ hv, map_zero,
          restrictedDual_apply_eq_zero_of_ne P hA hV hθ ψ.property hv]
    | zero => simp
    | add v w _ _ hv hw => rw [map_add, map_add, map_add, hv, hw]

end Center

section Translation

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [IsAlgClosed K]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  (P : Realization A K H) (hA : A.IsFiniteCartan)
  {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

local notation "𝔤" => KacMoodyAlgebra P
local notation "𝓤" => UniversalEnvelopingAlgebra K P.KacMoodyAlgebra
local notation "𝓩" => Subalgebra.center K 𝓤

include hA in
/-- `M^∨ ⊗ L(ν) ≅ (M ⊗ L(ν))^∨` for `ν` dominant integral (finite type), using the
contravariant form of `L(ν)`. -/
def restrictedDualTensorIrreducibleEquiv {ν : Dual K H} (hν : P.IsDominantIntegral ν) :
    restrictedDual P V ⊗[K] IrreducibleModule P ν ≃ₗ⁅K,𝔤⁆
      restrictedDual P (V ⊗[K] IrreducibleModule P ν) :=
  have := IrreducibleModule.finiteDimensional (P := P) hA hν
  restrictedDualTensorEquiv P V (IrreducibleModule.contravariantForm P ν)
    (IrreducibleModule.contravariantForm_lie_left P ν)
    (IrreducibleModule.nondegenerate_contravariantForm P ν)
    (IrreducibleModule.isSymm_contravariantForm P ν)
    (IrreducibleModule.isCategoryO P ν).iSup_weightSpaceOfMap_eq_top

include hA in
/-- **Translation commutes with duality** (Humphreys, GSM 94, Proposition 7.1): for `M` in `𝒪`,
`ν` dominant integral and `T = pr_{χ₂}(pr_{χ₁}(−) ⊗ L(ν))`, `(T M)^∨ ≅ T (M^∨)`. -/
def restrictedDualCentralTranslationEquiv {ν : Dual K H} (hν : P.IsDominantIntegral ν)
    (hV : IsCategoryO P V) (χ₁ χ₂ : 𝓩 →ₐ[K] K) :
    restrictedDual P (centralTranslation P (IrreducibleModule P ν) χ₁ χ₂ V) ≃ₗ⁅K,𝔤⁆
      centralTranslation P (IrreducibleModule P ν) χ₁ χ₂ (restrictedDual P V) :=
  (restrictedDualCentralBlockEquiv P hA
      ((hV.centralBlock P χ₁).tensorProduct (IrreducibleModule.isCategoryO P ν)) χ₂).trans
    ((centralBlockEquiv P
      (restrictedDualTensorIrreducibleEquiv P hA (V := centralBlock P V χ₁) hν).symm χ₂).trans
      (centralBlockEquiv P (rTensorEquiv P (IrreducibleModule P ν)
        (restrictedDualCentralBlockEquiv P hA hV χ₁)) χ₂))

end Translation

section DualVerma

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharZero K]
  [IsAlgClosed K] {H : Type*} [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

include hA in
/-- **Translation of dual Verma modules** (Humphreys, GSM 94, Theorem 7.6, dual Verma
part, integral weights, finite type): with `T_λ^μ = pr_{χ_μ}(pr_{χ_λ}(−) ⊗ L(ν))` and the
hypotheses of `translation_verma`, `T_λ^μ M(w·λ)^∨ ≅ M(w·μ)^∨` for every `w ∈ W`, where
`M^∨ = restrictedDual P M` is the duality functor of category `𝒪`. -/
theorem translation_dualVerma {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (restrictedDual P (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ))
      ≃ₗ⁅K,KacMoodyAlgebra P⁆ centralTranslation P (IrreducibleModule P ν)
        (centralCharacter P lam) (centralCharacter P μ)
        (restrictedDual P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam)))) := by
  obtain ⟨e⟩ := translation_verma_equiv P hA hlam hμ hfacet hν hz hzν w
  exact ⟨(restrictedDualEquiv P e).symm.trans
    (restrictedDualCentralTranslationEquiv P hA hν (VermaModule.isCategoryO P _) _ _)⟩

end DualVerma

end Matrix.Realization.KacMoodyAlgebra
