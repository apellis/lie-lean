/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.NegativeIntegralGrading
import LieLean.Algebra.QuantumGroup.Character

/-!
# Bar involution and `ℤ`-form of `V(λ)`

For `λ` dominant, Kashiwara's construction of the global basis of `V(λ)` ([Kas91] §6.1, §7) uses
the `𝒜`-form `V_ℤ(λ) = U⁻_ℤ u_λ` ([Kas91] (6.1.12)) and the bar involution
`(P u_λ)‾ = P̄ u_λ` of `V(λ)` ([Kas91] (6.1.15)). We construct both on the library's model
`L_q(λ) = IrreducibleModule R 𝕧 λ` over `𝕂 = ℚ(v)`:

* `ker_ev_eq`: the kernel of `y ↦ y⁻ v_λ`, `'f → L_q(λ)`, is `J + Σᵢ 'f θᵢ^{⟨i,λ⟩+1}`
  (`evKernel`), from the description of the maximal submodule of the Verma module;
* `evKernel_le_comap_bar`: this kernel is stable under the bar involution of `'f`;
* `hwBar`: the bar involution of `L_q(λ)`, with `hwBar_ev` (`(y⁻ v_λ)‾ = ȳ⁻ v_λ`),
  `hwBar_evq`, `hwBar_hwBar` and `hwBar_smul`;
* `hwIntegral`: `V_ℤ(λ)`, the image of `U⁻_ℤ`, and `hwBar_mem_hwIntegral` (it is bar-stable,
  as stated after [Kas91] (6.1.15)).

As in the grand loop, the root datum is `X`-regular (`R.IsXRegular`); the kernel description
uses quantum target 2 (`VermaModule.maxSubmodule_eq_fPowSubmodule` and its proof).

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), 465–516, §6.1.
-/

open Finset LusztigF FreeAlgebra

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop Sl2.RankOne

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X
local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (hR : R.IsXRegular)

lemma hvn_ratFunc : ∀ n : ℕ, 0 < n → 𝕧 ^ n ≠ 1 := fun _ hn ↦
  pow_ne_one_of_transcendental transcendental_ratFunc_X hn

/-! ### The kernel of `y ↦ y⁻ v_λ` -/

variable (D) in
/-- `J + Σᵢ 'f θᵢ^{nᵢ+1}`, as a subspace of `'f`. -/
def evKernel (n : I → ℕ) : Submodule 𝕂 (LusztigF 𝕂 I) :=
  serreSubmodule D 𝕧 ⊔ Submodule.span 𝕂 (Set.range fun g ↦ wordBasis 𝕂 I (powWord n g))

omit [Finite I] [DecidableEq I] in
lemma bar_monomial (w : List I) : LusztigF.bar (monomial 𝕂 w) = monomial 𝕂 w := by
  induction w with
  | nil => simp [monomial]
  | cons i w ih =>
    simp only [monomial, List.map_cons, List.prod_cons] at ih ⊢
    rw [map_mul, bar_θ, ih]

omit [Finite I] [DecidableEq I] in
/-- The subspace `J + Σᵢ 'f θᵢ^{nᵢ+1}` is stable under bar. -/
theorem evKernel_le_comap_bar (n : I → ℕ) :
    evKernel D n ≤ (evKernel D n).comap (freeBarSL (I := I)) := by
  unfold evKernel
  refine sup_le ((serreSubmodule_le_comap_freeBarSL D).trans
    (Submodule.comap_mono le_sup_left)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  refine Submodule.mem_sup_right (Submodule.subset_span ⟨g, ?_⟩)
  show wordBasis 𝕂 I (powWord n g) = LusztigF.bar (wordBasis 𝕂 I (powWord n g))
  rw [← monomial_eq_wordBasis, bar_monomial]

variable {R} (Λ : Dom R)

include hR in
/-- The kernel of `y ↦ y⁻ v_λ` is `J + Σᵢ 'f θᵢ^{⟨i,λ⟩+1}`. -/
theorem ker_ev_eq :
    LinearMap.ker (ev R 𝕧 Λ.1) = evKernel D (fun i ↦ (Λ.1 (R.coroot i)).toNat) := by
  have hle : ∀ ν, tildeSpan D (fun i ↦ 𝕧 ^ D.d i) (fun i ↦ (Λ.1 (R.coroot i)).toNat) ν ≤
      evKernel D (fun i ↦ (Λ.1 (R.coroot i)).toNat) := fun ν ↦ by
    unfold evKernel
    refine sup_le (fun y hy ↦ Submodule.mem_sup_left ?_) (fun y hy ↦ Submodule.mem_sup_right ?_)
    · rw [mem_serreSubmodule]
      exact serreSpan_le_serreIdeal D (NeZero.ne _) hvn_ratFunc hy
    · refine Submodule.span_mono ?_ hy
      rintro _ ⟨g, -, rfl⟩
      exact ⟨g, rfl⟩
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker, ev_apply, Submodule.Quotient.mk_eq_zero,
      VermaModule.toVerma_mem_maxSubmodule_iff hvn_ratFunc hR] at hy
    rw [← sum_weightProj y]
    refine Submodule.sum_mem _ fun ν _ ↦ hle ν ?_
    refine (VermaModule.shapovalovMap_eq_zero_iff_mem_tildeSpan hvt hR Λ.2
      (FreeAlgebra.weightProj_mem ν y)).1 ?_
    rw [shapovalovMap_eq_zero_iff _ (FreeAlgebra.weightProj_mem ν y)]
    intro w
    rw [vermaForm_weightProj, hy w, ite_self]
  · refine sup_le (fun y hy ↦ ?_) ?_
    · exact ev_eq_zero_of_mem (R := R) hvn_ratFunc Λ.1 (mem_serreSubmodule.1 hy)
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ev_apply, Submodule.Quotient.mk_eq_zero]
    refine VermaModule.fPowSubmodule_le_maxSubmodule hR hvn_ratFunc Λ.2
      (VermaModule.toVerma_mem_fPowSubmodule hvn_ratFunc 
        (ν := wordWeight (powWord (fun i ↦ (Λ.1 (R.coroot i)).toNat) g)) ?_)
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨g, rfl, rfl⟩)

/-! ### The bar involution of `V(λ)` -/

omit [Finite I] in
lemma ev_surjective : Function.Surjective (ev R 𝕧 Λ.1) :=
  (Submodule.mkQ_surjective _).comp (VermaModule.toVerma_surjective hvn_ratFunc)

include hR in
/-- The bar involution of `L_q(λ)`: `(y⁻ v_λ)‾ = ȳ⁻ v_λ` ([Kas91] (6.1.15)). -/
def hwBar : IrreducibleModule R 𝕧 Λ.1 →ₛₗ[barRingHom] IrreducibleModule R 𝕧 Λ.1 :=
  ((ev R 𝕧 Λ.1).quotKerEquivOfSurjective (ev_surjective Λ)).toLinearMap ∘ₛₗ
    ((LinearMap.ker (ev R 𝕧 Λ.1)).mapQ (LinearMap.ker (ev R 𝕧 Λ.1)) freeBarSL
      (by rw [ker_ev_eq hR]; exact evKernel_le_comap_bar _)) ∘ₛₗ
    ((ev R 𝕧 Λ.1).quotKerEquivOfSurjective (ev_surjective Λ)).symm.toLinearMap

theorem hwBar_ev (y : LusztigF 𝕂 I) : hwBar hR Λ (ev R 𝕧 Λ.1 y) = ev R 𝕧 Λ.1 (LusztigF.bar y) := by
  have h : ((ev R 𝕧 Λ.1).quotKerEquivOfSurjective (ev_surjective Λ)).symm (ev R 𝕧 Λ.1 y) =
      Submodule.Quotient.mk y :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp only [hwBar, LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.mapQ_apply]
  rfl

theorem hwBar_evq (x : Um D 𝕧) : hwBar hR Λ (evq hvt Λ x) = evq hvt Λ (negBar D x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact hwBar_ev hR Λ y

@[simp] theorem hwBar_hwBar (m : IrreducibleModule R 𝕧 Λ.1) : hwBar hR Λ (hwBar hR Λ m) = m := by
  obtain ⟨y, rfl⟩ := ev_surjective Λ m
  rw [hwBar_ev, hwBar_ev, LusztigF.bar_bar]

theorem hwBar_smul (c : 𝕂) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwBar hR Λ (c • m) = RatFunc.bar c • hwBar hR Λ m :=
  (hwBar hR Λ).map_smulₛₗ c m

theorem hwBar_hwv : hwBar hR Λ (IrreducibleModule.hwv R 𝕧 Λ.1) = IrreducibleModule.hwv R 𝕧 Λ.1 := by
  rw [← ev_one, hwBar_ev, map_one]

/-! ### The `ℤ`-form `V_ℤ(λ)` -/

/-- `𝒜 = ℤ[v, v⁻¹]` acts on `L_q(λ)` through `v ↦ X`. -/
instance hwLaurentModule : Module (LaurentPolynomial ℤ) (IrreducibleModule R 𝕧 Λ.1) :=
  Module.compHom _ integralLaurentEval

omit [Finite I] in
lemma hw_laurent_smul_eq (c : LaurentPolynomial ℤ) (m : IrreducibleModule R 𝕧 Λ.1) :
    c • m = integralLaurentEval c • m := rfl

/-- `V_ℤ(λ) = U⁻_ℤ u_λ` ([Kas91] (6.1.12)). -/
def hwIntegral : Submodule (LaurentPolynomial ℤ) (IrreducibleModule R 𝕧 Λ.1) where
  carrier := evq hvt Λ '' (negIntegral D : Set (Um D 𝕧))
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, add_mem hx hy, map_add _ _ _⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨c • x, Submodule.smul_mem _ c hx, ?_⟩
    rw [laurent_smul_eq, map_smul, hw_laurent_smul_eq]

lemma mem_hwIntegral (m : IrreducibleModule R 𝕧 Λ.1) :
    m ∈ hwIntegral Λ ↔ ∃ x ∈ negIntegral D, evq hvt Λ x = m := Iff.rfl

/-- `V_ℤ(λ)` is bar-stable. -/
theorem hwBar_mem_hwIntegral {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwIntegral Λ) :
    hwBar hR Λ m ∈ hwIntegral Λ := by
  obtain ⟨x, hx, rfl⟩ := hm
  exact ⟨negBar D x, negBar_mem_negIntegral D hx, (hwBar_evq hR Λ x).symm⟩

end LieLean.QuantumGroup
