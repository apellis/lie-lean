/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CategoryOInt

/-!
# Splitting off highest weight submodules

Let `M` be an integrable `U_q(𝔤)`-module and `w ∈ M^Λ` a nonzero vector of a maximal weight `Λ`
(`Λ + αᵢ` is not a weight for any `i`). Then `U w ≅ L_q(Λ)` and `U w` is a direct summand of `M`
([HK] Lemma 3.5.3).

## Construction

[HK] use the finite dual of `M` and the irreducibility of the lowest weight module. Here a
functional `φ` on `M`, supported on `M^Λ` with `φ(w) = 1`, is a primitive vector of weight `Λ` in
the dual `M*` with `U` acting through Lusztig's anti-involution `ρ` (`QuantumGroup.RhoDual`); an
`𝔰𝔩₂` argument gives `Fᵢ^{⟨i,Λ⟩+1} φ = 0`, so `v_Λ ↦ φ` defines `ι : L_q(Λ) → M*`. The pairing
`(m, x) ↦ ι(x)(m)` is contravariant, and its adjoint for the contravariant form of `L_q(Λ)` is a
`U`-linear `Π : M → L_q(Λ)`; by Schur's lemma `Π` restricted to `U w` is an isomorphism.

## Main results

* `QuantumGroup.IntegrableSl2.dE_eq_zero_of_E_dE`: for `x ∈ Mⁿ` with `n + b < 0`, if `E^{(b)} x`
  is primitive then `E^{(b)} x = 0`.
* `QuantumGroup.RhoDual`: the dual of a `U`-module, twisted by `ρ`.
* `QuantumGroup.exists_map_eq_hwv_of_maximal`: a `U`-linear map `M → L_q(Λ)` with `w ↦ v_Λ`.
* `QuantumGroup.exists_isCompl_span_of_maximal` ([HK] Lemma 3.5.3): `U w ≅ L_q(Λ)` is a direct
  summand of `M`, and `Λ` is dominant.

The results about `L_q(Λ)` assume `v` transcendental over `ℚ`, `k` of characteristic zero, finitely
many simple roots and an `X`-regular root datum, as in `QuantumGroup.IrreducibleModule.lift`. The
module `M` need not lie in `𝒪_int`: integrability suffices.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §3.5.
-/

open LieLean Finset

noncomputable section

namespace LieLean.QuantumGroup

/-! ### An `𝔰𝔩₂` lemma -/

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M} (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq0 hq

/-- If `x ∈ Mⁿ` with `n + b < 0` and `E^{(b)} x` is primitive, then `E^{(b)} x = 0`. -/
theorem dE_eq_zero_of_E_dE {n : ℤ} {x : M} (hx : x ∈ V.wt n) {b : ℕ} (hnb : n + b < 0)
    (hE : V.E (V.dE b x) = 0) : V.dE b x = 0 := by
  classical
  obtain ⟨N, η, hη, hη0, hN, rfl⟩ := exists_sum_dF hq0 hq hx
  -- `E^{(b)} F^{(b+1+j)} ηⱼ = F^{(j+1)} θⱼ`
  have key : ∀ j : ℕ, ∃ θ : M, θ ∈ V.prim (n + 2 * b + 2 * ((j + 1 : ℕ) : ℤ)) ∧
      V.dE b (V.dF (b + 1 + j) (η (b + 1 + j))) = V.dF (j + 1) θ := by
    intro j
    by_cases h0 : η (b + 1 + j) = 0
    · exact ⟨0, zero_mem _, by simp [h0]⟩
    have hnj := hη0 _ h0
    push_cast at hnj
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * ((b + 1 + j : ℕ) : ℤ) :=
      ⟨_, Int.toNat_of_nonneg (by push_cast; omega)⟩
    have hηp : η (b + 1 + j) ∈ V.prim p := by rw [hp]; exact hη _
    refine ⟨qBinomial q (p - (b + 1 + j) + b) b • η (b + 1 + j), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ ?_
      convert hη (b + 1 + j) using 2
      push_cast
      ring
    · rw [dE_dF_of_primitive hq0 hq hηp.1 hηp.2 (by omega) (by push_cast at hp; omega),
        map_smul, show b + 1 + j - b = j + 1 by omega]
  choose θ hθ hθe using key
  have hsplit : ∑ j ∈ range N, V.dF j (η j) =
      ∑ j ∈ range (b + 1), V.dF j (η j) + ∑ j ∈ range N, V.dF (b + 1 + j) (η (b + 1 + j)) := by
    rw [← sum_range_add]
    refine sum_subset (fun j hj ↦ mem_range.2 (by have := mem_range.1 hj; omega))
      fun j _ hj ↦ ?_
    rw [hN j (by simpa using hj), map_zero]
  have hlow : ∑ j ∈ range (b + 1), V.dF j (η j) = 0 := by
    refine sum_eq_zero fun j hj ↦ ?_
    by_cases h0 : η j = 0
    · rw [h0, map_zero]
    · have := hη0 j h0
      have := mem_range.1 hj
      omega
  set y := V.dE b (∑ j ∈ range N, V.dF j (η j))
  have hy : y = ∑ j ∈ range N, V.dF (j + 1) (θ j) := by
    rw [show y = V.dE b (∑ j ∈ range N, V.dF j (η j)) from rfl, hsplit, hlow, zero_add, map_sum]
    exact sum_congr rfl fun j _ ↦ hθe j
  set η' : ℕ → M := fun j ↦ Nat.casesOn j (-y) θ
  have hη' : ∀ j : ℕ, η' j ∈ V.prim (n + 2 * b + 2 * j) := by
    rintro (_ | j)
    · refine ⟨?_, ?_⟩
      · rw [Nat.cast_zero, mul_zero, add_zero]
        exact neg_mem (dE_mem hx b)
      · change V.E (-y) = 0
        rw [map_neg, hE, neg_zero]
    · exact hθ j
  have hsum : ∑ j ∈ range (N + 1), V.dF j (η' j) = 0 := by
    rw [sum_range_succ']
    change ∑ j ∈ range N, V.dF (j + 1) (θ j) + V.dF 0 (-y) = 0
    rw [← hy, dF_zero, add_neg_cancel]
  have := dF_eq_zero_of_sum_range_eq_zero hq0 hq (N + 1) (n + 2 * b) η' hη' hsum 0
    (Nat.succ_pos N)
  have h0 : V.dF 0 (-y) = 0 := this
  rw [dF_zero, neg_eq_zero] at h0
  exact h0

end IntegrableSl2

/-- The dual `M* = Hom_k(M, k)` of a `U`-module, with `U` acting through Lusztig's
anti-involution `ρ`: `(u f)(m) = f(ρ(u) m)`. -/
@[nolint unusedArguments]
def RhoDual {k I Y : Type*} [Field k] [AddCommGroup Y] {D : LusztigCartanDatum I}
    (_R : D.RootDatum Y) (_v : k) (M : Type*) [AddCommGroup M] [Module k M] : Type _ :=
  Module.Dual k M

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-! ### The `ρ`-twisted dual -/

namespace RhoDual

instance : AddCommGroup (RhoDual R v M) := inferInstanceAs (AddCommGroup (Module.Dual k M))

instance : Module k (RhoDual R v M) := inferInstanceAs (Module k (Module.Dual k M))

/-- The identification of `RhoDual R v M` with `Module.Dual k M`. -/
def toDual : RhoDual R v M ≃ₗ[k] Module.Dual k M := LinearEquiv.refl k _

instance : SMul (QuantumGroup R v) (RhoDual R v M) where
  smul u f := toDual.symm (toDual f ∘ₗ Algebra.lsmul k k M (rho R v u))

lemma toDual_smul (u : QuantumGroup R v) (f : RhoDual R v M) (m : M) :
    toDual (u • f) m = toDual f (rho R v u • m) := rfl

omit [DecidableEq I] [NeZero v] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] in
lemma ext {f g : RhoDual R v M} (h : ∀ m, toDual f m = toDual g m) : f = g :=
  toDual.injective (LinearMap.ext h)

instance : Module (QuantumGroup R v) (RhoDual R v M) where
  one_smul f := ext fun m ↦ by rw [toDual_smul, rho_one, one_smul]
  mul_smul x y f := ext fun m ↦ by rw [toDual_smul, toDual_smul, toDual_smul, rho_mul, mul_smul]
  smul_zero u := ext fun m ↦ by rw [toDual_smul]; rfl
  smul_add u f g := ext fun m ↦ by rw [toDual_smul, map_add, map_add, LinearMap.add_apply,
    LinearMap.add_apply, toDual_smul, toDual_smul]
  add_smul x y f := ext fun m ↦ by rw [toDual_smul, map_add, add_smul, map_add, map_add,
    LinearMap.add_apply, toDual_smul, toDual_smul]
  zero_smul f := ext fun m ↦ by rw [toDual_smul, map_zero, zero_smul, map_zero, map_zero]; rfl

instance : IsScalarTower k (QuantumGroup R v) (RhoDual R v M) where
  smul_assoc c u f := ext fun m ↦ by
    change toDual f (rho R v (c • u) • m) = c • toDual f (rho R v u • m)
    rw [map_smul (rho R v), smul_assoc, map_smul]

end RhoDual

/-! ### A primitive functional -/

section Functional

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M)

/-- `ρ(Fᵢ)^n m` is a multiple of `Eᵢ^n m` for a weight vector `m`. -/
lemma exists_rhoF_pow_smul {μ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M μ) (i : I)
    (n : ℕ) : ∃ c : k, rhoF R v i ^ n • m = c • (E R v i ^ n • m) := by
  induction n generalizing μ m with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih (E_smul_mem_weightSpace hm i)
    have h1 : rhoF R v i • m =
        (v ^ D.d i * (v ^ D.d i) ^ (-((μ + R.root i) (R.coroot i)))) • E R v i • m := by
      rw [rhoF, smul_assoc, mul_smul,
        K_neg_ktilde_smul_of_mem_weightSpace (E_smul_mem_weightSpace hm i), smul_smul]
    refine ⟨(v ^ D.d i * (v ^ D.d i) ^ (-((μ + R.root i) (R.coroot i)))) * c, ?_⟩
    rw [pow_succ, mul_smul, h1, smul_comm (rhoF R v i ^ n), hc, ← mul_smul (E R v i ^ n),
      ← pow_succ, smul_smul]

/-- The functional `g ∘ pr_Λ` on `M`, for `g` a functional on `M^Λ`. -/
def weightSpaceFunctional {Λ : Y →+ ℤ} (g : Module.Dual k (weightSpace R v M Λ)) : RhoDual R v M :=
  RhoDual.toDual.symm (g ∘ₗ (weightSetProj hv' hM {Λ}).codRestrict _
    (weightSetProj_singleton_mem hv' hM Λ))

variable {Λ : Y →+ ℤ} (g : Module.Dual k (weightSpace R v M Λ))

lemma weightSpaceFunctional_of_mem {m : M} (hm : m ∈ weightSpace R v M Λ) :
    RhoDual.toDual (weightSpaceFunctional hv' hM g) m = g ⟨m, hm⟩ := by
  simp only [weightSpaceFunctional, LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
  congr 1
  exact Subtype.ext (weightSetProj_singleton_of_mem hv' hM hm)

lemma weightSpaceFunctional_of_ne {Λ' : Y →+ ℤ} (h : Λ' ≠ Λ) {m : M}
    (hm : m ∈ weightSpace R v M Λ') : RhoDual.toDual (weightSpaceFunctional hv' hM g) m = 0 := by
  classical
  simp only [weightSpaceFunctional, LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
  have : (weightSetProj hv' hM {Λ}).codRestrict _ (weightSetProj_singleton_mem hv' hM Λ) m =
      0 := Subtype.ext (by simp [weightSetProj_of_mem hv' hM _ hm, h])
  rw [this, map_zero]

lemma K_smul_weightSpaceFunctional (μ : Y) :
    K R v μ • weightSpaceFunctional hv' hM g = v ^ Λ μ • weightSpaceFunctional hv' hM g := by
  have := ext_weightSpace hM (f := RhoDual.toDual (K R v μ • weightSpaceFunctional hv' hM g))
    (g := RhoDual.toDual (v ^ Λ μ • weightSpaceFunctional hv' hM g)) fun Λ' m hm ↦ by
      rw [RhoDual.toDual_smul, rho_K, hm μ, map_smul, map_smul, LinearMap.smul_apply]
      by_cases h : Λ' = Λ
      · subst h; rfl
      · rw [weightSpaceFunctional_of_ne hv' hM g h hm, smul_zero, smul_zero]
  exact RhoDual.toDual.injective this

variable (hmax : ∀ i, weightSpace R v M (Λ + R.root i) = ⊥)
include hmax

lemma E_smul_weightSpaceFunctional (i : I) : E R v i • weightSpaceFunctional hv' hM g = 0 := by
  refine RhoDual.toDual.injective (ext_weightSpace hM fun Λ' m hm ↦ ?_)
  rw [RhoDual.toDual_smul, rho_E, rhoE, smul_assoc, mul_smul, map_zero, LinearMap.zero_apply]
  have hF := F_smul_mem_weightSpace hm i
  by_cases h : Λ' - R.root i = Λ
  · have : m ∈ weightSpace R v M (Λ + R.root i) := by rw [← h, sub_add_cancel]; exact hm
    rw [hmax i, Submodule.mem_bot] at this
    simp [this]
  · rw [map_smul, Kt_smul_of_mem_weightSpace hF, map_smul,
      weightSpaceFunctional_of_ne hv' hM g h hF, smul_zero, smul_zero]

include hv' in
lemma F_pow_smul_weightSpaceFunctional (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) (i : I) :
    F R v i ^ ((Λ (R.coroot i)).toNat + 1) • weightSpaceFunctional hv' hM g = 0 := by
  set b := (Λ (R.coroot i)).toNat + 1
  have rho_pow : ∀ (x : QuantumGroup R v) (n : ℕ), rho R v (x ^ n) = rho R v x ^ n := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, rho_mul, ih, pow_succ']
  refine RhoDual.toDual.injective (ext_weightSpace hM fun Λ' m hm ↦ ?_)
  rw [RhoDual.toDual_smul, rho_pow, rho_F, map_zero, LinearMap.zero_apply]
  obtain ⟨c, hc⟩ := exists_rhoF_pow_smul hm i b
  set V := nodeSl2 R v M hv' hM i
  have hEb : E R v i ^ b • m = qFactorial (v ^ D.d i) b • V.dE b m := by
    rw [IntegrableSl2.dE_apply, smul_smul,
      mul_inv_cancel₀ (qFactorial_ne_zero_of_pow_ne_one (pow_d_ne_zero i) (pow_d_ne_one hv' i) b),
      one_smul, nodeSl2_E, ← map_pow, Algebra.lsmul_apply]
  have hmem := nodeSl2_dE_mem_weightSpace hv' hM i hm b
  rw [hc, hEb, map_smul, map_smul]
  by_cases h : Λ' + (b : ℤ) • R.root i = Λ
  · have hroot : R.root i (R.coroot i) = 2 := by rw [R.root_coroot, D.cartanMatrix_self]
    have h0 : V.dE b m = 0 := by
      refine IntegrableSl2.dE_eq_zero_of_E_dE (pow_d_ne_zero i) (pow_d_ne_one hv' i)
        (mem_nodeWt_of_mem hm) (b := b) ?_ ?_
      · have := congrArg (fun μ : Y →+ ℤ ↦ μ (R.coroot i)) h
        simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, hroot, smul_eq_mul] at this
        have hb : (b : ℤ) = Λ (R.coroot i) + 1 := by
          simp only [b]; push_cast; rw [Int.toNat_of_nonneg (hΛ i)]
        omega
      · rw [h] at hmem
        have := E_smul_mem_weightSpace hmem i
        rw [hmax i, Submodule.mem_bot] at this
        rw [nodeSl2_E]
        exact this
    rw [h0, map_zero, smul_zero, smul_zero]
  · rw [weightSpaceFunctional_of_ne hv' hM g h hmem, smul_zero, smul_zero]

end Functional

/-! ### The splitting -/

section Splitting

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) [Finite I] [CharZero k]
  (hvt : Transcendental ℚ v) (hR : R.IsXRegular) (hM : IsIntegrable R v M) {Λ : Y →+ ℤ}
  (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) (g : Module.Dual k (weightSpace R v M Λ))
  (hmax : ∀ i, weightSpace R v M (Λ + R.root i) = ⊥)

/-- The map `L_q(Λ) → M*`, `v_Λ ↦ g ∘ pr_Λ`. -/
def dualEmb : IrreducibleModule R v Λ →ₗ[QuantumGroup R v] RhoDual R v M :=
  IrreducibleModule.liftOfFPow hvt hR hv' hΛ (weightSpaceFunctional hv' hM g)
    (fun μ ↦ K_smul_weightSpaceFunctional hv' hM g μ) (E_smul_weightSpaceFunctional hv' hM g hmax)
    (F_pow_smul_weightSpaceFunctional hv' hM g hmax hΛ)

lemma dualEmb_hwv :
    dualEmb hv' hvt hR hM hΛ g hmax (IrreducibleModule.hwv R v Λ) =
      weightSpaceFunctional hv' hM g :=
  IrreducibleModule.liftOfFPow_hwv _ _ _ _ _ _ _ _

/-- The pairing `M × L_q(Λ) → k`, `(m, x) ↦ ι(x)(m)`. -/
def dualPairing : M →ₗ[k] IrreducibleModule R v Λ →ₗ[k] k :=
  (RhoDual.toDual.toLinearMap ∘ₗ (dualEmb hv' hvt hR hM hΛ g hmax).restrictScalars k).flip

lemma isContravariantPairing_dualPairing :
    IsContravariantPairing R v (dualPairing hv' hvt hR hM hΛ g hmax) := fun u m x ↦ by
  simp only [dualPairing, LinearMap.flip_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, map_smul, RhoDual.toDual_smul,
    rho_rho]

/-- The `U`-linear map `Π : M → L_q(Λ)`, adjoint to `ι : L_q(Λ) → M*`. -/
def dualProj : M →ₗ[QuantumGroup R v] IrreducibleModule R v Λ :=
  adjointHom hv' (IrreducibleModule.isGoodForm_form hR hv' hΛ) hM
    (isContravariantPairing_dualPairing hv' hvt hR hM hΛ g hmax)

lemma form_dualProj (m : M) (x : IrreducibleModule R v Λ) :
    IrreducibleModule.form Λ hR hv' (dualProj hv' hvt hR hM hΛ g hmax m) x =
      RhoDual.toDual (dualEmb hv' hvt hR hM hΛ g hmax x) m :=
  form_adjoint _ hM (isContravariantPairing_dualPairing hv' hvt hR hM hΛ g hmax) m x

include hv' hvt hR hM hmax in
/-- A `U`-linear map `M → L_q(Λ)` sending a nonzero vector `w` of a maximal weight `Λ` to `v_Λ`
(the main step of [HK] Lemma 3.5.3). -/
theorem exists_map_eq_hwv_of_maximal {w : M} (hw : w ∈ weightSpace R v M Λ) (hw0 : w ≠ 0) :
    (∀ i, 0 ≤ Λ (R.coroot i)) ∧ ∃ π : M →ₗ[QuantumGroup R v] IrreducibleModule R v Λ,
      π w = IrreducibleModule.hwv R v Λ := by
  have hE : ∀ i, E R v i • w = 0 := fun i ↦ by
    have := E_smul_mem_weightSpace hw i
    rwa [hmax i, Submodule.mem_bot] at this
  have hΛ := dominant_of_primitive hv' hM hw hw0 hE
  refine ⟨hΛ, ?_⟩
  have := IrreducibleModule.isSimpleModule hR hv' Λ
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one k (x := (⟨w, hw⟩ : weightSpace R v M Λ))
    (by simpa using hw0)
  set j := IrreducibleModule.lift hvt hR hv' hΛ hM w hw hE
  set P := dualProj hv' hvt hR hM hΛ g hmax
  have h1 : IrreducibleModule.form Λ hR hv' (P w) (IrreducibleModule.hwv R v Λ) = 1 := by
    rw [form_dualProj, dualEmb_hwv, weightSpaceFunctional_of_mem hv' hM g hw, hg]
  have hne : P ∘ₗ j ≠ 0 := fun h ↦ by
    have e := LinearMap.congr_fun h (IrreducibleModule.hwv R v Λ)
    rw [LinearMap.comp_apply, IrreducibleModule.lift_hwv, LinearMap.zero_apply] at e
    rw [e, map_zero, LinearMap.zero_apply] at h1
    exact zero_ne_one h1
  set e := LinearEquiv.ofBijective (P ∘ₗ j) (LinearMap.bijective_of_ne_zero hne)
  refine ⟨e.symm.toLinearMap ∘ₗ P, ?_⟩
  have hjw : w = j (IrreducibleModule.hwv R v Λ) := (IrreducibleModule.lift_hwv ..).symm
  rw [LinearMap.comp_apply, hjw]
  exact e.symm_apply_apply _

include hv' hvt hR hM hmax in
/-- **[HK] Lemma 3.5.3.** Let `M` be an integrable `U`-module and `w ∈ M^Λ` nonzero with `Λ`
maximal (`M^{Λ + αᵢ} = 0` for all `i`). Then `Λ` is dominant, `U w ≅ L_q(Λ)`, and `U w` has a
complement in `M`. ([HK] state this for `M` in `𝒪_int`.) -/
theorem exists_isCompl_span_of_maximal {w : M} (hw : w ∈ weightSpace R v M Λ) (hw0 : w ≠ 0) :
    (∀ i, 0 ≤ Λ (R.coroot i)) ∧
      Nonempty (IrreducibleModule R v Λ ≃ₗ[QuantumGroup R v]
        Submodule.span (QuantumGroup R v) {w}) ∧
      ∃ N : Submodule (QuantumGroup R v) M, IsCompl (Submodule.span (QuantumGroup R v) {w}) N := by
  obtain ⟨hΛ, π, hπ⟩ := exists_map_eq_hwv_of_maximal hv' hvt hR hM hmax hw hw0
  have hE : ∀ i, E R v i • w = 0 := fun i ↦ by
    have := E_smul_mem_weightSpace hw i
    rwa [hmax i, Submodule.mem_bot] at this
  have := IrreducibleModule.isSimpleModule hR hv' Λ
  set j := IrreducibleModule.lift hvt hR hv' hΛ hM w hw hE
  have hjw : j (IrreducibleModule.hwv R v Λ) = w := IrreducibleModule.lift_hwv ..
  -- `π ∘ j = 1`, since both are `U`-linear and fix the generator `v_Λ`
  have htop : Submodule.span (QuantumGroup R v) {IrreducibleModule.hwv R v Λ} = ⊤ := by
    refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun h ↦ hw0 ?_
    rw [Submodule.span_singleton_eq_bot.1 h, map_zero] at hjw
    exact hjw.symm
  have hπj : ∀ x, π (j x) = x := by
    have h : π ∘ₗ j = LinearMap.id := LinearMap.ext_on htop (by
      rintro _ rfl
      simp [hjw, hπ])
    exact fun x ↦ LinearMap.congr_fun h x
  have hrange : LinearMap.range j = Submodule.span (QuantumGroup R v) {w} := by
    rw [LinearMap.range_eq_map, ← htop, Submodule.map_span, Set.image_singleton, hjw]
  have hinj : Function.Injective j := fun x y h ↦ by rw [← hπj x, h, hπj]
  refine ⟨hΛ, ⟨(LinearEquiv.ofInjective j hinj).trans (LinearEquiv.ofEq _ _ hrange)⟩, ?_⟩
  refine ⟨LinearMap.ker (j.rangeRestrict ∘ₗ π), ?_⟩
  rw [← hrange]
  refine LinearMap.isCompl_of_proj fun ⟨x, y, hy⟩ ↦ ?_
  subst hy
  exact Subtype.ext (by simp [hπj])

end Splitting

end LieLean.QuantumGroup
