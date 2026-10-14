/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.Form
import LieLean.Algebra.QuantumGroup.Modified.RightModule
import LieLean.Algebra.QuantumGroup.RhoBar

/-!
# Right invariance of the form on `U̇`

([Lus] 26.1.3) `(x u, y) = (x, y ρ̄(u))` for `x, y ∈ U̇`, `u ∈ U`.

## Main results

* `QuantumGroup.formFunctional_rho_E_mul`: `P_{ζ-αᵢ}(ρ(Eᵢ) u) = P_ζ(u ρ̄(Eᵢ))`, the identity
  (a) in the proof of [Lus] 26.1.3, via [Lus] 1.2.13 (a) and 3.1.6.
* `QuantumGroup.Modified.form_rightAct_left`: [Lus] 26.1.3, `(x u, y) = (x, y ρ̄(u))`. The
  generators `Eᵢ` and `K_μ` are checked on the functionals `P_ζ`; `Fᵢ = ρ̄(ρ̄(Fᵢ))` follows from
  symmetry of the form ([Lus] 26.1.2 (d)).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 1.2.13, 3.1.6, 26.1.3.
-/

open LieLean LusztigF

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

lemma K_mul_plusHom_of_mem {μ : I →₀ ℕ} {x : LusztigF k I} (hx : x ∈ LusztigF.weightSpace k μ)
    (l : Y) :
    K R v l * plusHom R v x = v ^ R.rootSum μ l • (plusHom R v x * K R v l) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [plusHom_monomial_mem_adWeightSpace w l, wordChar_eq_rootSum, hw]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, mul_add, hx, hy, add_mul, smul_add]
  | smul c x _ hx => rw [map_smul, mul_smul_comm, hx, smul_mul_assoc, smul_comm]

/-- The commutator of `Fᵢ` with `x⁺` ([Lus] 3.1.6). -/
lemma F_mul_plusHom (i : I) (x : LusztigF k I) :
    F R v i * plusHom R v x = plusHom R v x * F R v i -
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (plusHom R v (rDeriv D v i x) * K R v (ktilde R i) -
        K R v (-ktilde R i) * plusHom R v (lDeriv D v i x)) := by
  have h : plusHom R v x * F R v i - F R v i * plusHom R v x =
      (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ • (plusHom R v (rDeriv D v i x) * K R v (ktilde R i) -
        K R v (-ktilde R i) * plusHom R v (lDeriv D v i x)) :=
    (relations R v).toPreRelations.lift_mul_sub (NeZero.ne v) i x
  rw [← h]
  abel

section Functional

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv

/-- The identity (a) in the proof of [Lus] 26.1.3, on `x⁺ K_μ θ_{w'}⁻`, for `x` of weight `ν' + i`
or with `rᵢ(x) = ᵢr(x) = 0`. -/
lemma formFunctional_rho_E_mul_aux (ζ : Y →+ ℤ) (i : I) {μx ν' : I →₀ ℕ} {x : LusztigF k I}
    (hx : x ∈ LusztigF.weightSpace k μx) (hr : rDeriv D v i x ∈ LusztigF.weightSpace k ν')
    (hl : rev k I (lDeriv D v i x) ∈ LusztigF.weightSpace k ν')
    (hμ : μx = ν' + Finsupp.single i 1 ∨ (rDeriv D v i x = 0 ∧ lDeriv D v i x = 0))
    (μ : Y) (w' : List I) :
    formFunctional R v hv (ζ - R.root i)
        (rho R v (E R v i) * (plusHom R v x * K R v μ * minusHom R v (monomial k w'))) =
      formFunctional R v hv ζ
        (plusHom R v x * K R v μ * minusHom R v (monomial k w') * rhoBar R v (E R v i)) := by
  have hv0 := NeZero.ne v
  -- expansion of the left side
  have hFZ : ∀ Z : QuantumGroup R v, F R v i * (plusHom R v x * Z) =
      plusHom R v x * (F R v i * Z) - (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ •
        (plusHom R v (rDeriv D v i x) * (K R v (ktilde R i) * Z) -
          K R v (-ktilde R i) * (plusHom R v (lDeriv D v i x) * Z)) := fun Z ↦ by
    rw [← mul_assoc, F_mul_plusHom, sub_mul, smul_mul_assoc, sub_mul]
    simp only [mul_assoc]
  have hexp : rho R v (E R v i) * (plusHom R v x * K R v μ * minusHom R v (monomial k w')) =
      v ^ D.d i • (K R v (ktilde R i) *
        (plusHom R v x * (F R v i * (K R v μ * minusHom R v (monomial k w'))))) -
      (v ^ D.d i * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹) • (K R v (ktilde R i) *
        (plusHom R v (rDeriv D v i x) * (K R v (ktilde R i) *
          (K R v μ * minusHom R v (monomial k w'))))) +
      (v ^ D.d i * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹) • (K R v (ktilde R i) *
        (K R v (-ktilde R i) * (plusHom R v (lDeriv D v i x) *
          (K R v μ * minusHom R v (monomial k w'))))) := by
    rw [rho_E, rhoE, Kt, smul_mul_assoc]
    simp only [mul_assoc]
    rw [hFZ]
    simp only [mul_sub, mul_smul_comm, smul_sub, smul_smul]
    abel
  have hA : K R v (ktilde R i) *
      (plusHom R v x * (F R v i * (K R v μ * minusHom R v (monomial k w')))) =
      (v ^ R.rootSum μx (ktilde R i) * v ^ R.root i μ) •
        (plusHom R v x * K R v (ktilde R i + μ) * minusHom R v (monomial k (i :: w'))) := by
    rw [← mul_assoc, K_mul_plusHom_of_mem hx, smul_mul_assoc, ← mul_assoc (F R v i),
      F_mul_K hv0, smul_mul_assoc, mul_smul_comm, smul_smul, monomial_cons,
      map_mul, minusHom_θ, ← K_add]
    simp only [mul_assoc]
  have hB : K R v (ktilde R i) * (plusHom R v (rDeriv D v i x) *
      (K R v (ktilde R i) * (K R v μ * minusHom R v (monomial k w')))) =
      v ^ R.rootSum ν' (ktilde R i) • (plusHom R v (rDeriv D v i x) *
        K R v (ktilde R i + (ktilde R i + μ)) * minusHom R v (monomial k w')) := by
    rw [← mul_assoc, K_mul_plusHom_of_mem hr, smul_mul_assoc, ← K_add, ← K_add]
    simp only [mul_assoc]
  have hC : K R v (ktilde R i) * (K R v (-ktilde R i) * (plusHom R v (lDeriv D v i x) *
      (K R v μ * minusHom R v (monomial k w')))) =
      plusHom R v (lDeriv D v i x) * K R v μ * minusHom R v (monomial k w') := by
    rw [← mul_assoc, K_add, add_neg_cancel, K_zero, one_mul]
    simp only [mul_assoc]
  -- the right side
  have hRt : plusHom R v x * K R v μ * minusHom R v (monomial k w') * rhoBar R v (E R v i) =
      ((v ^ D.d i)⁻¹ * v ^ R.rootSum (wordWeight w') (-ktilde R i)) •
        (plusHom R v x * K R v (μ + -ktilde R i) *
          minusHom R v (monomial k (w' ++ [i]))) := by
    rw [rhoBar_E, rhoBarE, mul_smul_comm, ← mul_assoc, mul_assoc _ (minusHom R v _),
      minusHom_monomial_mul_K, mul_smul_comm, smul_mul_assoc, smul_smul, monomial_append,
      map_mul, monomial_cons, monomial_nil, mul_one, minusHom_θ, ← K_add]
    simp only [mul_assoc]
  -- the values of the form
  have hfA : form D v (rev k I x) (monomial k (i :: w')) =
      thetaNorm D v i * form D v (rev k I (rDeriv D v i x)) (monomial k w') := by
    rw [monomial_cons, form_comm, form_θ_mul, lDeriv_rev, form_comm]
  have hfR : form D v (rev k I x) (monomial k (w' ++ [i])) =
      thetaNorm D v i * form D v (rev k I (lDeriv D v i x)) (monomial k w') := by
    rw [monomial_append, monomial_cons, monomial_nil, mul_one, form_mul_θ_right, rDeriv_rev]
  rw [hexp, hRt, map_add, map_sub, map_smul, map_smul, map_smul, map_smul, hA, hB, hC, map_smul,
    map_smul, formFunctional_plusHom_K_minusHom_monomial,
    formFunctional_plusHom_K_minusHom_monomial, formFunctional_plusHom_K_minusHom_monomial,
    formFunctional_plusHom_K_minusHom_monomial, hfA, hfR]
  rcases hμ with rfl | ⟨h0r, h0l⟩
  swap
  · simp [h0r, h0l]
  by_cases hν : ν' = wordWeight w'
  · subst hν
    have he := normSq_wordWeight_emod_two (R := R) w'
    have hd : (2 : ℤ) * D.d i = D.dot i i := D.two_mul_d i
    have hq : v ^ D.d i ≠ 0 := pow_ne_zero _ hv0
    have ht : thetaNorm D v i = v ^ D.d i * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ := by
      rw [thetaNorm, show v ^ D.d i * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ =
        ((v ^ D.d i)⁻¹ * (v ^ D.d i - (v ^ D.d i)⁻¹))⁻¹ by rw [mul_inv, inv_inv]]
      congr 1
      rw [mul_sub, inv_mul_cancel₀ hq, sq]
    have e1 : v ^ R.rootSum (wordWeight w' + Finsupp.single i 1) (ktilde R i) * v ^ R.root i μ *
        formScale R v (ζ - R.root i) (ktilde R i + μ) (wordWeight (i :: w')) * v ^ D.d i =
        v ^ R.rootSum (wordWeight w') (ktilde R i) *
          formScale R v (ζ - R.root i) (ktilde R i + (ktilde R i + μ)) (wordWeight w') := by
      rw [formScale, formScale, ← zpow_natCast]
      simp only [← zpow_add₀ hv0]
      congr 1
      simp only [wordWeight_cons, normSq_single_add, LusztigCartanDatum.RootDatum.rootSum_add,
        LusztigCartanDatum.RootDatum.rootSum_single, one_smul, AddMonoidHom.add_apply,
        AddMonoidHom.sub_apply, map_add, ktildeSum_add, ktildeSum_single,
        rootSum_ktilde_eq_root_ktildeSum, root_ktilde_eq_dot]
      omega
    have e2 : formScale R v (ζ - R.root i) μ (wordWeight w') = (v ^ D.d i)⁻¹ *
        v ^ R.rootSum (wordWeight w') (-ktilde R i) *
          formScale R v ζ (μ + -ktilde R i) (wordWeight (w' ++ [i])) := by
      rw [formScale, formScale, ← zpow_natCast, ← zpow_neg]
      simp only [← zpow_add₀ hv0]
      congr 1
      simp only [wordWeight_append, wordWeight_cons, wordWeight_nil, add_zero,
        add_comm (wordWeight w') (Finsupp.single i 1), normSq_single_add,
        LusztigCartanDatum.RootDatum.rootSum_add, LusztigCartanDatum.RootDatum.rootSum_single,
        one_smul, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, map_add, map_neg,
        ktildeSum_add, ktildeSum_single, rootSum_ktilde_eq_root_ktildeSum, root_ktilde_eq_dot]
      omega
    generalize form D v (rev k I (rDeriv D v i x)) (monomial k w') = fr
    generalize form D v (rev k I (lDeriv D v i x)) (monomial k w') = fl
    simp only [smul_eq_mul]
    rw [ht]
    linear_combination
      (v ^ D.d i * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ * fr) * e1 +
      (v ^ D.d i * (v ^ D.d i - (v ^ D.d i)⁻¹)⁻¹ * fl) * e2
  · have h1 : form D v (rev k I (rDeriv D v i x)) (monomial k w') = 0 :=
      form_eq_zero_of_ne D v hν (rev_mem_weightSpace hr) (monomial_mem_weightSpace w')
    have h2 : form D v (rev k I (lDeriv D v i x)) (monomial k w') = 0 :=
      form_eq_zero_of_ne D v hν hl (monomial_mem_weightSpace w')
    simp [h1, h2]

/-- **The identity (a) in the proof of [Lus] 26.1.3**: `P_{ζ-αᵢ}(ρ(Eᵢ) u) = P_ζ(u ρ̄(Eᵢ))`. -/
theorem formFunctional_rho_E_mul (ζ : Y →+ ℤ) (i : I) (u : QuantumGroup R v) :
    formFunctional R v hv (ζ - R.root i) (rho R v (E R v i) * u) =
      formFunctional R v hv ζ (u * rhoBar R v (E R v i)) := by
  induction u using induction_plusHom_K_minusHom (NeZero.ne v) with
  | h0 => simp
  | hadd x y hx hy => rw [mul_add, map_add, hx, hy, add_mul, map_add]
  | hsmul c x hx => rw [mul_smul_comm, map_smul, hx, smul_mul_assoc, map_smul]
  | hmon w μ w' =>
    have hw := monomial_mem_weightSpace (k := k) w
    by_cases hi : wordWeight w i = 0
    · have h0r : rDeriv D v i (monomial k w) = 0 := rDeriv_eq_zero_of_mem D v i hi hw
      have h0l' : rev k I (lDeriv D v i (monomial k w)) = 0 := by
        rw [← rDeriv_rev]; exact rDeriv_eq_zero_of_mem D v i hi (rev_mem_weightSpace hw)
      have h0l : lDeriv D v i (monomial k w) = 0 := by
        have h := congrArg (rev k I) h0l'
        rwa [rev_rev, map_zero] at h
      refine formFunctional_rho_E_mul_aux hv ζ i (ν' := 0) hw ?_ ?_ (Or.inr ⟨h0r, h0l⟩) μ w'
      · rw [h0r]; exact Submodule.zero_mem _
      · rw [h0l']; exact Submodule.zero_mem _
    · have hle : Finsupp.single i 1 ≤ wordWeight w :=
        Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
      have hμ : wordWeight w = (wordWeight w - Finsupp.single i 1) + Finsupp.single i 1 :=
        (tsub_add_cancel_of_le hle).symm
      have hw' : monomial k w ∈
          LusztigF.weightSpace k ((wordWeight w - Finsupp.single i 1) + Finsupp.single i 1) :=
        hμ ▸ hw
      refine formFunctional_rho_E_mul_aux hv ζ i hw (rDeriv_mem_weightSpace D v i hw') ?_
        (Or.inl hμ) μ w'
      rw [← rDeriv_rev]
      exact rDeriv_mem_weightSpace D v i (rev_mem_weightSpace hw')

end Functional

lemma rhoBar_mem_adWeightSpace {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) : rhoBar R v x ∈ adWeightSpace R v (-χ) := fun μ ↦ by
  have h := congrArg (rhoBar R v) (hx μ)
  rw [rhoBar_mul, map_smul, rhoBar_mul, rhoBar_K] at h
  rw [AddMonoidHom.neg_apply, h, smul_smul, ← zpow_add₀ (NeZero.ne v), neg_add_cancel, zpow_zero,
    one_smul]

namespace Modified

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv

/-- [Lus] 26.1.3 for a homogeneous `u ∈ U_χ`, reduced to an identity of the functionals `P_ζ`. -/
lemma form_rightAct_left_of_mem {χ : Y →+ ℤ} {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v χ)
    (H : ∀ ζ z, z ∈ adWeightSpace R v χ →
      formFunctional R v hv (ζ - χ) (rho R v u * z) = formFunctional R v hv ζ (z * rhoBar R v u))
    (x y : Modified R v) :
    form R v hv (rightAct R v hv u x) y = form R v hv x (rightAct R v hv (rhoBar R v u) y) := by
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | helt l₁ l₂ a ha =>
  induction y using induction_on with
  | h0 => simp
  | hadd y y' hy hy' => simp only [map_add, hy, hy']
  | helt m₁ m₂ b hb =>
    rw [rightAct_elt hv hu, rightAct_elt hv (rhoBar_mem_adWeightSpace hu), form_elt_elt,
      form_elt_elt]
    have e : ((l₁, l₂ - χ) = (m₁, m₂)) ↔ ((l₁, l₂) = (m₁, m₂ - -χ)) := by
      simp only [Prod.mk.injEq, sub_neg_eq_add, sub_eq_iff_eq_add]
    split_ifs with h₁ h₂ h₃
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
      have hz : rho R v a * b ∈ adWeightSpace R v χ := by
        have := mul_mem_adWeightSpace (rho_mem_adWeightSpace ha) hb
        convert this using 2
        abel
      rw [rho_mul, mul_assoc, H _ _ hz, mul_assoc]
    · exact absurd (e.1 h₁) h₂
    · exact absurd (e.2 h₃) h₁
    · rfl

/-- `P(u)` implies `P(ρ̄ u)`, by symmetry of the form. -/
lemma form_rightAct_left_rhoBar {u : QuantumGroup R v}
    (H : ∀ x y, form R v hv (rightAct R v hv u x) y =
      form R v hv x (rightAct R v hv (rhoBar R v u) y))
    (x y : Modified R v) :
    form R v hv (rightAct R v hv (rhoBar R v u) x) y =
      form R v hv x (rightAct R v hv (rhoBar R v (rhoBar R v u)) y) := by
  rw [form_comm, ← H, form_comm, rhoBar_rhoBar]

lemma form_rightAct_left_mul {u u' : QuantumGroup R v}
    (hu : ∀ x y, form R v hv (rightAct R v hv u x) y =
      form R v hv x (rightAct R v hv (rhoBar R v u) y))
    (hu' : ∀ x y, form R v hv (rightAct R v hv u' x) y =
      form R v hv x (rightAct R v hv (rhoBar R v u') y))
    (x y : Modified R v) :
    form R v hv (rightAct R v hv (u * u') x) y =
      form R v hv x (rightAct R v hv (rhoBar R v (u * u')) y) := by
  rw [rightAct_mul, hu', hu, ← rightAct_mul, ← rhoBar_mul]

lemma form_rightAct_left_smul (c : k) {u : QuantumGroup R v}
    (hu : ∀ x y, form R v hv (rightAct R v hv u x) y =
      form R v hv x (rightAct R v hv (rhoBar R v u) y))
    (x y : Modified R v) :
    form R v hv (rightAct R v hv (c • u) x) y =
      form R v hv x (rightAct R v hv (rhoBar R v (c • u)) y) := by
  simp only [map_smul, LinearMap.smul_apply, hu]

/-- **[Lus] 26.1.3**: `(x u, y) = (x, y ρ̄(u))` for `x, y ∈ U̇` and `u ∈ U`. -/
theorem form_rightAct_left (u : QuantumGroup R v) (x y : Modified R v) :
    form R v hv (rightAct R v hv u x) y = form R v hv x (rightAct R v hv (rhoBar R v u) y) := by
  have hE : ∀ i x y, form R v hv (rightAct R v hv (E R v i) x) y =
      form R v hv x (rightAct R v hv (rhoBar R v (E R v i)) y) :=
    fun i ↦ form_rightAct_left_of_mem hv (E_mem_adWeightSpace i) fun ζ z _ ↦
      formFunctional_rho_E_mul hv ζ i z
  have hK : ∀ μ x y, form R v hv (rightAct R v hv (K R v μ) x) y =
      form R v hv x (rightAct R v hv (rhoBar R v (K R v μ)) y) :=
    fun μ ↦ form_rightAct_left_of_mem hv (K_mem_adWeightSpace μ) fun ζ z hz ↦ by
      have h := hz μ
      rw [AddMonoidHom.zero_apply, zpow_zero, one_smul] at h
      rw [rho_K, rhoBar_K, sub_zero, h]
  induction u using QuantumGroup.induction_on generalizing x y with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one]
    refine form_rightAct_left_smul hv c (fun x y ↦ ?_) x y
    rw [rightAct_one, rhoBar_one, rightAct_one]
  | E i => exact hE i x y
  | K μ => exact hK μ x y
  | F i =>
    have h := form_rightAct_left_rhoBar hv (u := rhoBar R v (F R v i)) (fun x y ↦ by
      rw [rhoBar_F, rhoBarF]
      exact form_rightAct_left_smul hv _ (form_rightAct_left_mul hv (hK _) (hE i)) x y) x y
    rwa [rhoBar_rhoBar] at h
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | mul u u' hu hu' => exact form_rightAct_left_mul hv hu hu' x y

end Modified

end LieLean.QuantumGroup
