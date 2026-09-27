/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Affine hyperplanes in a dual space and polynomial functions

Let `H` be a finite-dimensional vector space over an infinite field `K`. For `a ∈ H` nonzero and
`c ∈ K`, the affine polynomial `λ ↦ λ(a) + c` on `H*` (`Module.Dual.affPoly a c`) cuts out an
affine hyperplane. We show:

* a polynomial vanishing on the hyperplane is divisible by `λ(a) + c`
  (`Module.Dual.affPoly_dvd_of_forall`); hence if it is not divisible, it is nonzero at some point
  of the hyperplane (`Module.Dual.exists_eval_ne_zero_of_not_dvd`);
* `λ(a) + c` is irreducible (`Module.Dual.irreducible_affPoly`), and if it divides `λ(a') + c'`
  the two are proportional (`Module.Dual.affProportional_of_affPoly_dvd`);
* finitely many polynomials that are each nonzero somewhere on the hyperplane are simultaneously
  nonzero at some point of it (`Module.Dual.exists_forall_evalPoly_ne_zero_of_hyperplane`);
* restriction to lines `λ₀ + t δ` (`Module.Dual.linePoly`), with the leading coefficient
  (`Module.Dual.coeff_linePoly_of_totalDegree_le`) and the order of vanishing of products of
  affine polynomials (`Module.Dual.natTrailingDegree_linePoly_prod`);
* the multiplicity of a hyperplane in a product of affine polynomials is well defined
  (`Module.Dual.sum_filter_eq_of_C_mul_prod_eq`), and conversely it determines the product up to a
  scalar (`Module.Dual.exists_prod_pow_eq_C_mul_prod_pow`).
-/

open Polynomial

noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The top homogeneous component of a nonzero polynomial is nonzero. -/
lemma homogeneousComponent_totalDegree_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    fun s ↦ s.sum fun _ e ↦ e
  intro h
  have : (homogeneousComponent p.totalDegree p).coeff m = 0 := by
    rw [h]; rfl
  have hdeg : m.degree = p.totalDegree := by rw [totalDegree, hmd]; rfl
  simp only [coeff_homogeneousComponent, hdeg, ↓reduceIte] at this
  exact (mem_support_iff.mp hm) this

/-- Total degree is additive for nonzero polynomials over a domain. -/
lemma totalDegree_mul_eq_add [IsDomain R] {p q : MvPolynomial σ R} (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).totalDegree = p.totalDegree + q.totalDegree := by
  refine le_antisymm (totalDegree_mul p q) (le_of_not_gt fun hlt ↦ ?_)
  have h := homogeneousComponent_mul_of_totalDegree_le le_rfl le_rfl (p := p) (q := q)
  rw [homogeneousComponent_eq_zero _ _ hlt] at h
  exact mul_ne_zero (homogeneousComponent_totalDegree_ne_zero hp)
    (homogeneousComponent_totalDegree_ne_zero hq) h.symm

lemma totalDegree_eq_zero_of_isUnit [IsDomain R] {p : MvPolynomial σ R} (hp : IsUnit p) :
    p.totalDegree = 0 := by
  obtain ⟨q, hq⟩ := hp.exists_right_inv
  have := congrArg totalDegree hq
  rw [totalDegree_mul_eq_add (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq),
    totalDegree_one] at this
  omega

end MvPolynomial

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

lemma natTrailingDegree_pow_eq_mul (p : R[X]) (n : ℕ) :
    (p ^ n).natTrailingDegree = n * p.natTrailingDegree := by
  by_cases hp : p = 0
  · rcases n with _ | n
    · simp
    · simp [hp]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, natTrailingDegree_mul (pow_ne_zero _ hp) hp, ih, add_one_mul]

lemma natTrailingDegree_finsetProd {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).natTrailingDegree = ∑ i ∈ s, (f i).natTrailingDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      natTrailingDegree_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

end Polynomial

namespace Module.Dual

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

variable (K H) in
/-- The affine polynomial `λ ↦ λ(a) + c` on `H*`. -/
def affPoly (a : H) (c : K) : MvPolynomial (PolyIdx K H) K := linPoly K H a + MvPolynomial.C c

@[simp] lemma evalPoly_affPoly (a : H) (c : K) (Λ : Dual K H) :
    evalPoly K H (affPoly K H a c) Λ = Λ a + c := by
  simp [affPoly]

@[simp] lemma evalPoly_C (u : K) (Λ : Dual K H) : evalPoly K H (MvPolynomial.C u) Λ = u := by
  simp [evalPoly_apply]

lemma evalPoly_aeval (g : PolyIdx K H → MvPolynomial (PolyIdx K H) K)
    (F : MvPolynomial (PolyIdx K H) K) (Λ : Dual K H) :
    evalPoly K H (MvPolynomial.aeval g F) Λ =
      MvPolynomial.aeval (fun j ↦ evalPoly K H (g j) Λ) F := by
  simp only [evalPoly_apply]
  exact congrArg (fun φ ↦ φ F) (MvPolynomial.comp_aeval (R := K) g
    (MvPolynomial.aeval fun j ↦ Λ (Module.Free.chooseBasis K H j)))

lemma exists_dual_apply_ne_zero {a : H} (ha : a ≠ 0) : ∃ δ : Dual K H, δ a ≠ 0 := by
  by_contra! h
  exact ha ((Module.forall_dual_apply_eq_zero_iff K a).mp h)

lemma exists_dual_apply_eq_one {a : H} (ha : a ≠ 0) : ∃ δ : Dual K H, δ a = 1 := by
  obtain ⟨δ, hδ⟩ := exists_dual_apply_ne_zero (K := K) ha
  exact ⟨(δ a)⁻¹ • δ, by simp [hδ]⟩

/-- A nonzero polynomial is nonzero at some point (over an infinite field). -/
lemma exists_evalPoly_ne_zero [Infinite K] {F : MvPolynomial (PolyIdx K H) K} (hF : F ≠ 0) :
    ∃ Λ : Dual K H, evalPoly K H F Λ ≠ 0 := by
  by_contra! h
  exact hF (evalPoly_injective (by ext Λ; simp [h Λ]))

/-- Finitely many nonzero polynomials are simultaneously nonzero at some point. -/
lemma exists_forall_evalPoly_ne_zero [Infinite K] {κ : Type*} (s : Finset κ)
    (F : κ → MvPolynomial (PolyIdx K H) K) (hF : ∀ k ∈ s, F k ≠ 0) :
    ∃ Λ : Dual K H, ∀ k ∈ s, evalPoly K H (F k) Λ ≠ 0 := by
  obtain ⟨Λ, hΛ⟩ := exists_evalPoly_ne_zero (Finset.prod_ne_zero_iff.mpr hF)
  refine ⟨Λ, fun k hk ↦ ?_⟩
  rw [map_prod, Finset.prod_apply] at hΛ
  exact Finset.prod_ne_zero_iff.mp hΛ k hk

/-! ### Projection onto a hyperplane -/

variable (K H) in
/-- The substitution `F ↦ (λ ↦ F(λ - (λ(a) + c) δ))`. For `δ(a) = 1` this is composition with a
projection onto the hyperplane `λ(a) + c = 0`. -/
def projSubst (a : H) (c : K) (δ : Dual K H) :
    MvPolynomial (PolyIdx K H) K →ₐ[K] MvPolynomial (PolyIdx K H) K :=
  MvPolynomial.aeval fun j ↦
    MvPolynomial.X j - affPoly K H a c * MvPolynomial.C (δ (Module.Free.chooseBasis K H j))

lemma evalPoly_projSubst (a : H) (c : K) (δ : Dual K H) (F : MvPolynomial (PolyIdx K H) K)
    (Λ : Dual K H) :
    evalPoly K H (projSubst K H a c δ F) Λ = evalPoly K H F (Λ - (Λ a + c) • δ) := by
  rw [projSubst, evalPoly_aeval, evalPoly_apply]
  congr 1
  ext j
  have := evalPoly_affPoly a c Λ
  simp only [evalPoly_apply] at *
  simp only [MvPolynomial.aeval_X, map_sub, map_mul, this, MvPolynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]

/-- `projSubst` is the identity modulo `λ(a) + c`; so if it kills `F`, then `λ(a) + c` divides
`F`. -/
lemma affPoly_dvd_of_projSubst_eq_zero (a : H) (c : K) (δ : Dual K H)
    {F : MvPolynomial (PolyIdx K H) K} (h : projSubst K H a c δ F = 0) : affPoly K H a c ∣ F := by
  set I := Ideal.span {affPoly K H a c}
  have hmk : (Ideal.Quotient.mkₐ K I).comp (projSubst K H a c δ) = Ideal.Quotient.mkₐ K I := by
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    have hφ : Ideal.Quotient.mk I (affPoly K H a c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [AlgHom.comp_apply, projSubst, MvPolynomial.aeval_X, map_sub, map_mul]
    rw [Ideal.Quotient.mkₐ_eq_mk, hφ, zero_mul, sub_zero]
  have := congrArg (fun f ↦ f F) hmk
  simp only [AlgHom.comp_apply, h, map_zero, Ideal.Quotient.mkₐ_eq_mk] at this
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp this.symm)

/-- **A polynomial vanishing on an affine hyperplane is divisible by its equation.** -/
theorem affPoly_dvd_of_forall [Infinite K] {a : H} (ha : a ≠ 0) (c : K)
    {F : MvPolynomial (PolyIdx K H) K}
    (hF : ∀ Λ : Dual K H, Λ a + c = 0 → evalPoly K H F Λ = 0) : affPoly K H a c ∣ F := by
  obtain ⟨δ, hδ⟩ := exists_dual_apply_eq_one (K := K) ha
  refine affPoly_dvd_of_projSubst_eq_zero a c δ (evalPoly_injective ?_)
  ext Λ
  rw [evalPoly_projSubst, map_zero, Pi.zero_apply]
  exact hF _ (by simp [hδ])

/-- A polynomial not divisible by the equation of an affine hyperplane is nonzero at some point of
the hyperplane. -/
theorem exists_eval_ne_zero_of_not_dvd [Infinite K] {a : H} (ha : a ≠ 0) (c : K)
    {F : MvPolynomial (PolyIdx K H) K} (hF : ¬ affPoly K H a c ∣ F) :
    ∃ Λ : Dual K H, Λ a + c = 0 ∧ evalPoly K H F Λ ≠ 0 := by
  by_contra! h
  exact hF (affPoly_dvd_of_forall ha c h)

/-- **Generic points of a hyperplane.** Finitely many polynomials, each nonzero at some point of an
affine hyperplane, are simultaneously nonzero at some point of it. -/
theorem exists_forall_evalPoly_ne_zero_of_hyperplane [Infinite K] {a : H} (ha : a ≠ 0) (c : K)
    {κ : Type*} (s : Finset κ) (F : κ → MvPolynomial (PolyIdx K H) K)
    (hF : ∀ k ∈ s, ∃ Λ : Dual K H, Λ a + c = 0 ∧ evalPoly K H (F k) Λ ≠ 0) :
    ∃ Λ : Dual K H, Λ a + c = 0 ∧ ∀ k ∈ s, evalPoly K H (F k) Λ ≠ 0 := by
  obtain ⟨δ, hδ⟩ := exists_dual_apply_eq_one (K := K) ha
  obtain ⟨Λ, hΛ⟩ := exists_forall_evalPoly_ne_zero s (fun k ↦ projSubst K H a c δ (F k))
    fun k hk h0 ↦ by
      obtain ⟨Λ', hΛ', hne⟩ := hF k hk
      have := congrFun (congrArg (evalPoly K H) h0) Λ'
      rw [evalPoly_projSubst, hΛ', zero_smul, sub_zero, map_zero, Pi.zero_apply] at this
      exact hne this
  refine ⟨Λ - (Λ a + c) • δ, by simp [hδ], fun k hk ↦ ?_⟩
  rw [← evalPoly_projSubst]
  exact hΛ k hk

/-! ### Degree and irreducibility -/

lemma totalDegree_affPoly_le (a : H) (c : K) : (affPoly K H a c).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le (totalDegree_linPoly_le a) (by simp))

lemma affPoly_ne_zero {a : H} (ha : a ≠ 0) (c : K) : affPoly K H a c ≠ 0 := by
  intro h
  obtain ⟨Λ, hΛ⟩ := exists_dual_apply_ne_zero (K := K) ha
  have h1 := congrFun (congrArg (evalPoly K H) h) Λ
  have h2 := congrFun (congrArg (evalPoly K H) h) ((Λ a)⁻¹ • Λ)
  have h3 := congrFun (congrArg (evalPoly K H) h) ((2 : K) • (Λ a)⁻¹ • Λ)
  simp only [evalPoly_affPoly, map_zero, Pi.zero_apply, LinearMap.smul_apply, smul_eq_mul,
    inv_mul_cancel₀ hΛ] at h1 h2 h3
  have : (1 : K) = 0 := by linear_combination h3 - 2 * h2 + h2
  exact one_ne_zero this

lemma totalDegree_affPoly {a : H} (ha : a ≠ 0) (c : K) : (affPoly K H a c).totalDegree = 1 := by
  refine le_antisymm (totalDegree_affPoly_le a c) (Nat.one_le_iff_ne_zero.mpr fun h ↦ ?_)
  have hr := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h
  set r := (affPoly K H a c).coeff 0
  obtain ⟨Λ, hΛ⟩ := exists_dual_apply_ne_zero (K := K) ha
  have h1 := congrFun (congrArg (evalPoly K H) hr) Λ
  have h2 := congrFun (congrArg (evalPoly K H) hr) 0
  simp only [evalPoly_affPoly, evalPoly_C, LinearMap.zero_apply, zero_add] at h1 h2
  exact hΛ (by linear_combination h1 - h2)

/-- The equation of an affine hyperplane is irreducible. -/
theorem irreducible_affPoly {a : H} (ha : a ≠ 0) (c : K) : Irreducible (affPoly K H a c) := by
  refine ⟨fun hu ↦ ?_, fun p q hpq ↦ ?_⟩
  · have := MvPolynomial.totalDegree_eq_zero_of_isUnit hu
    rw [totalDegree_affPoly ha] at this
    exact one_ne_zero this
  · have hp : p ≠ 0 := fun h ↦ affPoly_ne_zero ha c (by rw [hpq, h, zero_mul])
    have hq : q ≠ 0 := fun h ↦ affPoly_ne_zero ha c (by rw [hpq, h, mul_zero])
    have := congrArg MvPolynomial.totalDegree hpq
    rw [MvPolynomial.totalDegree_mul_eq_add hp hq, totalDegree_affPoly ha] at this
    rcases Nat.eq_zero_or_pos p.totalDegree with h | h
    · left
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h
      rw [h] at hp ⊢
      exact (isUnit_iff_ne_zero.mpr fun h0 ↦ hp (by simp [h0])).map MvPolynomial.C
    · right
      have h' := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by omega : q.totalDegree = 0)
      rw [h'] at hq ⊢
      exact (isUnit_iff_ne_zero.mpr fun h0 ↦ hq (by simp [h0])).map MvPolynomial.C

/-! ### Proportional affine functions -/

/-- The affine functions `λ ↦ λ(a) + c` and `λ ↦ λ(a₀) + c₀` are proportional:
`(a, c) = u (a₀, c₀)` for some `u`. -/
def AffProportional (a : H) (c : K) (a₀ : H) (c₀ : K) : Prop :=
  ∃ u : K, a = u • a₀ ∧ c = u * c₀

lemma AffProportional.refl (a : H) (c : K) : AffProportional a c a c := ⟨1, by simp, by simp⟩

lemma AffProportional.ne_zero {a a₀ : H} {c c₀ : K} (ha : a ≠ 0) :
    AffProportional a c a₀ c₀ → ∃ u : K, u ≠ 0 ∧ a = u • a₀ ∧ c = u * c₀ := by
  rintro ⟨u, rfl, rfl⟩
  exact ⟨u, fun h ↦ ha (by rw [h, zero_smul]), rfl, rfl⟩

lemma AffProportional.symm {a a₀ : H} {c c₀ : K} (ha : a ≠ 0) (h : AffProportional a c a₀ c₀) :
    AffProportional a₀ c₀ a c := by
  obtain ⟨u, hu, rfl, rfl⟩ := h.ne_zero ha
  exact ⟨u⁻¹, by rw [smul_smul, inv_mul_cancel₀ hu, one_smul], by rw [← mul_assoc,
    inv_mul_cancel₀ hu, one_mul]⟩

lemma AffProportional.trans {a a₁ a₂ : H} {c c₁ c₂ : K} (h : AffProportional a c a₁ c₁)
    (h' : AffProportional a₁ c₁ a₂ c₂) : AffProportional a c a₂ c₂ := by
  obtain ⟨u, rfl, rfl⟩ := h
  obtain ⟨v, rfl, rfl⟩ := h'
  exact ⟨u * v, by rw [smul_smul], by rw [mul_assoc]⟩

lemma AffProportional.affPoly_eq {a a₀ : H} {c c₀ : K} {u : K} (ha : a = u • a₀)
    (hc : c = u * c₀) : affPoly K H a c = MvPolynomial.C u * affPoly K H a₀ c₀ := by
  rw [affPoly, affPoly, ha, hc, map_smul, MvPolynomial.smul_eq_C_mul, map_mul, mul_add]

lemma AffProportional.evalPoly_eq_zero {a a₀ : H} {c c₀ : K} (h : AffProportional a c a₀ c₀)
    {Λ : Dual K H} (hΛ : Λ a₀ + c₀ = 0) : Λ a + c = 0 := by
  obtain ⟨u, rfl, rfl⟩ := h
  rw [map_smul, smul_eq_mul, ← mul_add, hΛ, mul_zero]

/-- If the equation of an affine hyperplane divides that of another, they are proportional. -/
lemma affProportional_of_affPoly_dvd {a a₀ : H} (ha₀ : a₀ ≠ 0) (ha : a ≠ 0) {c c₀ : K}
    (h : affPoly K H a₀ c₀ ∣ affPoly K H a c) : AffProportional a c a₀ c₀ := by
  obtain ⟨q, hq⟩ := h
  have hq0 : q ≠ 0 := by rintro rfl; exact affPoly_ne_zero ha c (by rw [hq, mul_zero])
  have hdeg := congrArg MvPolynomial.totalDegree hq
  rw [MvPolynomial.totalDegree_mul_eq_add (affPoly_ne_zero ha₀ c₀) hq0, totalDegree_affPoly ha,
    totalDegree_affPoly ha₀] at hdeg
  have hq' := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by omega : q.totalDegree = 0)
  set u := q.coeff 0
  have hfun (Λ : Dual K H) : Λ a + c = (Λ a₀ + c₀) * u := by
    have := congrFun (congrArg (evalPoly K H) hq) Λ
    rwa [hq', map_mul, Pi.mul_apply, evalPoly_affPoly, evalPoly_affPoly, evalPoly_C] at this
  have hc : c = u * c₀ := by
    have := hfun 0
    simp only [LinearMap.zero_apply, zero_add] at this
    rw [this, mul_comm]
  refine ⟨u, ?_, hc⟩
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff K (a - u • a₀)).mp fun Λ ↦ ?_
  rw [map_sub, map_smul, smul_eq_mul]
  linear_combination hfun Λ - hc

/-! ### Restriction to lines -/

variable (K H) in
/-- The restriction `t ↦ F(λ₀ + t δ)` of a polynomial `F` on `H*` to a line, as a polynomial in
`t`. -/
def linePoly (Λ₀ δ : Dual K H) : MvPolynomial (PolyIdx K H) K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun j ↦
    C (δ (Module.Free.chooseBasis K H j)) * X + C (Λ₀ (Module.Free.chooseBasis K H j))

lemma eval_linePoly (Λ₀ δ : Dual K H) (F : MvPolynomial (PolyIdx K H) K) (t : K) :
    (linePoly K H Λ₀ δ F).eval t = evalPoly K H F (Λ₀ + t • δ) := by
  have := congrArg (fun φ ↦ φ F) (MvPolynomial.comp_aeval (R := K)
    (f := fun j ↦ C (δ (Module.Free.chooseBasis K H j)) * X +
      C (Λ₀ (Module.Free.chooseBasis K H j))) (Polynomial.aeval t))
  simp only [AlgHom.comp_apply] at this
  rw [← coe_aeval_eq_eval, linePoly, this, evalPoly_apply]
  refine congrArg (fun g ↦ MvPolynomial.aeval g F) (funext fun j ↦ ?_)
  simp only [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

@[simp] lemma linePoly_C (Λ₀ δ : Dual K H) (u : K) :
    linePoly K H Λ₀ δ (MvPolynomial.C u) = C u :=
  MvPolynomial.aeval_C _ u

lemma linePoly_affPoly [Infinite K] (Λ₀ δ : Dual K H) (a : H) (c : K) :
    linePoly K H Λ₀ δ (affPoly K H a c) = C (δ a) * X + C (Λ₀ a + c) :=
  Polynomial.funext fun t ↦ by
    rw [eval_linePoly, evalPoly_affPoly]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, eval_add, eval_mul,
      eval_C, eval_X]
    ring

lemma natDegree_linePoly_monomial_le_and_coeff (Λ₀ δ : Dual K H)
    (m : PolyIdx K H →₀ ℕ) :
    (linePoly K H Λ₀ δ (MvPolynomial.monomial m 1)).natDegree ≤ m.degree ∧
      (linePoly K H Λ₀ δ (MvPolynomial.monomial m 1)).coeff m.degree =
        evalPoly K H (MvPolynomial.monomial m 1) δ := by
  induction m using Finsupp.induction with
  | zero => simp [evalPoly_apply]
  | single_add j k m _ _ ih =>
    have hlin : (C (δ (Module.Free.chooseBasis K H j)) * X +
        C (Λ₀ (Module.Free.chooseBasis K H j))).natDegree ≤ 1 := natDegree_linear_le
    have hpow := natDegree_pow_le_of_le k hlin
    rw [mul_one] at hpow
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, map_add, Finsupp.degree_single]
    simp only [linePoly, MvPolynomial.aeval_X] at ih ⊢
    refine ⟨natDegree_mul_le_of_le hpow ih.1, ?_⟩
    have hc := coeff_pow_of_natDegree_le (m := k) hlin
    rw [mul_one] at hc
    rw [coeff_mul_add_eq_of_natDegree_le hpow ih.1, ih.2, hc, map_mul, map_pow, Pi.mul_apply,
      Pi.pow_apply]
    congr 1
    simp [evalPoly_apply]

/-- **Leading coefficient of a restriction to a line.** If `F` has degree `≤ d`, then
`t ↦ F(λ₀ + t δ)` has degree `≤ d`, with coefficient of `t^d` equal to `F_d(δ)`, where `F_d` is
the homogeneous component of degree `d` of `F`. -/
theorem natDegree_linePoly_le_and_coeff (Λ₀ δ : Dual K H) {d : ℕ}
    {F : MvPolynomial (PolyIdx K H) K} (hF : F.totalDegree ≤ d) :
    (linePoly K H Λ₀ δ F).natDegree ≤ d ∧
      (linePoly K H Λ₀ δ F).coeff d = evalPoly K H (MvPolynomial.homogeneousComponent d F) δ := by
  classical
  have key : ∀ m ∈ F.support,
      (linePoly K H Λ₀ δ (MvPolynomial.monomial m (F.coeff m))).natDegree ≤ d ∧
      (linePoly K H Λ₀ δ (MvPolynomial.monomial m (F.coeff m))).coeff d =
        evalPoly K H (MvPolynomial.homogeneousComponent d
          (MvPolynomial.monomial m (F.coeff m))) δ := by
    intro m hm
    have hmd : m.degree ≤ d := (MvPolynomial.le_totalDegree hm).trans hF
    obtain ⟨h1, h2⟩ := natDegree_linePoly_monomial_le_and_coeff Λ₀ δ m
    have hCm : MvPolynomial.monomial m (F.coeff m) =
        MvPolynomial.C (F.coeff m) * MvPolynomial.monomial m 1 := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [hCm, map_mul, linePoly_C]
    refine ⟨(natDegree_C_mul_le _ _).trans (h1.trans hmd), ?_⟩
    rw [coeff_C_mul, MvPolynomial.homogeneousComponent_C_mul, map_mul, Pi.mul_apply, evalPoly_C]
    congr 1
    rcases hmd.lt_or_eq with hlt | heq
    · rw [coeff_eq_zero_of_natDegree_lt (h1.trans_lt hlt),
        MvPolynomial.homogeneousComponent_eq_zero' _ _ fun m' hm' ↦ ?_, map_zero, Pi.zero_apply]
      simp only [MvPolynomial.support_monomial, one_ne_zero, ↓reduceIte,
        Finset.mem_singleton] at hm'
      rw [hm']
      exact hlt.ne
    · rw [← heq, h2, MvPolynomial.homogeneousComponent_of_mem
        (MvPolynomial.isHomogeneous_monomial _ rfl)]
      simp
  rw [F.as_sum]
  exact Finset.sum_induction _ (fun G ↦ (linePoly K H Λ₀ δ G).natDegree ≤ d ∧
      (linePoly K H Λ₀ δ G).coeff d =
        evalPoly K H (MvPolynomial.homogeneousComponent d G) δ)
    (fun G G' h h' ↦ ⟨by rw [map_add]; exact natDegree_add_le_of_degree_le h.1 h'.1, by
      rw [map_add, coeff_add, map_add, map_add, Pi.add_apply, h.2, h'.2]⟩)
    ⟨by simp, by simp⟩ key

/-- A product of powers of affine polynomials restricted to a line transversal to all of the
hyperplanes through `λ₀` is nonzero. -/
theorem linePoly_C_mul_prod_ne_zero [Infinite K] {κ : Type*} (s : Finset κ)
    (a : κ → H) (c : κ → K) (e : κ → ℕ) {c₀ : K} (hc₀ : c₀ ≠ 0) {Λ₀ δ : Dual K H}
    (hδ : ∀ k ∈ s, Λ₀ (a k) + c k = 0 → δ (a k) ≠ 0) :
    linePoly K H Λ₀ δ (MvPolynomial.C c₀ * ∏ k ∈ s, affPoly K H (a k) (c k) ^ e k) ≠ 0 := by
  rw [map_mul, map_prod, linePoly_C]
  refine mul_ne_zero (C_ne_zero.mpr hc₀) (Finset.prod_ne_zero_iff.mpr fun k hk ↦ ?_)
  rw [map_pow, linePoly_affPoly]
  refine pow_ne_zero _ fun h ↦ ?_
  have h0 := congrArg (coeff · 0) h
  have h1 := congrArg (coeff · 1) h
  simp only [coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at h0 h1
  simp only [one_ne_zero, zero_ne_one, ↓reduceIte, add_zero, zero_add] at h0 h1
  exact hδ k hk h0 h1

/-- **Order of vanishing of a product of affine polynomials along a line.** Along a line
`λ₀ + t δ` that is transversal to every hyperplane `λ(a_k) + c_k = 0` through `λ₀`, the product
`c₀ ∏_k (λ(a_k) + c_k)^{e_k}` vanishes at `t = 0` to order `∑_{k : λ₀(a_k) + c_k = 0} e_k`. -/
theorem natTrailingDegree_linePoly_prod [Infinite K] [DecidableEq K] {κ : Type*} (s : Finset κ)
    (a : κ → H) (c : κ → K) (e : κ → ℕ) {c₀ : K} (hc₀ : c₀ ≠ 0) {Λ₀ δ : Dual K H}
    (hδ : ∀ k ∈ s, Λ₀ (a k) + c k = 0 → δ (a k) ≠ 0) :
    (linePoly K H Λ₀ δ (MvPolynomial.C c₀ *
        ∏ k ∈ s, affPoly K H (a k) (c k) ^ e k)).natTrailingDegree =
      ∑ k ∈ s with Λ₀ (a k) + c k = 0, e k := by
  have hfac (k : κ) (hk : k ∈ s) : linePoly K H Λ₀ δ (affPoly K H (a k) (c k)) ≠ 0 ∧
      (linePoly K H Λ₀ δ (affPoly K H (a k) (c k))).natTrailingDegree =
        if Λ₀ (a k) + c k = 0 then 1 else 0 := by
    rw [linePoly_affPoly]
    split_ifs with h
    · rw [h, map_zero, add_zero, ← monomial_one_one_eq_X, C_mul_monomial, mul_one]
      exact ⟨(monomial_eq_zero_iff _ _).not.mpr (hδ k hk h),
        natTrailingDegree_monomial (hδ k hk h)⟩
    · have hc0 : (C (δ (a k)) * X + C (Λ₀ (a k) + c k)).coeff 0 ≠ 0 := by simpa using h
      exact ⟨fun h0 ↦ hc0 (by rw [h0, coeff_zero]),
        natTrailingDegree_eq_zero.mpr (.inr hc0)⟩
  rw [map_mul, map_prod, linePoly_C, natTrailingDegree_mul (C_ne_zero.mpr hc₀)
      (Finset.prod_ne_zero_iff.mpr fun k hk ↦ by rw [map_pow]; exact pow_ne_zero _ (hfac k hk).1),
    natTrailingDegree_C, zero_add, natTrailingDegree_finsetProd _ _
      fun k hk ↦ by rw [map_pow]; exact pow_ne_zero _ (hfac k hk).1, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [map_pow, natTrailingDegree_pow_eq_mul, (hfac k hk).2]
  split_ifs <;> simp

/-! ### Leading terms of products of affine polynomials -/

@[simp] lemma affPoly_zero (a : H) : affPoly K H a 0 = linPoly K H a := by
  simp [affPoly]

lemma homogeneousComponent_one_affPoly (a : H) (c : K) :
    MvPolynomial.homogeneousComponent 1 (affPoly K H a c) = linPoly K H a := by
  rw [affPoly, map_add, MvPolynomial.homogeneousComponent_of_mem (isHomogeneous_linPoly a),
    MvPolynomial.homogeneousComponent_eq_zero _ _ (by simp)]
  simp

/-- The leading term of `c₀ ∏_k (λ(a_k) + c_k)^{e_k}` is `c₀ ∏_k λ(a_k)^{e_k}`. -/
theorem hasTop_C_mul_prod_affPoly_pow {κ : Type*} (s : Finset κ) (a : κ → H) (c : κ → K)
    (e : κ → ℕ) (c₀ : K) :
    HasTop (∑ k ∈ s, e k) (MvPolynomial.C c₀ * ∏ k ∈ s, linPoly K H (a k) ^ e k)
      (evalPoly K H (MvPolynomial.C c₀ * ∏ k ∈ s, affPoly K H (a k) (c k) ^ e k)) := by
  have hpow (k : κ) : (affPoly K H (a k) (c k) ^ e k).totalDegree ≤ e k :=
    (MvPolynomial.totalDegree_pow _ _).trans
      (by simpa using Nat.mul_le_mul_left (e k) (totalDegree_affPoly_le (a k) (c k)))
  have hprod : (∏ k ∈ s, affPoly K H (a k) (c k) ^ e k).totalDegree ≤ ∑ k ∈ s, e k :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun k _ ↦ hpow k)
  refine ⟨_, ?_, ?_, rfl⟩
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hprod
  · rw [MvPolynomial.homogeneousComponent_C_mul,
      MvPolynomial.homogeneousComponent_prod_of_totalDegree_le s _ e fun k _ ↦ hpow k]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    have := MvPolynomial.homogeneousComponent_prod_of_totalDegree_le (Finset.range (e k))
      (fun _ ↦ affPoly K H (a k) (c k)) (fun _ ↦ 1)
      fun _ _ ↦ totalDegree_affPoly_le (a k) (c k)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Finset.prod_const,
      homogeneousComponent_one_affPoly] at this
    exact this

lemma affProportional_zero_iff (a a₀ : H) :
    AffProportional a (0 : K) a₀ 0 ↔ ∃ u : K, a = u • a₀ := by
  simp [AffProportional]

/-! ### Multiplicities of hyperplanes in products of affine polynomials -/

open Classical in
/-- **The multiplicity of a hyperplane in a product of affine polynomials is well defined**: if
two products `c₀ ∏_k (λ(a_k) + c_k)^{e_k}` agree, then for every affine hyperplane
`λ(a₀) + b₀ = 0` the sums of the exponents of the factors proportional to `λ(a₀) + b₀` agree. -/
theorem sum_filter_eq_of_C_mul_prod_eq [Infinite K] {κ κ' : Type*} {s : Finset κ}
    {s' : Finset κ'} {a : κ → H} {c : κ → K} {a' : κ' → H} {c' : κ' → K}
    (ha : ∀ k ∈ s, a k ≠ 0) (ha' : ∀ k ∈ s', a' k ≠ 0) (e : κ → ℕ) (e' : κ' → ℕ) {c₀ c₀' : K}
    (hc₀ : c₀ ≠ 0) (hc₀' : c₀' ≠ 0)
    (h : MvPolynomial.C c₀ * ∏ k ∈ s, affPoly K H (a k) (c k) ^ e k =
      MvPolynomial.C c₀' * ∏ k ∈ s', affPoly K H (a' k) (c' k) ^ e' k)
    {a₀ : H} (ha₀ : a₀ ≠ 0) (b₀ : K) :
    ∑ k ∈ s with AffProportional (a k) (c k) a₀ b₀, e k =
      ∑ k ∈ s' with AffProportional (a' k) (c' k) a₀ b₀, e' k := by
  -- a generic point `Λ₀` of the hyperplane
  obtain ⟨Λ₀, hΛ₀, hgen⟩ := exists_forall_evalPoly_ne_zero_of_hyperplane ha₀ b₀
    ((s.filter fun k ↦ ¬ AffProportional (a k) (c k) a₀ b₀).disjSum
      (s'.filter fun k ↦ ¬ AffProportional (a' k) (c' k) a₀ b₀))
    (Sum.elim (fun k ↦ affPoly K H (a k) (c k)) fun k ↦ affPoly K H (a' k) (c' k)) (by
      rintro (k | k) hk
      · rw [Finset.inl_mem_disjSum, Finset.mem_filter] at hk
        exact exists_eval_ne_zero_of_not_dvd ha₀ b₀
          fun hd ↦ hk.2 (affProportional_of_affPoly_dvd ha₀ (ha k hk.1) hd)
      · rw [Finset.inr_mem_disjSum, Finset.mem_filter] at hk
        exact exists_eval_ne_zero_of_not_dvd ha₀ b₀
          fun hd ↦ hk.2 (affProportional_of_affPoly_dvd ha₀ (ha' k hk.1) hd))
  obtain ⟨δ, hδ⟩ := exists_dual_apply_ne_zero (K := K) ha₀
  have hiff {a₁ : H} {c₁ : K} (ha₁ : a₁ ≠ 0)
      (hne : ¬ AffProportional a₁ c₁ a₀ b₀ → Λ₀ a₁ + c₁ ≠ 0) :
      (Λ₀ a₁ + c₁ = 0 ↔ AffProportional a₁ c₁ a₀ b₀) ∧
        (Λ₀ a₁ + c₁ = 0 → δ a₁ ≠ 0) := by
    refine ⟨⟨fun h0 ↦ by_contra fun hn ↦ hne hn h0, fun hp ↦ hp.evalPoly_eq_zero hΛ₀⟩,
      fun h0 ↦ ?_⟩
    obtain ⟨u, hu, rfl, -⟩ := (by_contra fun hn ↦ hne hn h0 : AffProportional a₁ c₁ a₀ b₀).ne_zero
      ha₁
    rw [map_smul, smul_eq_mul]
    exact mul_ne_zero hu hδ
  have hs (k : κ) (hk : k ∈ s) := hiff (ha k hk) fun hn ↦ by
    simpa using hgen (.inl k) (Finset.inl_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨hk, hn⟩))
  have hs' (k : κ') (hk : k ∈ s') := hiff (ha' k hk) fun hn ↦ by
    simpa using hgen (.inr k) (Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨hk, hn⟩))
  have := congrArg (fun F ↦ (linePoly K H Λ₀ δ F).natTrailingDegree) h
  rw [natTrailingDegree_linePoly_prod s a c e hc₀ fun k hk ↦ (hs k hk).2,
    natTrailingDegree_linePoly_prod s' a' c' e' hc₀' fun k hk ↦ (hs' k hk).2] at this
  rwa [Finset.filter_congr fun k hk ↦ (hs k hk).1,
    Finset.filter_congr fun k hk ↦ (hs' k hk).1] at this

open Classical in
/-- **A product of affine polynomials is determined up to a scalar by the multiplicities of its
hyperplanes**: if for every `k₀` the sums of the exponents `e_k` and `f_k` over the factors
proportional to `λ(a_{k₀}) + c_{k₀}` agree, then `∏_k (λ(a_k) + c_k)^{e_k}` and
`∏_k (λ(a_k) + c_k)^{f_k}` differ by a nonzero scalar. -/
theorem exists_prod_pow_eq_C_mul_prod_pow {κ : Type*} (s : Finset κ) {a : κ → H} (c : κ → K)
    (ha : ∀ k ∈ s, a k ≠ 0) (e f : κ → ℕ)
    (h : ∀ k₀ ∈ s, ∑ k ∈ s with AffProportional (a k) (c k) (a k₀) (c k₀), e k =
      ∑ k ∈ s with AffProportional (a k) (c k) (a k₀) (c k₀), f k) :
    ∃ u : K, u ≠ 0 ∧ ∏ k ∈ s, affPoly K H (a k) (c k) ^ e k =
      MvPolynomial.C u * ∏ k ∈ s, affPoly K H (a k) (c k) ^ f k := by
  induction hn : ∑ k ∈ s, e k generalizing e f with
  | zero =>
    have he : ∀ k ∈ s, e k = 0 := Finset.sum_eq_zero_iff.mp hn
    have hf : ∀ k ∈ s, f k = 0 := fun k₀ hk₀ ↦ by
      have := h k₀ hk₀
      rw [Finset.sum_eq_zero fun k hk ↦ he k (Finset.mem_filter.mp hk).1] at this
      exact Finset.sum_eq_zero_iff.mp this.symm k₀
        (Finset.mem_filter.mpr ⟨hk₀, AffProportional.refl _ _⟩)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_mul, Finset.prod_eq_one fun k hk ↦ by rw [he k hk, pow_zero],
      Finset.prod_eq_one fun k hk ↦ by rw [hf k hk, pow_zero]]
  | succ n ih =>
    obtain ⟨k₀, hk₀, he₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hn.trans_ne n.succ_ne_zero)
    have hpos : ∑ k ∈ s with AffProportional (a k) (c k) (a k₀) (c k₀), f k ≠ 0 := by
      rw [← h k₀ hk₀]
      exact fun h0 ↦ he₀ (Finset.sum_eq_zero_iff.mp h0 k₀
        (Finset.mem_filter.mpr ⟨hk₀, AffProportional.refl _ _⟩))
    obtain ⟨k₁, hk₁', hf₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
    obtain ⟨hk₁, hprop⟩ := Finset.mem_filter.mp hk₁'
    obtain ⟨v, hv, hva, hvc⟩ := hprop.ne_zero (ha k₁ hk₁)
    have hsum_mem {g : κ → ℕ} {k₂ : κ} (hg : g k₂ ≠ 0) {t : Finset κ} (ht : k₂ ∈ t) :
        ∑ k ∈ t, Function.update g k₂ (g k₂ - 1) k + 1 = ∑ k ∈ t, g k := by
      rw [Finset.sum_update_of_mem ht, ← Finset.sum_erase_add _ _ ht,
        Finset.sdiff_singleton_eq_erase]
      omega
    have hsum_not {g : κ → ℕ} {k₂ : κ} {t : Finset κ} (ht : k₂ ∉ t) :
        ∑ k ∈ t, Function.update g k₂ (g k₂ - 1) k = ∑ k ∈ t, g k :=
      Finset.sum_update_of_notMem ht _ _
    obtain ⟨u, hu, hprod⟩ := ih (Function.update e k₀ (e k₀ - 1))
      (Function.update f k₁ (f k₁ - 1)) (fun k₂ hk₂ ↦ by
        have hiff : k₀ ∈ s.filter (fun k ↦ AffProportional (a k) (c k) (a k₂) (c k₂)) ↔
            k₁ ∈ s.filter (fun k ↦ AffProportional (a k) (c k) (a k₂) (c k₂)) := by
          simp only [Finset.mem_filter, hk₀, hk₁, true_and]
          exact ⟨hprop.trans, (hprop.symm (ha k₁ hk₁)).trans⟩
        have := h k₂ hk₂
        by_cases h0 : k₀ ∈ s.filter (fun k ↦ AffProportional (a k) (c k) (a k₂) (c k₂))
        · have h1 := hsum_mem he₀ h0
          have h2 := hsum_mem hf₁ (hiff.mp h0)
          omega
        · rw [hsum_not h0, hsum_not (hiff.not.mp h0)]
          exact this) (by
        have := hsum_mem he₀ hk₀
        omega)
    have hsplit {g : κ → ℕ} {k₂ : κ} (hk₂ : k₂ ∈ s) (hg : g k₂ ≠ 0) :
        ∏ k ∈ s, affPoly K H (a k) (c k) ^ g k = affPoly K H (a k₂) (c k₂) *
          ∏ k ∈ s, affPoly K H (a k) (c k) ^ Function.update g k₂ (g k₂ - 1) k := by
      rw [← Finset.mul_prod_erase _ _ hk₂, ← Finset.mul_prod_erase _ _ hk₂,
        Function.update_self, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hg)]
      congr 1
      exact Finset.prod_congr rfl fun k hk ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    refine ⟨u * v⁻¹, mul_ne_zero hu (inv_ne_zero hv), ?_⟩
    have hC : MvPolynomial.C (u * v⁻¹) * MvPolynomial.C v = (MvPolynomial.C u :
        MvPolynomial (PolyIdx K H) K) := by
      rw [← map_mul, mul_assoc, inv_mul_cancel₀ hv, mul_one]
    rw [hsplit hk₀ he₀, hsplit hk₁ hf₁, hprod, AffProportional.affPoly_eq hva hvc,
      ← mul_assoc (MvPolynomial.C (u * v⁻¹)), ← mul_assoc (MvPolynomial.C (u * v⁻¹)), hC]
    ring

end Module.Dual
