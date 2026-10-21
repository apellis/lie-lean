/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Families
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Hyperplane
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Polynomial families: substitution and density on hyperplanes

Complements to `Matrix.Realization.KacMoodyAlgebra.VermaModule.polyFam` (polynomial families
`λ ↦ F(λ) ∈ U(𝔫₋)`) used for Shapovalov elements ([HumO] §4.12–4.13):

* `comp_mem_polyFam`: substituting a polynomial map `𝔥* → 𝔥*` into a polynomial family gives a
  polynomial family;
* `dual_mem_polyFun`: a linear functional applied to a polynomial family is a polynomial function;
* `mem_of_forall_nat`: if `F(λ)` lies in a subspace `W` for all `λ` on the hyperplane
  `φ(λ) = c` with `ψ(λ) ∈ -ℕ_{≥ N}` (`φ`, `ψ` linear), and some `δ ∈ 𝔥*` has `φ(δ) = 0`,
  `ψ(δ) = 1`, then
  `F(λ) ∈ W` on the whole hyperplane (the Zariski density argument of [HumO] §4.13);
* `descPochhammer_mem_polyFun`, `choose_eq_descPochhammer`: binomial coefficients `C(n, j)` as
  polynomials in `n`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §4.13.
-/

open Module Module.Dual

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H}

local notation "𝒰⁻" => UniversalEnvelopingAlgebra K (nNeg P)

/-! ### Polynomial functions -/

omit [CharZero K] in
lemma exists_mem_polyLE_of_mem_polyFun {c : Dual K H → K} (hc : c ∈ polyFun K H) :
    ∃ d, c ∈ polyLE K H d := by
  obtain ⟨p, rfl⟩ := hc
  exact ⟨p.totalDegree, mem_polyLE.mpr ⟨p, le_rfl, rfl⟩⟩

omit [CharZero K] in
lemma smul_mem_polyFam_of_mem_polyFun {c : Dual K H → K} (hc : c ∈ polyFun K H)
    {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) : (fun Λ ↦ c Λ • F Λ) ∈ polyFam P := by
  obtain ⟨d, hd⟩ := exists_mem_polyLE_of_mem_polyFun hc
  exact smul_mem_polyFam hd hF

omit [CharZero K] in
lemma smul_const_mem_polyFam_of_mem_polyFun {c : Dual K H → K} (hc : c ∈ polyFun K H)
    (u : 𝒰⁻) : (fun Λ ↦ c Λ • u) ∈ polyFam P :=
  smul_mem_polyFam_of_mem_polyFun hc (const_mem_polyFam u)

omit [CharZero K] in
lemma apply_mem_polyFun (a : H) : (fun Λ : Dual K H ↦ Λ a) ∈ polyFun K H :=
  ⟨linPoly K H a, funext fun Λ ↦ evalPoly_linPoly a Λ⟩

omit [CharZero K] in
lemma const_mem_polyFun (c : K) : (fun _ : Dual K H ↦ c) ∈ polyFun K H :=
  ⟨MvPolynomial.C c, funext fun Λ ↦ evalPoly_C c Λ⟩

/-! ### Substitution -/

omit [CharZero K] in
/-- Substituting a polynomial map `T : 𝔥* → 𝔥*` into a polynomial family gives a polynomial
family. -/
theorem comp_mem_polyFam {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) {T : Dual K H → Dual K H}
    (hT : ∀ j, (fun Λ ↦ T Λ (Module.Free.chooseBasis K H j)) ∈ polyFun K H) :
    (fun Λ ↦ F (T Λ)) ∈ polyFam P := by
  choose g hg using hT
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, u, rfl⟩ := hF
    refine Submodule.subset_span ⟨MvPolynomial.aeval g p, u, funext fun Λ ↦ ?_⟩
    have hgΛ : (fun j ↦ evalPoly K H (g j) Λ) = fun j ↦ T Λ (Module.Free.chooseBasis K H j) :=
      funext fun j ↦ congrFun (hg j) Λ
    simp only
    rw [evalPoly_aeval, hgΛ, evalPoly_apply]
  | zero => exact zero_mem_polyFam
  | add F G _ _ hF hG => exact add_mem_polyFam hF hG
  | smul a F _ hF => exact const_smul_mem_polyFam a hF

omit [CharZero K] in
/-- Substituting `λ ↦ λ + c(λ) δ + δ₀` with `c` polynomial into a polynomial family gives a
polynomial family. -/
theorem comp_add_smul_mem_polyFam {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P)
    {c : Dual K H → K} (hc : c ∈ polyFun K H) (δ δ₀ : Dual K H) :
    (fun Λ ↦ F (Λ + c Λ • δ + δ₀)) ∈ polyFam P := by
  refine comp_mem_polyFam hF fun j ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  exact add_mem (add_mem (apply_mem_polyFun _) (mul_mem hc (const_mem_polyFun _)))
    (const_mem_polyFun _)

/-! ### Linear functionals -/

omit [CharZero K] in
/-- A linear functional applied to a polynomial family is a polynomial function. -/
theorem dual_mem_polyFun (φ : 𝒰⁻ →ₗ[K] K) {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) :
    (fun Λ ↦ φ (F Λ)) ∈ polyFun K H := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨p, u, rfl⟩ := hF
    refine ⟨p * MvPolynomial.C (φ u), funext fun Λ ↦ ?_⟩
    simp
  | zero =>
    have h : (fun Λ ↦ φ ((0 : Dual K H → 𝒰⁻) Λ)) = 0 := funext fun Λ ↦ by simp
    rw [h]
    exact zero_mem _
  | add F G _ _ hF hG =>
    have h : (fun Λ ↦ φ ((F + G) Λ)) = (fun Λ ↦ φ (F Λ)) + fun Λ ↦ φ (G Λ) :=
      funext fun Λ ↦ by simp
    rw [h]
    exact add_mem hF hG
  | smul a F _ hF =>
    have h : (fun Λ ↦ φ ((a • F) Λ)) = a • fun Λ ↦ φ (F Λ) := funext fun Λ ↦ by simp
    rw [h]
    exact Subalgebra.smul_mem _ hF a

/-! ### Density on hyperplanes -/

/-- A polynomial function vanishing at the points of the hyperplane `φ(λ) = c` with
`ψ(λ) ∈ -ℕ_{≥ N}` vanishes on the hyperplane, provided some `δ` has `φ(δ) = 0`, `ψ(δ) = 1`. -/
theorem eq_zero_of_forall_nat {F : Dual K H → K} (hF : F ∈ polyFun K H)
    {φ ψ : Dual K H →ₗ[K] K} {c : K} {δ : Dual K H} (hδa : φ δ = 0) (hδb : ψ δ = 1) (N : ℕ)
    (h : ∀ Λ : Dual K H, φ Λ = c → ∀ m : ℕ, N ≤ m → ψ Λ = -(m : K) → F Λ = 0)
    {Λ : Dual K H} (hΛ : φ Λ = c) : F Λ = 0 := by
  obtain ⟨p, rfl⟩ := hF
  have hG : linePoly K H Λ δ p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ ↦ -((N + m : ℕ) : K) - ψ Λ)
      (fun m m' hmm ↦ ?_) fun m ↦ ?_
    · have h1 := neg_injective (sub_left_injective hmm)
      exact Nat.add_left_cancel (Nat.cast_injective h1)
    · change (linePoly K H Λ δ p).eval _ = 0
      rw [eval_linePoly]
      refine h _ ?_ (N + m) (Nat.le_add_right N m) ?_
      · rw [map_add, map_smul, hδa, smul_zero, add_zero, hΛ]
      · rw [map_add, map_smul, hδb, smul_eq_mul, mul_one]
        ring
  have h0 := eval_linePoly Λ δ p 0
  rw [hG, Polynomial.eval_zero, zero_smul, add_zero] at h0
  exact h0.symm

/-- A polynomial family with values in a subspace `W` at the points of the hyperplane `φ(λ) = c`
with `ψ(λ) ∈ -ℕ_{≥ N}` has values in `W` on the hyperplane, provided some `δ` has `φ(δ) = 0`,
`ψ(δ) = 1`. -/
theorem mem_of_forall_nat {F : Dual K H → 𝒰⁻} (hF : F ∈ polyFam P) (W : Submodule K 𝒰⁻)
    {φ ψ : Dual K H →ₗ[K] K} {c : K} {δ : Dual K H} (hδa : φ δ = 0) (hδb : ψ δ = 1) (N : ℕ)
    (h : ∀ Λ : Dual K H, φ Λ = c → ∀ m : ℕ, N ≤ m → ψ Λ = -(m : K) → F Λ ∈ W)
    {Λ : Dual K H} (hΛ : φ Λ = c) : F Λ ∈ W := by
  by_contra hW
  obtain ⟨χ, hχ, hχW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hW inferInstance
  refine hχ (eq_zero_of_forall_nat (dual_mem_polyFun χ hF) hδa hδb N
    (fun Λ' hΛ' m hm hb ↦ ?_) hΛ)
  have := Submodule.mem_map_of_mem (f := χ) (h Λ' hΛ' m hm hb)
  rwa [hχW, Submodule.mem_bot] at this

/-! ### Binomial coefficients -/

omit [CharZero K] in
lemma descPochhammer_mem_polyFun {c : Dual K H → K} (hc : c ∈ polyFun K H) (j : ℕ) :
    (fun Λ ↦ (descPochhammer K j).eval (c Λ)) ∈ polyFun K H := by
  obtain ⟨p, rfl⟩ := hc
  refine ⟨Polynomial.aeval p (descPochhammer K j), funext fun Λ ↦ ?_⟩
  have h := Polynomial.aeval_algHom_apply (Pi.evalAlgHom K (fun _ : Dual K H ↦ K) Λ)
    (evalPoly K H p) (descPochhammer K j)
  change evalPoly K H (Polynomial.aeval p (descPochhammer K j)) Λ =
    Polynomial.eval (evalPoly K H p Λ) (descPochhammer K j)
  rw [← Polynomial.aeval_algHom_apply (evalPoly K H), ← Polynomial.coe_aeval_eq_eval]
  exact h.symm

lemma choose_eq_descPochhammer (n j : ℕ) :
    (n.choose j : K) = (descPochhammer K j).eval (n : K) / j.factorial := by
  rw [descPochhammer_eval_eq_descFactorial K, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, mul_div_cancel_left₀ _ (by exact_mod_cast j.factorial_ne_zero)]

end Matrix.Realization.KacMoodyAlgebra.VermaModule
