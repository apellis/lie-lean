/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.LinearAlgebra.Matrix.Cartan.IntegralSimpleRoots

/-!
# Weights on a single integral wall

Let `A` be a Cartan matrix of finite type with a realization over a field `K` of characteristic
zero, and let `x` be a weight with `⟨x, β^∨⟩ ∈ ℤ_{<0}` for every positive root `β` integral for
`x` (`x = λ + ρ`, `λ` antidominant and regular). For a simple integral root `γ`
(`Matrix.Realization.exists_isPosRoot_reflectionOf_mul`) we construct an integral weight `c` such
that `x + c` lies on the wall of `γ` and on no other integral wall, with `⟨x + c, β^∨⟩ < 0` for
the other positive integral roots, provided `x` is deep enough in its chamber. This supplies the
weights `μ` of the wall-crossing functors `Θ_s = T_μ^λ T_λ^μ` for the simple reflections of the
integral Weyl group `W_[λ]` (Humphreys, GSM 94, §7.15, §7.16).

## Main results

* `Matrix.Realization.exists_int_corootPairing_of_integral`: integral weights pair integrally
  with every real coroot.
* `Matrix.Realization.one_le_of_corootPairing_rho_eq`: `⟨ρ, β^∨⟩ ≥ 1` for every positive root.
* `Matrix.Realization.exists_wall_shift`: the wall weight. With `n = -⟨x, γ^∨⟩ = 2q + ε`,
  `ε ∈ {0, 1}`, and `γ = u αⱼ`, the shift is `c = q γ + ε (u ρ)`; the proof is our own (for
  `β ≠ γ`, `2⟨x + c, β^∨⟩ = ⟨x, β^∨⟩ + ⟨x, (s_γ β)^∨⟩ + ε ⟨2 u ρ - γ, β^∨⟩`, and the last term is
  bounded independently of `x`).

## References

* J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  AMS 2008, §7.15, §7.16.
-/

noncomputable section

open Module CoxeterSystem

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} (hF : A.IsFiniteCartan)

omit [DecidableEq ι] [CharZero K] in
/-- Integral weights pair integrally with every real coroot. -/
lemma exists_int_corootPairing_of_integral {hA : A.IsGeneralizedCartan} {c : Dual K H}
    (hc : ∀ t, ∃ z : ℤ, c (P.coroot t) = z) (v : P.weylGroup hA) (i : ι) :
    ∃ m : ℤ, P.corootPairing hA c v i = m := by
  obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA (v⁻¹).2 hc
  obtain ⟨z, hz⟩ := hc i
  refine ⟨z + (A *ᵥ k) i, ?_⟩
  change ((v⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) c (P.coroot i) = _
  rw [hk, LinearMap.add_apply, hz, P.rootOf_apply_coroot]
  exact (Int.cast_add _ _).symm

omit [DecidableEq ι] [CharZero K] in
/-- Simple roots are integral weights. -/
lemma root_integral (j t : ι) : ∃ z : ℤ, P.root j (P.coroot t) = z := by
  classical
  refine ⟨(A *ᵥ Pi.single j 1) t, ?_⟩
  rw [← P.rootOf_apply_coroot, rootOf_single]

omit [DecidableEq ι] [CharZero K] in
/-- Weyl group translates of integral weights are integral. -/
lemma apply_integral {hA : A.IsGeneralizedCartan} (w : P.weylGroup hA) {c : Dual K H}
    (hc : ∀ t, ∃ z : ℤ, c (P.coroot t) = z) (t : ι) :
    ∃ z : ℤ, (w : Dual K H ≃ₗ[K] Dual K H) c (P.coroot t) = z := by
  obtain ⟨k, hk⟩ := P.exists_apply_eq_add_rootOf hA w.2 hc
  obtain ⟨z, hz⟩ := hc t
  refine ⟨z + (A *ᵥ k) t, ?_⟩
  rw [hk, LinearMap.add_apply, hz, P.rootOf_apply_coroot]
  exact (Int.cast_add _ _).symm

variable [FiniteDimensional K H]

include hF in
/-- A positive definite symmetrization computes coroot pairings: if `β = v αᵢ = Σₜ bₜ αₜ`, then
`⟨y, β^∨⟩ dᵢ = Σₜ bₜ ⟨y, αₜ^∨⟩ dₜ`. -/
lemma exists_corootPairing_mul_eq_sum : ∃ d : ι → ℤ, (∀ t, 0 < d t) ∧
    ∀ {hA : A.IsGeneralizedCartan} (y : Dual K H) (v : P.weylGroup hA) (i : ι) (b : ι → ℤ),
      (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = P.rootOf b →
        P.corootPairing hA y v i * d i = ∑ t, (b t : K) * y (P.coroot t) * d t := by
  obtain ⟨d, hdpos, hpos⟩ := hF.exists_posDef
  have hsymm : (diagonal d * A).IsSymm := by
    simpa [IsHermitian, IsSymm] using hpos.isHermitian
  set S := Symmetrization.ofDiagonal d hdpos hsymm
  refine ⟨d, hdpos, fun {hA} y v i b hb ↦ ?_⟩
  set B := P.dualBilinForm S
  have hd (t : ι) : (d t : K) ≠ 0 := by exact_mod_cast (hdpos t).ne'
  have hroot (z : Dual K H) (t : ι) : B z (P.root t) = z (P.coroot t) * d t := by
    rw [dualBilinForm_root_right]
    simp only [S, Symmetrization.ofDiagonal]
    push_cast
    field_simp
  have hform : B y ((v : Dual K H ≃ₗ[K] Dual K H) (P.root i)) =
      P.corootPairing hA y v i * d i := by
    rw [← P.dualBilinForm_weylGroup hA S (v⁻¹).2, inv_apply_apply, hroot]
    rfl
  have hsum : B y (P.rootOf b) = ∑ t, (b t : K) * (y (P.coroot t) * d t) := by
    simp only [rootOf, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, map_smul, smul_eq_mul,
      hroot]
  rw [hb, hsum] at hform
  rw [← hform]
  exact Finset.sum_congr rfl fun t _ ↦ by ring

include hF in
/-- `⟨ρ, β^∨⟩ ≥ 1` for every positive real root `β`. -/
lemma one_le_of_corootPairing_rho_eq {hA : A.IsGeneralizedCartan} {v : P.weylGroup hA} {i : ι}
    (hv : P.IsPosRoot hA v i) {m : ℤ} (hm : P.corootPairing hA P.rho v i = m) : 1 ≤ m := by
  obtain ⟨d, hdpos, hd⟩ := exists_corootPairing_mul_eq_sum (P := P) hF
  obtain ⟨b, hb0, hb⟩ := hv
  have h := hd P.rho v i b hb
  simp only [rho_coroot, mul_one, hm] at h
  have hz : m * d i = ∑ t, b t * d t := by exact_mod_cast h
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hall
    have : b = 0 := funext fun s ↦ not_not.mp fun h ↦ hall ⟨s, h⟩
    rw [this, map_zero] at hb
    exact P.linearIndependent_root.ne_zero i ((LinearEquiv.map_eq_zero_iff _).mp hb)
  have hpos : 0 < ∑ t, b t * d t :=
    Finset.sum_pos' (fun s _ ↦ mul_nonneg (hb0 s) (hdpos s).le)
      ⟨t, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hb0 t) (Ne.symm ht)) (hdpos t)⟩
  have hdi := hdpos i
  by_contra h1
  have : m * d i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hdi.le
  omega

omit [FiniteDimensional K H] in
include hF in
/-- **A weight on a single integral wall.** Let `γ = u αⱼ` be a positive root. There is `D` such
that for every weight `x` with `⟨x, β^∨⟩ ∈ ℤ_{≤ -D}` for the positive roots `β` integral for `x`,
for which `γ` is integral and simple (`s_γ` permutes the other positive integral roots), some
integral weight `c` has `⟨x + c, γ^∨⟩ = 0` and `⟨x + c, β^∨⟩ ∈ ℤ_{<0}` for every other positive
root `β` with `⟨x + c, β^∨⟩ ∈ ℤ`. -/
theorem exists_wall_shift {hA : A.IsGeneralizedCartan} (u : P.weylGroup hA) (j : ι) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ x : Dual K H,
      (∀ v i, P.IsPosRoot hA v i → ∀ n : ℤ, P.corootPairing hA x v i = n → n ≤ -D) →
      P.IsPosRoot hA u j → P.IsIntegralRoot hA x u j →
      (∀ v i, P.IsPosRoot hA v i → P.IsIntegralRoot hA x v i →
        (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) ≠ (u : Dual K H ≃ₗ[K] Dual K H) (P.root j) →
          P.IsPosRoot hA (P.reflectionOf hA u j * v) i) →
      ∃ c : Dual K H, (∀ t, ∃ z : ℤ, c (P.coroot t) = z) ∧
        P.corootPairing hA (x + c) u j = 0 ∧
        ∀ v i, P.IsPosRoot hA v i → ∀ m : ℤ, P.corootPairing hA (x + c) v i = m →
          m < 0 ∨ (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) =
            (u : Dual K H ≃ₗ[K] Dual K H) (P.root j) := by
  classical
  have : Finite (P.weylGroup hA) := P.finite_weylGroup hF
  set γ := (u : Dual K H ≃ₗ[K] Dual K H) (P.root j) with hγdef
  set r := (u : Dual K H ≃ₗ[K] Dual K H) P.rho with hrdef
  have hγ : ∀ t, ∃ z : ℤ, γ (P.coroot t) = z := apply_integral u (root_integral j)
  have hr : ∀ t, ∃ z : ℤ, r (P.coroot t) = z :=
    apply_integral u fun t ↦ ⟨1, by rw [rho_coroot, Int.cast_one]⟩
  choose fγ hfγ using exists_int_corootPairing_of_integral (hA := hA) hγ
  choose fr hfr using exists_int_corootPairing_of_integral (hA := hA) hr
  obtain ⟨M, hM⟩ := (Set.finite_range fun p : P.weylGroup hA × ι ↦
    2 * fr p.1 p.2 - fγ p.1 p.2).bddAbove
  refine ⟨M.toNat + 1, by omega, fun x hdeep hu hux hsimple ↦ ?_⟩
  obtain ⟨a₀, ha₀⟩ := hux
  change P.corootPairing hA x u j = a₀ at ha₀
  have ha₀D := hdeep u j hu a₀ ha₀
  set n := (-a₀).toNat with hn
  have hna : (n : ℤ) = -a₀ := Int.toNat_of_nonneg (by omega)
  set q := n / 2
  set ε := n % 2
  have hqε : n = 2 * q + ε := (Nat.div_add_mod n 2).symm
  have hε : ε < 2 := Nat.mod_lt _ (by omega)
  refine ⟨(q : K) • γ + (ε : K) • r, fun t ↦ ?_, ?_, fun v i hv m hm ↦ ?_⟩
  · obtain ⟨z₁, hz₁⟩ := hγ t
    obtain ⟨z₂, hz₂⟩ := hr t
    refine ⟨q * z₁ + ε * z₂, ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hz₁, hz₂, smul_eq_mul,
      smul_eq_mul]
    push_cast
    ring
  · have hγγ : P.corootPairing hA γ u j = 2 := corootPairing_apply_root_self u j
    have hrr : P.corootPairing hA r u j = 1 := by
      rw [hrdef, corootPairing_apply, inv_mul_cancel, corootPairing_one, rho_coroot]
    rw [corootPairing_add, corootPairing_add, corootPairing_smul, corootPairing_smul, hγγ, hrr,
      ha₀]
    have : (a₀ : K) = -((2 * q + ε : ℕ) : K) := by
      rw [← hqε, ← Int.cast_natCast, hna, Int.cast_neg, neg_neg]
    rw [this]
    push_cast
    ring
  by_cases hvγ : (v : Dual K H ≃ₗ[K] Dual K H) (P.root i) = γ
  · exact Or.inr hvγ
  left
  have hc : P.corootPairing hA ((q : K) • γ + (ε : K) • r) v i = q * fγ v i + ε * fr v i := by
    rw [corootPairing_add, corootPairing_smul, corootPairing_smul, hfγ, hfr]
  set a := m - (q * fγ v i + ε * fr v i) with ha
  have hxa : P.corootPairing hA x v i = a := by
    rw [corootPairing_add, hc] at hm
    rw [ha]
    push_cast
    linear_combination hm
  have hvx : P.IsIntegralRoot hA x v i := ⟨a, hxa⟩
  have hsv := hsimple v i hv hvx hvγ
  have hb : P.corootPairing hA x (P.reflectionOf hA u j * v) i =
      ((a + fγ v i * n : ℤ) : K) := by
    have hnK : (n : K) = -(a₀ : K) := by exact_mod_cast hna
    rw [corootPairing_reflectionOf_mul, hxa, hfγ, ha₀]
    push_cast
    rw [hnK]
    ring
  have hbD := hdeep _ i hsv _ hb
  have haD := hdeep v i hv a hxa
  have hMv : 2 * fr v i - fγ v i ≤ M := hM ⟨(v, i), rfl⟩
  have hMt : M ≤ (M.toNat : ℤ) := Int.self_le_toNat M
  have h2m : 2 * m = a + (a + fγ v i * n) + ε * (2 * fr v i - fγ v i) := by
    rw [ha, hqε]
    push_cast
    ring
  interval_cases ε <;> push_cast at h2m ⊢ <;> omega

end Matrix.Realization
