/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Syzygy

/-!
# Local nilpotence on actual BGG cycles modulo incoming boundaries

## Main results

* `BGGIntegrable.exists_pow_mem_bggMap_range`: the rank-one quotient is locally
  nilpotent for the actual chosen BGG map, via one-dimensionality of Verma homomorphisms.
* `BGGIntegrable.exists_pow_ascent_boundary`: finite-support assembly produces an actual
  incoming boundary agreeing with a power of any vector on all simple-ascent coordinates.
* `BGGIntegrable.exists_pow_mem_range_of_cycle`: for cycles, the descent detector identifies
  that power with the actual boundary. This holds for arbitrary generalized Cartan matrices.

## References

Heckenberger–Kolb, *On the Bernstein–Gelfand–Gelfand resolution for Kac–Moody
algebras and quantized enveloping algebras*, arXiv:math/0605460, §3.1, Lemma 3.3 and
Proposition 3.4 (consulted). The proof implements their ascent/descent argument directly
on finitely supported vectors, without claiming that homology embeds into the direct sum
of rank-one quotients.
-/

open Module LieModule CoxeterSystem DirectSum
noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra
namespace BGGIntegrable

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan) {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

local notation "W" => P.weylGroup hA
local notation "cs" => P.coxeterSystem hA

/-- Rank-one nilpotence modulo the range of the actual chosen BGG embedding. -/
theorem exists_pow_mem_bggMap_range {w : W} {i : ι}
    (hw : ¬ (cs).IsLeftDescent w i) (x : VermaModule P (P.weylDot hA w Λ)) :
    ∃ N, (toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) x ∈
      (bggMap P hA hΛ ((cs).simple i * w) w).range := by
  obtain ⟨n, hn0, hn⟩ := P.exists_weylDot_add_rho_coroot_eq hA hΛ hw
  have hcov := (cs).bruhatCovBy_simple_mul_of_not_isLeftDescent hw
  have hne : bggMap P hA hΛ ((cs).simple i * w) w ≠ 0 := by
    intro h
    exact VermaModule.hwv_ne_zero P _ (bggMap_injective P hA hΛ hcov.1
      (by rw [h, map_zero, _root_.zero_apply]))
  have hr := range_eq_of_finrank_hom_eq_one P (P.weylDot_simple_mul hA i w Λ)
    (VermaModule.finrank_hom_simple_mul hA hΛ hw) hne
    (VermaModule.reflectionHom_ne_zero hA hn0 hn)
  let q := LieSubmodule.Quotient.mk' (VermaModule.reflectionHom hA hn0 hn).range
  obtain ⟨N, hN⟩ := VermaModule.exists_toEnd_f_pow_quotient_eq_zero hA hn0 hn (q x)
  refine ⟨N, ?_⟩
  rw [hr]
  rw [toEnd_pow_apply_map, LieSubmodule.Quotient.mk'_apply,
    LieSubmodule.Quotient.mk_eq_zero'] at hN
  exact hN

/-- A power of a simple lowering operator acts coordinatewise on a BGG term. -/
lemma pow_apply_coordinate (k : ℕ) (i : ι) (N : ℕ) (x : BGGTerm P hA Λ k)
    (w : {w : W // (cs).length w = k}) :
    ((toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) x) w =
      (toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) (x w) :=
  (toEnd_pow_apply_map (DirectSum.lieModuleComponent K _ P.KacMoodyAlgebra
    (fun w : {w : W // (cs).length w = k} ↦ VermaModule P (P.weylDot hA w Λ)) w)
    N (f P i) x).symm

open Classical in
/-- Simple lowering powers commute with the actual inclusion of a Verma summand. -/
lemma pow_apply_of (k : ℕ) (i : ι) (N : ℕ)
    (w : {w : W // (cs).length w = k}) (x : VermaModule P (P.weylDot hA w Λ)) :
    (toEnd K P.KacMoodyAlgebra (BGGTerm P hA Λ k) (f P i) ^ N)
        (DirectSum.of _ w x) =
      DirectSum.of _ w ((toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) x) :=
  toEnd_pow_apply_map (DirectSum.lieModuleOf K _ P.KacMoodyAlgebra
    (fun w : {w : W // (cs).length w = k} ↦ VermaModule P (P.weylDot hA w Λ)) w)
    N (f P i) x

open Classical in
/-- The incoming simple-descent summand has only its paired simple-ascent coordinate. -/
lemma incoming_ascent_coordinate (k : ℕ) (i : ι)
    (w : {w : W // (cs).length w = k}) (hw : ¬ (cs).IsLeftDescent w i)
    (m : VermaModule P (P.weylDot hA ((cs).simple i * w) Λ))
    (v : {w : W // (cs).length w = k}) (hv : ¬ (cs).IsLeftDescent v i) :
    (bggDiff P hA hΛ k (DirectSum.of _
      (⟨(cs).simple i * w, ((cs).not_isLeftDescent_iff.mp hw).trans
        (congrArg (· + 1) w.2)⟩ : {u : W // (cs).length u = k + 1}) m)) v =
      (DirectSum.of (fun w : {w : W // (cs).length w = k} ↦
        VermaModule P (P.weylDot hA w Λ)) w
        (bggSign P hA w ((cs).simple i * w) •
          bggMap P hA hΛ ((cs).simple i * w) w m)) v := by
  classical
  rw [BGGSyzygy.bggDiff_of_apply]
  by_cases hvw : v = w
  · subst v
    rw [ite_eq_left ((cs).bruhatCovBy_simple_mul_of_not_isLeftDescent hw)]
    simp
  · have hD : (cs).IsLeftDescent ((cs).simple i * w) i := by
      rw [(cs).isLeftDescent_iff_not_isLeftDescent_mul,
        (cs).simple_mul_simple_cancel_left]
      exact hw
    have hnc : ¬ (cs).BruhatCovBy v ((cs).simple i * w) := by
      intro h
      have heq := h.eq_simple_mul hD hv
      have hvw' : (v : W) = w := by simpa using heq
      exact hvw (Subtype.ext hvw')
    rw [ite_eq_right hnc]
    simp [DirectSum.of_apply, Ne.symm hvw]

open Classical in
/-- Every single summand is nilpotent modulo boundaries and descent summands. -/
lemma exists_pow_ascent_boundary_of (k : ℕ) (i : ι)
    (w : {w : W // (cs).length w = k}) (x : VermaModule P (P.weylDot hA w Λ)) :
    ∃ N, ∃ y : BGGTerm P hA Λ (k + 1),
      ∀ v : {w : W // (cs).length w = k}, ¬ (cs).IsLeftDescent v i →
      ((toEnd K P.KacMoodyAlgebra (BGGTerm P hA Λ k) (f P i) ^ N)
        (DirectSum.of _ w x)) v = (bggDiff P hA hΛ k y) v := by
  classical
  by_cases hw : (cs).IsLeftDescent w i
  · refine ⟨0, 0, fun v hv ↦ ?_⟩
    have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    simp [DirectSum.of_apply, hwv]
  · obtain ⟨N, m, hm⟩ := exists_pow_mem_bggMap_range P hA hΛ hw x
    let c := bggSign P hA w ((cs).simple i * w)
    have hc : c ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    refine ⟨N, DirectSum.of _
      (⟨(cs).simple i * w, ((cs).not_isLeftDescent_iff.mp hw).trans
        (congrArg (· + 1) w.2)⟩ : {u : W // (cs).length u = k + 1})
      (c⁻¹ • m), fun v hv ↦ ?_⟩
    rw [incoming_ascent_coordinate P hA hΛ k i w hw _ v hv, pow_apply_of]
    rw [map_smul (bggMap P hA hΛ ((cs).simple i * w) w) c⁻¹ m,
      smul_smul, mul_inv_cancel₀ hc, one_smul, hm]

/-- Powers preserve equality of simple-ascent coordinates. -/
lemma ascent_coordinates_pow (k : ℕ) (i : ι) (N : ℕ)
    {x y : BGGTerm P hA Λ k}
    (h : ∀ w : {w : W // (cs).length w = k},
      ¬ (cs).IsLeftDescent w i → x w = y w) :
    ∀ w : {w : W // (cs).length w = k}, ¬ (cs).IsLeftDescent w i →
      ((toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) x) w =
      ((toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) y) w := by
  intro w hw
  rw [pow_apply_coordinate, pow_apply_coordinate, h w hw]

set_option maxHeartbeats 1000000 in
-- Finite-support induction and dependent coefficient actions exceed the default elaboration fuel.
/-- Finite-support assembly of the rank-one argument. No finite Weyl group is needed. -/
theorem exists_pow_ascent_boundary (k : ℕ) (i : ι) (x : BGGTerm P hA Λ k) :
    ∃ N, ∃ y : BGGTerm P hA Λ (k + 1),
      ∀ w : {w : W // (cs).length w = k}, ¬ (cs).IsLeftDescent w i →
      ((toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) x) w =
        (bggDiff P hA hΛ k y) w := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | of w x => exact exists_pow_ascent_boundary_of P hA hΛ k i w x
  | add x z hx hz =>
    obtain ⟨N, y, hy⟩ := hx
    obtain ⟨M, t, ht⟩ := hz
    refine ⟨M + N,
      (toEnd K P.KacMoodyAlgebra _ (f P i) ^ M) y +
      (toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) t, fun w hw ↦ ?_⟩
    have hy' := ascent_coordinates_pow P hA k i M hy w hw
    have ht' := ascent_coordinates_pow P hA k i N ht w hw
    rw [toEnd_pow_apply_map] at hy' ht'
    rw [map_add, DFinsupp.add_apply, map_add, DFinsupp.add_apply]
    congr 1
    · rw [pow_add, Module.End.mul_apply]
      exact hy'
    · rw [Nat.add_comm M N, pow_add, Module.End.mul_apply]
      exact ht'

/-- Each simple lowering operator acts locally nilpotently on every actual
positive-degree BGG cycle modulo actual incoming boundaries. This is the lowering-operator
part of Heckenberger–Kolb, arXiv:math/0605460, Proposition 3.4 (consulted), using Lemma 3.3.
No exactness, symmetrizability, or coinvariant-detection hypothesis is used. -/
theorem exists_pow_mem_range_of_cycle (k : ℕ) (i : ι)
    (x : BGGTerm P hA Λ (k + 1)) (hx : bggDiff P hA hΛ k x = 0) :
    ∃ N, (toEnd K P.KacMoodyAlgebra _ (f P i) ^ N) x ∈
      (bggDiff P hA hΛ (k + 1)).range := by
  obtain ⟨N, y, hy⟩ := exists_pow_ascent_boundary P hA hΛ (k + 1) i x
  refine ⟨N, y, ?_⟩
  apply BGGSyzygy.cycle_eq_of_ascent_coordinates P hA hΛ k i
  · exact LieModuleHom.congr_fun (bggDiff_comp_bggDiff P hA hΛ k) y
  · rw [← toEnd_pow_apply_map, hx, map_zero]
  · intro w hw
    exact (hy w hw).symm

end BGGIntegrable
end Matrix.Realization.KacMoodyAlgebra

