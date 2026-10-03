/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG

/-!
# Simple-descent detection of actual BGG syzygies

## Main results

A cycle supported only on Weyl summands with a fixed simple left descent is zero.
Thus projection onto the complementary simple-ascent summands detects actual syzygies.
This is NOT detection modulo the nilradical action and does not claim BGG exactness.

## References

Heckenberger–Kolb, *On the Bernstein–Gelfand–Gelfand resolution for Kac–Moody
algebras and quantized enveloping algebras*, arXiv:math/0605460, Proposition 3.4,
last paragraph of its proof. The Bruhat input is already formalized as
`CoxeterSystem.BruhatCovBy.eq_simple_mul`.
-/

open Module LieModule CoxeterSystem DirectSum
noncomputable section
namespace Matrix.Realization.KacMoodyAlgebra
namespace BGGSyzygy

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)
  (hA : A.IsGeneralizedCartan) {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

local notation "W" => P.weylGroup hA
local notation "cs" => P.coxeterSystem hA

open Classical in
/-- A single coordinate of the actual differential on a Verma summand. -/
lemma bggDiff_of_apply (k : ℕ) (u : {u : W // (cs).length u = k + 1})
    (v : {v : W // (cs).length v = k}) (m : VermaModule P (P.weylDot hA u Λ)) :
    (bggDiff P hA hΛ k (DirectSum.of _ u m)) v =
      if (cs).BruhatCovBy v u then bggSign P hA v u • bggMap P hA hΛ u v m else 0 := by
  classical
  rw [bggDiff_of]
  by_cases hv : (cs).BruhatCovBy v u
  · rw [ite_eq_left hv]
    rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single v]
    · change bggSign P hA v u • (DirectSum.of (fun w : {w : W // (cs).length w = k} ↦
        VermaModule P (P.weylDot hA w Λ)) v (bggMap P hA hΛ u v m)) v = _
      simp
    · intro b hb hbv
      change bggSign P hA b u • (DirectSum.of (fun w : {w : W // (cs).length w = k} ↦
        VermaModule P (P.weylDot hA w Λ)) b (bggMap P hA hΛ u b m)) v = _
      simp [DirectSum.of_apply, hbv]
    · intro hv'
      exact (hv' ((mem_bggBoundary P hA).mpr hv)).elim
  · rw [ite_eq_right hv, DFinsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro b hb
    have hbv : b ≠ v := by
      rintro rfl
      exact hv ((mem_bggBoundary P hA).mp hb)
    change bggSign P hA b u • (DirectSum.of (fun w : {w : W // (cs).length w = k} ↦
        VermaModule P (P.weylDot hA w Λ)) b (bggMap P hA hΛ u b m)) v = _
    simp [DirectSum.of_apply, hbv]

/-- The actual BGG differential has trivial kernel on the sum of summands carrying
any fixed simple left descent. No lower exactness, CE vanishing, or coinvariant
surjectivity is assumed. This is the detector in Heckenberger–Kolb, Proposition 3.4. -/
theorem eq_zero_of_cycle_supported_on_leftDescents (k : ℕ) (i : ι)
    (x : BGGTerm P hA Λ (k + 1)) (hx : bggDiff P hA hΛ k x = 0)
    (hsupport : ∀ u : {u : W // (cs).length u = k + 1},
      ¬ (cs).IsLeftDescent u i → x u = 0) : x = 0 := by
  classical
  apply DFinsupp.ext
  intro u
  change x u = 0
  by_cases hu : (cs).IsLeftDescent u i
  · let v : {v : W // (cs).length v = k} :=
      ⟨(cs).simple i * u, by
        have hlen := (cs).isLeftDescent_iff.mp hu
        rw [u.2] at hlen
        omega⟩
    have hcov : (cs).BruhatCovBy v u :=
      (cs).bruhatCovBy_simple_mul_of_isLeftDescent hu
    have hv : ¬ (cs).IsLeftDescent v i :=
      (cs).isLeftDescent_iff_not_isLeftDescent_mul.mp hu
    have hcoord : (bggDiff P hA hΛ k x) v =
        bggSign P hA v u • bggMap P hA hΛ u v (x u) := by
      conv_lhs => rw [← DirectSum.sum_support_of x]
      rw [map_sum, DFinsupp.finsetSum_apply, Finset.sum_eq_single u]
      · rw [bggDiff_of_apply, ite_eq_left hcov]
      · intro b hb hbu
        by_cases hbD : (cs).IsLeftDescent b i
        · have hncov : ¬ (cs).BruhatCovBy v b := by
            intro h
            have heq := h.eq_simple_mul hbD hv
            have hval : (u : W) = b := mul_left_cancel heq
            exact hbu (Subtype.ext hval.symm)
          rw [bggDiff_of_apply, ite_eq_right hncov]
        · rw [hsupport b hbD, map_zero, map_zero]
          rfl
      · intro hus
        have hu0 : x u = 0 := DFinsupp.notMem_support_iff.mp hus
        rw [hu0, map_zero, map_zero]
        rfl
    rw [hx] at hcoord
    have hsign : bggSign P hA v u ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    have hm : bggMap P hA hΛ u v (x u) = 0 :=
      (smul_eq_zero.mp hcoord.symm).resolve_left hsign
    exact bggMap_injective P hA hΛ hcov.1 (hm.trans (map_zero _).symm)
  · exact hsupport u hu

/-- Equality of actual syzygies is detected by the simple-ascent coordinates alone.
This is a vector-level detector, not a nilradical-coinvariant detector. -/
theorem cycle_eq_of_ascent_coordinates (k : ℕ) (i : ι)
    (x y : BGGTerm P hA Λ (k + 1))
    (hx : bggDiff P hA hΛ k x = 0) (hy : bggDiff P hA hΛ k y = 0)
    (hxy : ∀ u : {u : W // (cs).length u = k + 1},
      ¬ (cs).IsLeftDescent u i → x u = y u) : x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_cycle_supported_on_leftDescents P hA hΛ k i
  · rw [map_sub, hx, hy, sub_self]
  · intro u hu
    change x u - y u = 0
    exact sub_eq_zero.mpr (hxy u hu)

/-- Projection of the actual BGG syzygy space onto the simple-ascent summands is
injective. This supplies the descent-elimination step of Heckenberger–Kolb's
integrable-homology proof without any assumed positive-degree BGG exactness. -/
theorem ascent_projection_injective_on_syzygy (k : ℕ) (i : ι) :
    Function.Injective (fun z : (bggDiff P hA hΛ k).ker ↦
      fun u : {u : {u : W // (cs).length u = k + 1} // ¬ (cs).IsLeftDescent u i} ↦
        z.1 u.1) := by
  intro x y hxy
  apply Subtype.ext
  apply cycle_eq_of_ascent_coordinates P hA hΛ k i x.1 y.1 x.2 y.2
  intro u hu
  exact congr_fun hxy ⟨u, hu⟩

end BGGSyzygy
end Matrix.Realization.KacMoodyAlgebra

