/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.RegularFiltration
import LieLean.Algebra.Lie.UniversalEnveloping.LeadingAction
import LieLean.LinearAlgebra.ExteriorAlgebra.KoszulSupport

/-!
# The actual regular CE differential has leading term negative Koszul

## Main definitions / results

* `pbwTensor`, `polynomialDiff`: the actual CE differential conjugated by PBW.
* `polynomialDiff_add_delta_mem`: negative Koszul is the leading differential, with
  lower-polynomial-degree error on the supported tensor span.

## References

The proof is reconstructed from the existing CE recursion, contraction identity and PBW
leading-action theorem. The finite set restricts exterior support only; no finiteness of the
basis index type is assumed.
-/

noncomputable section
open scoped TensorProduct BigOperators
open TensorProduct ExteriorAlgebra
open UniversalEnvelopingAlgebra (LeftRegular)
namespace LieModule.ChevalleyEilenberg.CELeading

variable {R L I : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder I] (b : Module.Basis I R L)
local notation "U" => LeftRegular R L
local notation "P" => MvPolynomial I R
local notation "EP" => ExteriorAlgebra R L ⊗[R] P

/-- The actual PBW equivalence on coefficient tensors. -/
def pbwTensor : (ExteriorAlgebra R L ⊗[R] U) ≃ₗ[R] EP :=
  TensorProduct.congr (LinearEquiv.refl R _) ((LeftRegular.equiv R L).trans
    (UniversalEnvelopingAlgebra.pbwEquiv b))

/-- Exterior degree `q` and polynomial degree at most `n`. -/
def rectangle (q n : ℕ) : Submodule R EP :=
  Submodule.span R {z | ∃ (e : ExteriorAlgebra R L), e ∈ ⋀[R]^q L ∧
    ∃ p : P, p ∈ MvPolynomial.restrictTotalDegree I R n ∧ z = e ⊗ₜ[R] p}

omit [LinearOrder I] in
lemma tmul_mem {q n : ℕ} {e : ExteriorAlgebra R L} (he : e ∈ ⋀[R]^q L)
    {p : P} (hp : p ∈ MvPolynomial.restrictTotalDegree I R n) :
    e ⊗ₜ[R] p ∈ rectangle (R := R) (L := L) (I := I) q n :=
  Submodule.subset_span ⟨e, he, p, hp, rfl⟩

/-- Exterior multiplication on polynomial tensors. -/
def wedgeP (x : L) : Module.End R EP :=
  TensorProduct.map (LinearMap.mulLeft R (ι R x)) LinearMap.id

omit [LinearOrder I] in
@[simp] lemma wedgeP_tmul (x : L) (e : ExteriorAlgebra R L) (p : P) :
    wedgeP (I := I) x (e ⊗ₜ[R] p) = (ι R x * e) ⊗ₜ[R] p := rfl

omit [LinearOrder I] in
lemma wedgeP_mem (x : L) {q n : ℕ} {z : EP}
    (hz : z ∈ rectangle q n) : wedgeP x z ∈ rectangle (q + 1) n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, p, hp, rfl⟩ := hz
    rw [wedgeP_tmul]
    apply tmul_mem _ hp
    rw [exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ x) he
  | zero => simpa only [map_zero] using (rectangle (q + 1) n).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r z _ hz => rw [map_smul]; exact Submodule.smul_mem _ r hz

@[simp] lemma pbwTensor_tmul (e : ExteriorAlgebra R L) (u : U) :
    pbwTensor b (e ⊗ₜ[R] u) =
      e ⊗ₜ[R] UniversalEnvelopingAlgebra.pbwEquiv b (LeftRegular.equiv R L u) := rfl

lemma pbwTensor_wedge (x : L) (c : ExteriorAlgebra R L ⊗[R] U) :
    pbwTensor b (wedge R L U x c) = wedgeP x (pbwTensor b c) := by
  induction c with
  | tmul e u => rfl
  | add c d hc hd => simp only [map_add, hc, hd]

/-- The exterior-adjoint part of the diagonal action does not raise coefficient degree. -/
lemma lieAction_error (x : L) (l : List I) (n : ℕ) (u : U)
    (hu : LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n) :
    pbwTensor b (lieAction R L U x (Koszul.basisWord b l ⊗ₜ[R] u)) -
      Koszul.basisWord b l ⊗ₜ[R]
        UniversalEnvelopingAlgebra.pbwEquiv b (LeftRegular.equiv R L ⁅x, u⁆) ∈
      rectangle l.length n := by
  induction l with
  | nil => simp [Koszul.basisWord]
  | cons i l ih =>
    change pbwTensor b (lieAction R L U x
      (wedge R L U (b i) (Koszul.basisWord b l ⊗ₜ[R] u))) -
      wedgeP (b i) (Koszul.basisWord b l ⊗ₜ[R]
        UniversalEnvelopingAlgebra.pbwEquiv b (LeftRegular.equiv R L ⁅x, u⁆)) ∈ _
    rw [lieAction_wedge, map_add, pbwTensor_wedge, pbwTensor_wedge,
      add_sub_assoc, ← map_sub]
    exact add_mem
      (wedgeP_mem _ (tmul_mem (Koszul.basisWord_mem_exteriorPower b l)
        ((UniversalEnvelopingAlgebra.mem_filtration_iff_pbwEquiv b).mp hu)))
      (wedgeP_mem _ ih)

/-- The finite Koszul sum obeys the positive contraction recursion. -/
lemma delta_wedge (s : Finset I) (j : I) (hj : j ∈ s)
    (e : ExteriorAlgebra R L) (p : P) :
    Koszul.delta b s ((ι R (b j) * e) ⊗ₜ[R] p) =
      e ⊗ₜ[R] (MvPolynomial.X j * p) - wedgeP (b j) (Koszul.delta b s (e ⊗ₜ[R] p)) := by
  classical
  change Koszul.delta b s (Koszul.wedge b j e ⊗ₜ[R] p) = _
  simp only [Koszul.delta, LinearMap.sum_apply, Koszul.deltaTerm_tmul,
    Koszul.contract_wedge,
    sub_tmul, Finset.sum_sub_distrib, map_sum, wedgeP_tmul]
  simp only [Koszul.wedge_apply]
  congr 1
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    TensorProduct.ite_tmul, hj]

/-- Under actual PBW, the CE differential is negative Koszul modulo polynomial degree `n`,
one below its expected degree `n+1`. Reconstructed from `diff_wedge` and PBW leading action.
Only the exterior word must be supported in `s`; the polynomial may involve other variables. -/
theorem diff_add_delta_basisWord (s : Finset I) (l : List I)
    (hl : ∀ i ∈ l, i ∈ s) (n : ℕ) (u : U)
    (hu : LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n) :
    pbwTensor b (diff R L U (Koszul.basisWord b l ⊗ₜ[R] u)) +
      Koszul.delta b s (pbwTensor b (Koszul.basisWord b l ⊗ₜ[R] u)) ∈
      rectangle (l.length - 1) n := by
  induction l with
  | nil => simp [Koszul.basisWord, Koszul.delta, Koszul.deltaTerm_tmul, Koszul.contract]
  | cons j l ih =>
    let p := UniversalEnvelopingAlgebra.pbwEquiv b (LeftRegular.equiv R L u)
    have haction : pbwTensor b (lieAction R L U (b j)
        (Koszul.basisWord b l ⊗ₜ[R] u)) -
        Koszul.basisWord b l ⊗ₜ[R] (MvPolynomial.X j * p) ∈ rectangle l.length n := by
      have hc := tmul_mem (Koszul.basisWord_mem_exteriorPower b l)
        (UniversalEnvelopingAlgebra.pbwEquiv_ι_basis_mul_sub_mem b j n hu)
      rw [tmul_sub] at hc
      have ha := lieAction_error b (b j) l n u hu
      rw [LeftRegular.equiv_lie] at ha
      convert add_mem ha hc using 1
      abel
    have htail : wedgeP (b j)
        (pbwTensor b (diff R L U (Koszul.basisWord b l ⊗ₜ[R] u)) +
          Koszul.delta b s (pbwTensor b (Koszul.basisWord b l ⊗ₜ[R] u))) ∈
        rectangle l.length n := by
      cases l with
      | nil => simp [Koszul.basisWord, Koszul.delta, Koszul.deltaTerm_tmul, Koszul.contract]
      | cons i l =>
        exact wedgeP_mem _ (ih (fun i hi => hl i (List.mem_cons_of_mem j hi)))
    change pbwTensor b (diff R L U
      (wedge R L U (b j) (Koszul.basisWord b l ⊗ₜ[R] u))) +
      Koszul.delta b s ((ι R (b j) * Koszul.basisWord b l) ⊗ₜ[R] p) ∈
      rectangle l.length n
    rw [diff_wedge, map_sub, map_neg, pbwTensor_wedge,
      delta_wedge b s j (hl j (by simp))]
    convert sub_mem (neg_mem haction) htail using 1
    simp only [map_add, pbwTensor_tmul]
    abel

/-- The actual conjugated differential on polynomial tensors. -/
def polynomialDiff : Module.End R EP :=
  (pbwTensor b).toLinearMap ∘ₗ diff R L U ∘ₗ (pbwTensor b).symm.toLinearMap

/-- The comparison for arbitrary bounded-degree polynomial coefficients. -/
theorem polynomialDiff_add_delta_basisWord (s : Finset I) (l : List I)
    (hl : ∀ i ∈ l, i ∈ s) (n : ℕ) (p : P)
    (hp : p ∈ MvPolynomial.restrictTotalDegree I R n) :
    polynomialDiff b (Koszul.basisWord b l ⊗ₜ[R] p) +
      Koszul.delta b s (Koszul.basisWord b l ⊗ₜ[R] p) ∈ rectangle (l.length - 1) n := by
  let u := (LeftRegular.equiv R L).symm ((UniversalEnvelopingAlgebra.pbwEquiv b).symm p)
  have he : UniversalEnvelopingAlgebra.pbwEquiv b (LeftRegular.equiv R L u) = p := by
    simp [u]
  have hu : LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n :=
    (UniversalEnvelopingAlgebra.mem_filtration_iff_pbwEquiv b).mpr (he ▸ hp)
  have ht : pbwTensor b (Koszul.basisWord b l ⊗ₜ[R] u) =
      Koszul.basisWord b l ⊗ₜ[R] p := by rw [pbwTensor_tmul, he]
  have h := diff_add_delta_basisWord b s l hl n u hu
  rw [← ht]
  simpa only [polynomialDiff, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using h

/-- Bounded-degree tensors supported in a finite set in the exterior factor.
Polynomial support is unrestricted, and `I` need not be finite. -/
def supportedTensors (s : Finset I) (q n : ℕ) : Submodule R EP :=
  Submodule.span R {z | ∃ (l : List I) (p : P), l.length = q ∧
    (∀ i ∈ l, i ∈ s) ∧ p ∈ MvPolynomial.restrictTotalDegree I R n ∧
      z = Koszul.basisWord b l ⊗ₜ[R] p}

/-- Chain-level PBW/Koszul comparison on the entire supported bounded-degree span.
The actual CE differential transported by PBW differs from **negative** Koszul by exterior
degree `q-1`, polynomial degree at most `n`, hence total degree at most `q+n-1` for `q>0`.
Reconstructed by linear extension of the proved CE recursion comparison; no acyclicity or
comparison hypothesis is assumed. -/
theorem polynomialDiff_add_delta_mem (s : Finset I) (q n : ℕ) (z : EP)
    (hz : z ∈ supportedTensors b s q n) :
    polynomialDiff b z + Koszul.delta b s z ∈ rectangle (q - 1) n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, p, hq, hl, hp, rfl⟩ := hz
    simpa only [hq] using polynomialDiff_add_delta_basisWord b s l hl n p hp
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add, add_add_add_comm] using add_mem hx hy
  | smul r z _ hz =>
    simpa only [map_smul, smul_add] using Submodule.smul_mem (rectangle (q - 1) n) r hz


end LieModule.ChevalleyEilenberg.CELeading
