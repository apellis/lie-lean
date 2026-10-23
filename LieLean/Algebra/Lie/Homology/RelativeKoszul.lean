/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.RelativeDuality
import LieLean.LinearAlgebra.ExteriorAlgebra.KoszulDescent

/-!
# Exactness of relative chains by Koszul descent

Let `L` be a Lie algebra over a field `K` of characteristic zero, `η : H → L` a linear map onto an
abelian subalgebra acting diagonalizably, and `V ⊆ L` a complement of `η(H)` stable under
`ad η(H)`, with projection `p : L → V`. The relative chains of an `L`-module `X` are the chains of
weight `0` modulo `⨆ₐ η(a) ∧ C`; they are identified with `(⋀V ⊗ X)_0` by `⋀p ⊗ 1`.

Suppose `V` has a basis `b` of weight vectors and `X` has polynomial coordinates
`Ψ : X ≃ K[x_j]` in which the monomials are weight vectors and `b j` acts by multiplication by
`x_j` up to terms of lower degree. Then the relative differential, written in these coordinates,
has leading term minus the Koszul differential, and Koszul descent shows that the relative chain
complex is exact in positive degrees
(`LieModule.ChevalleyEilenberg.RelativeKoszul.relExact`, in the form required by
`LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_relExact`).

## Main definitions

* `LieModule.ChevalleyEilenberg.RelativeKoszul.toCoord`, `ofCoord`: the maps `⋀p ⊗ Ψ` and
  `⋀(V ↪ L) ⊗ Ψ⁻¹` between `⋀L ⊗ X` and `⋀V ⊗ K[x_j]`.
* `LieModule.ChevalleyEilenberg.RelativeKoszul.relDiff`: the differential in coordinates.

## Main results

* `LieModule.ChevalleyEilenberg.RelativeKoszul.relDiff_add_delta_mem`: the leading term of the
  relative differential is minus the Koszul differential.
* `LieModule.ChevalleyEilenberg.RelativeKoszul.relExact`: positive-degree exactness of the
  relative chains.

## References

This is the acyclicity input of Humphreys, *Representations of semisimple Lie algebras in the BGG
category 𝒪*, GSM 94, Thm. 6.15 (a); the argument is our own.
-/

open Module TensorProduct ExteriorAlgebra
open ExteriorAlgebra.Koszul (rectangle supportedTensors tmul_mem_rectangle basisWord)

noncomputable section

namespace LieModule.ChevalleyEilenberg.RelativeKoszul

variable {K L X J : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup X] [Module K X] [LieRingModule L X] [LieModule K L X]
  {V : Submodule K L} (p : L →ₗ[K] V) (Ψ : X ≃ₗ[K] MvPolynomial J K)

local notation "P" => MvPolynomial J K
local notation "EP" => ExteriorAlgebra K V ⊗[K] P
local notation "EX" => ExteriorAlgebra K L ⊗[K] X

/-! ### Coordinates -/

/-- The coordinate map `⋀p ⊗ Ψ : ⋀L ⊗ X → ⋀V ⊗ K[x_j]`. -/
def toCoord : EX →ₗ[K] EP :=
  TensorProduct.map (ExteriorAlgebra.map p).toLinearMap Ψ.toLinearMap

/-- The map `⋀(V ↪ L) ⊗ Ψ⁻¹ : ⋀V ⊗ K[x_j] → ⋀L ⊗ X`. -/
def ofCoord : EP →ₗ[K] EX :=
  TensorProduct.map (ExteriorAlgebra.map V.subtype).toLinearMap Ψ.symm.toLinearMap

/-- The Chevalley–Eilenberg differential in coordinates. -/
def relDiff : Module.End K EP := toCoord p Ψ ∘ₗ diff K L X ∘ₗ ofCoord Ψ

/-- Exterior multiplication by `x ∈ V` on `⋀V ⊗ K[x_j]`. -/
def wedgeV (x : V) : Module.End K EP :=
  TensorProduct.map (LinearMap.mulLeft K (ι K x)) LinearMap.id

omit [LieRingModule L X] [LieModule K L X] in
@[simp] lemma toCoord_tmul (ω : ExteriorAlgebra K L) (x : X) :
    toCoord p Ψ (ω ⊗ₜ x) = ExteriorAlgebra.map p ω ⊗ₜ Ψ x := rfl

omit [LieRingModule L X] [LieModule K L X] in
@[simp] lemma ofCoord_tmul (e : ExteriorAlgebra K V) (q : P) :
    ofCoord Ψ (e ⊗ₜ q) = ExteriorAlgebra.map V.subtype e ⊗ₜ Ψ.symm q := rfl

omit [LieRingModule L X] [LieModule K L X] in
@[simp] lemma wedgeV_tmul (x : V) (e : ExteriorAlgebra K V) (q : P) :
    wedgeV (J := J) x (e ⊗ₜ q) = (ι K x * e) ⊗ₜ q := rfl

variable {p} (hp : ∀ x : V, p x = x)
include hp in
omit [LieRingModule L X] [LieModule K L X] in
lemma map_map_subtype (e : ExteriorAlgebra K V) :
    ExteriorAlgebra.map p (ExteriorAlgebra.map V.subtype e) = e := by
  rw [← AlgHom.comp_apply, map_comp_map,
    show p ∘ₗ V.subtype = LinearMap.id from LinearMap.ext hp, ExteriorAlgebra.map_id, AlgHom.id_apply]

include hp in
omit [LieRingModule L X] [LieModule K L X] in
@[simp] lemma toCoord_ofCoord (z : EP) : toCoord p Ψ (ofCoord Ψ z) = z := by
  induction z with
  | tmul e q => simp [map_map_subtype hp]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

variable (p) in
omit [LieRingModule L X] [LieModule K L X] in
lemma toCoord_wedge (y : L) (c : EX) :
    toCoord p Ψ (wedge K L X y c) = wedgeV (p y) (toCoord p Ψ c) := by
  induction c with
  | tmul ω x => simp [map_mul, map_apply_ι]
  | add c c' hc hc' => simp only [map_add, hc, hc']

omit [LieRingModule L X] [LieModule K L X] in
lemma ofCoord_wedgeV (x : V) (z : EP) :
    ofCoord Ψ (wedgeV x z) = wedge K L X (x : L) (ofCoord Ψ z) := by
  induction z with
  | tmul e q => simp [map_mul, map_apply_ι]
  | add z z' hz hz' => simp only [map_add, hz, hz']

omit [LieRingModule L X] [LieModule K L X] in
lemma wedgeV_mem (x : V) {q n : ℕ} {z : EP} (hz : z ∈ rectangle q n) :
    wedgeV x z ∈ rectangle (q + 1) n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, r, hr, rfl⟩ := hz
    rw [wedgeV_tmul]
    apply tmul_mem_rectangle _ hr
    rw [exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ x) he
  | zero => simpa only [map_zero] using (rectangle (q + 1) n).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r z _ hz => rw [map_smul]; exact Submodule.smul_mem _ r hz

variable (b : Basis J K V)

omit [LieRingModule L X] [LieModule K L X] in
lemma basisWord_cons_tmul (j : J) (l : List J) (q : P) :
    basisWord b (j :: l) ⊗ₜ[K] q = wedgeV (b j) (basisWord b l ⊗ₜ[K] q) := by
  simp [basisWord]

omit [LieRingModule L X] [LieModule K L X] in
/-- The Koszul differential satisfies the contraction recursion. -/
lemma delta_wedgeV (s : Finset J) (j : J) (hj : j ∈ s) (e : ExteriorAlgebra K V) (q : P) :
    Koszul.delta b s ((ι K (b j) * e) ⊗ₜ[K] q) =
      e ⊗ₜ[K] (MvPolynomial.X j * q) - wedgeV (b j) (Koszul.delta b s (e ⊗ₜ[K] q)) := by
  classical
  change Koszul.delta b s (Koszul.wedge b j e ⊗ₜ[K] q) = _
  simp only [Koszul.delta, LinearMap.sum_apply, Koszul.deltaTerm_tmul, Koszul.contract_wedge,
    sub_tmul, Finset.sum_sub_distrib, map_sum, wedgeV_tmul]
  simp only [Koszul.wedge_apply]
  congr 1
  simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, TensorProduct.ite_tmul, hj]

/-! ### The leading term -/

include hp in
/-- The adjoint part of the action of `y` does not raise the coefficient degree. -/
lemma lieAction_error (y : L) (l : List J) (n : ℕ) {q : P}
    (hq : q ∈ MvPolynomial.restrictTotalDegree J K n) :
    toCoord p Ψ (lieAction K L X y (ofCoord Ψ (basisWord b l ⊗ₜ q))) -
      basisWord b l ⊗ₜ[K] Ψ ⁅y, Ψ.symm q⁆ ∈ rectangle l.length n := by
  induction l with
  | nil => simp [basisWord]
  | cons i l ih =>
    rw [basisWord_cons_tmul, basisWord_cons_tmul, ofCoord_wedgeV, lieAction_wedge, map_add,
      toCoord_wedge, toCoord_wedge, toCoord_ofCoord (hp := hp), hp, add_sub_assoc, ← map_sub]
    exact add_mem (wedgeV_mem _ (tmul_mem_rectangle
      (Koszul.basisWord_mem_exteriorPower b l) hq)) (wedgeV_mem _ ih)

/-- Leading-term hypothesis: `b j` acts as `x_j` modulo lower degree. -/
def IsLeading : Prop := ∀ (j : J) (n : ℕ) (q : P), q ∈ MvPolynomial.restrictTotalDegree J K n →
  Ψ ⁅(b j : L), Ψ.symm q⁆ - MvPolynomial.X j * q ∈ MvPolynomial.restrictTotalDegree J K n

variable {Ψ b} (hlead : IsLeading Ψ b)
include hp hlead

/-- On a basis word, the relative differential is minus the Koszul differential modulo
coefficient degree `n`. -/
theorem relDiff_add_delta_basisWord (s : Finset J) (l : List J) (hl : ∀ i ∈ l, i ∈ s)
    (n : ℕ) {q : P} (hq : q ∈ MvPolynomial.restrictTotalDegree J K n) :
    relDiff p Ψ (basisWord b l ⊗ₜ q) + Koszul.delta b s (basisWord b l ⊗ₜ q) ∈
      rectangle (l.length - 1) n := by
  induction l with
  | nil =>
    simp [relDiff, basisWord, Koszul.delta, Koszul.deltaTerm_tmul, Koszul.contract]
  | cons j l ih =>
    have haction : toCoord p Ψ (lieAction K L X (b j) (ofCoord Ψ (basisWord b l ⊗ₜ q))) -
        basisWord b l ⊗ₜ[K] (MvPolynomial.X j * q) ∈ rectangle l.length n := by
      have h1 := lieAction_error (X := X) (hp := hp) (Ψ := Ψ) (b := b) (b j) l n hq
      have h2 : basisWord b l ⊗ₜ[K] Ψ ⁅(b j : L), Ψ.symm q⁆ -
          basisWord b l ⊗ₜ[K] (MvPolynomial.X j * q) ∈ rectangle l.length n := by
        rw [← TensorProduct.tmul_sub]
        exact tmul_mem_rectangle (Koszul.basisWord_mem_exteriorPower b l) (hlead j n q hq)
      convert add_mem h1 h2 using 1
      abel
    have htail : wedgeV (b j) (relDiff p Ψ (basisWord b l ⊗ₜ q) +
        Koszul.delta b s (basisWord b l ⊗ₜ q)) ∈ rectangle l.length n := by
      cases l with
      | nil => simp [relDiff, basisWord, Koszul.delta, Koszul.deltaTerm_tmul, Koszul.contract]
      | cons i l => exact wedgeV_mem _ (ih fun i hi ↦ hl i (List.mem_cons_of_mem j hi))
    have hw : basisWord b (j :: l) = ι K (b j) * basisWord b l := by simp [basisWord]
    rw [hw, delta_wedgeV b s j (hl j (by simp)), ← wedgeV_tmul, relDiff, LinearMap.comp_apply,
      LinearMap.comp_apply, ofCoord_wedgeV, diff_wedge, map_sub, map_neg, toCoord_wedge, hp]
    simp only [List.length_cons, Nat.add_sub_cancel]
    convert sub_mem (neg_mem haction) htail using 1
    simp only [relDiff, LinearMap.comp_apply, map_add]
    abel

/-- The relative differential in coordinates has leading term minus the Koszul differential. -/
theorem relDiff_add_delta_mem (s : Finset J) (q n : ℕ) {z : EP}
    (hz : z ∈ supportedTensors b s q n) :
    relDiff p Ψ z + Koszul.delta b s z ∈ rectangle (q - 1) n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, r, hq, hl, hr, rfl⟩ := hz
    simpa only [hq] using relDiff_add_delta_basisWord (hp := hp) (b := b) (Ψ := Ψ) (hlead := hlead) (s := s) (l := l) hl n hr
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add, add_add_add_comm] using add_mem hx hy
  | smul r z _ hz =>
    simpa only [map_smul, smul_add] using Submodule.smul_mem (rectangle (q - 1) n) r hz

end LieModule.ChevalleyEilenberg.RelativeKoszul
