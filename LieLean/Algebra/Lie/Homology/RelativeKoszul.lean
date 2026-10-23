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

section Leading

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

end Leading

/-! ### Relative chains -/

section Relative

variable {H : Type*} [AddCommGroup H] [Module K H] (η : H →ₗ[K] L) (ρ : DerivAction K H L X)

/-- The data of the relative setting: `ρ` is the action of `η(H)`, which is abelian, and
`p : L → V` is a projection along `η(H)` commuting with `ad η(H)`. -/
structure IsRelData (p : L →ₗ[K] V) : Prop where
  D_eq : ∀ a, ρ.D a = LieAlgebra.ad K L (η a)
  φ_eq : ∀ a (x : X), ρ.φ a x = ⁅η a, x⁆
  lie_eta : ∀ a a', ⁅η a, η a'⁆ = 0
  map_eta : ∀ a, p (η a) = 0
  sub_mem : ∀ y, ∃ a, y - (p y : L) = η a
  map_ad : ∀ a y, (p ⁅η a, y⁆ : L) = ⁅η a, (p y : L)⁆

variable {η ρ}

omit [LieRingModule L X] [LieModule K L X] in
lemma wedgeV_zero (z : EP) : wedgeV 0 z = 0 := by
  induction z with
  | tmul e q => simp
  | add z z' h h' => rw [map_add, h, h', add_zero]

omit [LieModule K L X] in
lemma toCoord_eq_zero_of_mem (hr : IsRelData η ρ p) {w : EX}
    (hw : w ∈ wedgeRange K L X η) : toCoord p Ψ w = 0 := by
  induction hw using Submodule.iSup_induction' with
  | mem a w hw =>
    obtain ⟨c, rfl⟩ := hw
    rw [toCoord_wedge, hr.map_eta, wedgeV_zero]
  | zero => exact map_zero _
  | add w w' _ _ h h' => rw [map_add, h, h', add_zero]

omit [LieRingModule L X] [LieModule K L X] in
lemma wedge_mem_wedgeRange_of_mem (y : L) {w : EX} (hw : w ∈ wedgeRange K L X η) :
    wedge K L X y w ∈ wedgeRange K L X η := by
  induction hw using Submodule.iSup_induction' with
  | mem a w hw =>
    obtain ⟨c, rfl⟩ := hw
    have e : wedge K L X y (wedge K L X (η a) c) = wedge K L X (η a) (-wedge K L X y c) := by
      induction c with
      | tmul ω x =>
        rw [map_neg, wedge_tmul, wedge_tmul, wedge_tmul, wedge_tmul, ← neg_tmul, ← mul_assoc,
          ← mul_assoc, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap y (η a)),
          neg_mul]
      | add c c' h h' => simp only [map_add, map_neg, h, h', neg_add]
    rw [e]
    exact wedge_mem_wedgeRange η a _
  | zero => simpa only [map_zero] using (wedgeRange K L X η).zero_mem
  | add w w' _ _ h h' => rw [map_add]; exact add_mem h h'

omit [LieRingModule L X] [LieModule K L X] in
lemma ofCoord_toCoord_tmul (ω : ExteriorAlgebra K L) (x : X) :
    ofCoord Ψ (toCoord p Ψ (ω ⊗ₜ x)) = ExteriorAlgebra.map (V.subtype ∘ₗ p) ω ⊗ₜ x := by
  rw [toCoord_tmul, ofCoord_tmul, ← AlgHom.comp_apply, map_comp_map, LinearEquiv.symm_apply_apply]

omit [LieModule K L X] in
/-- `c` and `(⋀p ⊗ Ψ)⁻¹(⋀p ⊗ Ψ) c` agree modulo `⨆ₐ η(a) ∧ C`. -/
lemma sub_ofCoord_toCoord_mem (hr : IsRelData η ρ p) (c : EX) :
    c - ofCoord Ψ (toCoord p Ψ c) ∈ wedgeRange K L X η := by
  induction c with
  | tmul ω x =>
    rw [ofCoord_toCoord_tmul, ← sub_tmul]
    induction ω using exterior_induction with
    | algebraMap r => simp [AlgHom.commutes]
    | add ω ω' h h' =>
      rw [map_add, add_sub_add_comm, add_tmul]
      exact add_mem h h'
    | ι_mul y ω h =>
      obtain ⟨a, ha⟩ := hr.sub_mem y
      have e : (ι K y * ω - ExteriorAlgebra.map (V.subtype ∘ₗ p) (ι K y * ω)) ⊗ₜ[K] x =
          wedge K L X (η a) (ω ⊗ₜ x) + wedge K L X (p y : L)
            ((ω - ExteriorAlgebra.map (V.subtype ∘ₗ p) ω) ⊗ₜ x) := by
        rw [wedge_tmul, wedge_tmul, ← add_tmul, map_mul, ExteriorAlgebra.map_apply_ι, ← ha,
          map_sub, sub_mul, mul_sub]
        simp only [LinearMap.comp_apply, Submodule.subtype_apply]
        congr 1
        abel
      rw [e]
      exact add_mem (wedge_mem_wedgeRange η a _) (wedge_mem_wedgeRange_of_mem _ h)
  | add c c' h h' =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem h h'

omit [LieModule K L X] in
/-- The kernel of `⋀p ⊗ Ψ` is `⨆ₐ η(a) ∧ C`. -/
lemma mem_of_toCoord_eq_zero (hr : IsRelData η ρ p) {c : EX} (hc : toCoord p Ψ c = 0) :
    c ∈ wedgeRange K L X η := by
  simpa [hc] using sub_ofCoord_toCoord_mem (Ψ := Ψ) hr c

omit [LieRingModule L X] [LieModule K L X] in
/-- Naturality of the derivation extension. -/
lemma map_extDeriv {f D : L →ₗ[K] L} (h : ∀ y, f (D y) = D (f y)) (ω : ExteriorAlgebra K L) :
    ExteriorAlgebra.map f (extDeriv D ω) = extDeriv D (ExteriorAlgebra.map f ω) := by
  induction ω using exterior_induction with
  | algebraMap r => simp [AlgHom.commutes]
  | add ω ω' h h' => simp only [map_add, h, h']
  | ι_mul y ω ih =>
    rw [extDeriv_ι_mul, map_add, map_mul, map_mul, ExteriorAlgebra.map_apply_ι,
      ExteriorAlgebra.map_apply_ι, ih, map_mul, ExteriorAlgebra.map_apply_ι, extDeriv_ι_mul, h]

omit [LieModule K L X] in
lemma ofCoord_toCoord_θ (hr : IsRelData η ρ p) (a : H) (c : EX) :
    ofCoord Ψ (toCoord p Ψ (ρ.θ a c)) = ρ.θ a (ofCoord Ψ (toCoord p Ψ c)) := by
  induction c with
  | tmul ω x =>
    rw [ρ.θ_tmul, map_add, map_add, ofCoord_toCoord_tmul, ofCoord_toCoord_tmul,
      ofCoord_toCoord_tmul, ρ.θ_tmul, map_extDeriv]
    intro y
    simp [hr.D_eq, hr.map_ad]
  | add c c' h h' => simp only [map_add, h, h']

variable (hT : ⨆ μ, Module.End.weightSpaceOf ρ.θ μ = ⊤)

/-- The projection onto the chains of weight `0`. -/
abbrev Pr : Module.End K EX := Module.End.weightProj hT 0

omit [LieModule K L X] in
lemma Pr_ofCoord_toCoord (hr : IsRelData η ρ p) (c : EX) :
    Pr hT (ofCoord Ψ (toCoord p Ψ c)) = ofCoord Ψ (toCoord p Ψ (Pr hT c)) :=
  Module.End.weightProj_comm_of_mapsTo hT 0 (ofCoord Ψ ∘ₗ toCoord p Ψ)
    (fun ν c hc a ↦ by
      simp only [LinearMap.comp_apply]
      rw [← ofCoord_toCoord_θ (Ψ := Ψ) hr a c, hc a, map_smul, map_smul]) c

lemma Pr_diff (c : EX) : Pr hT (diff K L X c) = diff K L X (Pr hT c) :=
  Module.End.weightProj_comm_of_mapsTo hT 0 (diff K L X)
    (fun ν c hc a ↦ by rw [← ρ.diff_θ, hc a, map_smul]) c

omit [LieModule K L X] in
lemma Pr_wedge (hr : IsRelData η ρ p) (a : H) (c : EX) :
    Pr hT (wedge K L X (η a) c) = wedge K L X (η a) (Pr hT c) :=
  Module.End.weightProj_comm_of_mapsTo hT 0 _ (fun ν c hc b ↦ by
    rw [ρ.θ_wedge, hr.D_eq, LieAlgebra.ad_apply, hr.lie_eta, map_zero, LinearMap.zero_apply,
      zero_add, hc b, map_smul]) c

omit [LieModule K L X] in
lemma Pr_Pr (c : EX) : Pr hT (Pr hT c) = Pr hT c :=
  Module.End.weightProj_of_mem hT (Module.End.weightProj_mem hT 0 c)

omit [LieModule K L X] in
lemma θ_Pr (a : H) (c : EX) : ρ.θ a (Pr hT c) = 0 := by
  have h := Module.End.weightProj_mem hT 0 c a
  simpa using h

lemma lieAction_eq_θ (hr : IsRelData η ρ p) (a : H) : lieAction K L X (η a) = ρ.θ a := by
  have : ρ.φ a = toEnd K L X (η a) := LinearMap.ext (hr.φ_eq a)
  rw [ρ.θ_apply, hr.D_eq, this]
  rfl

/-- The differential maps the weight-`0` part of `⨆ₐ η(a) ∧ C` into `⨆ₐ η(a) ∧ C`. -/
lemma diff_Pr_mem (hr : IsRelData η ρ p) {w : EX} (hw : w ∈ wedgeRange K L X η) :
    diff K L X (Pr hT w) ∈ wedgeRange K L X η := by
  induction hw using Submodule.iSup_induction' with
  | mem a w hw =>
    obtain ⟨c, rfl⟩ := hw
    rw [Pr_wedge hT hr, diff_wedge, lieAction_eq_θ hr, θ_Pr, neg_zero, zero_sub]
    exact neg_mem (wedge_mem_wedgeRange η a _)
  | zero => simpa only [map_zero] using (wedgeRange K L X η).zero_mem
  | add w w' _ _ h h' => rw [map_add, map_add]; exact add_mem h h'

/-! ### The weight-`0` projection in coordinates -/

variable (p) in
/-- The projection onto weight `0`, in coordinates. -/
def prZero : Module.End K EP := toCoord p Ψ ∘ₗ Pr hT ∘ₗ ofCoord Ψ

include hp in
omit [LieModule K L X] in
lemma ofCoord_prZero (hr : IsRelData η ρ p) (z : EP) :
    ofCoord Ψ (prZero p Ψ hT z) = Pr hT (ofCoord Ψ z) := by
  rw [prZero, LinearMap.comp_apply, LinearMap.comp_apply, ← Pr_ofCoord_toCoord Ψ hT hr,
    toCoord_ofCoord (hp := hp)]

include hp in
omit [LieModule K L X] in
lemma prZero_toCoord (hr : IsRelData η ρ p) (c : EX) :
    prZero p Ψ hT (toCoord p Ψ c) = toCoord p Ψ (Pr hT c) := by
  rw [prZero, LinearMap.comp_apply, LinearMap.comp_apply, Pr_ofCoord_toCoord Ψ hT hr,
    toCoord_ofCoord (hp := hp)]

include hp in
omit [LieModule K L X] in
lemma prZero_prZero (hr : IsRelData η ρ p) (z : EP) :
    prZero p Ψ hT (prZero p Ψ hT z) = prZero p Ψ hT z := by
  change toCoord p Ψ (Pr hT (ofCoord Ψ (prZero p Ψ hT z))) = _
  rw [ofCoord_prZero Ψ hp hT hr, Pr_Pr]
  rfl

/-- On weight `0`, the relative differential in coordinates is the differential. -/
lemma relDiff_toCoord_Pr (hr : IsRelData η ρ p) (c : EX) :
    relDiff p Ψ (toCoord p Ψ (Pr hT c)) = toCoord p Ψ (diff K L X (Pr hT c)) := by
  set w := Pr hT c - ofCoord Ψ (toCoord p Ψ (Pr hT c))
  have hw : w ∈ wedgeRange K L X η := sub_ofCoord_toCoord_mem (Ψ := Ψ) hr _
  have hPw : Pr hT w = w := by
    simp only [w, map_sub, Pr_ofCoord_toCoord Ψ hT hr, Pr_Pr]
  have h0 : toCoord p Ψ (diff K L X w) = 0 := by
    rw [← hPw]
    exact toCoord_eq_zero_of_mem Ψ hr (diff_Pr_mem hT hr hw)
  have e : ofCoord Ψ (toCoord p Ψ (Pr hT c)) = Pr hT c - w := by simp only [w, sub_sub_cancel]
  rw [relDiff, LinearMap.comp_apply, LinearMap.comp_apply, e, map_sub, map_sub, h0, sub_zero]

lemma relDiff_prZero (hr : IsRelData η ρ p) (z : EP) :
    relDiff p Ψ (prZero p Ψ hT z) = toCoord p Ψ (diff K L X (Pr hT (ofCoord Ψ z))) :=
  relDiff_toCoord_Pr Ψ hT hr _

lemma relDiff_relDiff_prZero (hr : IsRelData η ρ p) (z : EP) :
    relDiff p Ψ (relDiff p Ψ (prZero p Ψ hT z)) = 0 := by
  have e : diff K L X (Pr hT (ofCoord Ψ z)) = Pr hT (diff K L X (Pr hT (ofCoord Ψ z))) := by
    rw [Pr_diff hT, Pr_Pr]
  rw [relDiff_prZero Ψ hT hr, e, relDiff_toCoord_Pr Ψ hT hr, ← e, diff_diff, map_zero]

include hp in
lemma prZero_relDiff_prZero (hr : IsRelData η ρ p) (z : EP) :
    prZero p Ψ hT (relDiff p Ψ (prZero p Ψ hT z)) = relDiff p Ψ (prZero p Ψ hT z) := by
  rw [relDiff_prZero Ψ hT hr, prZero_toCoord Ψ hp hT hr, Pr_diff hT, Pr_Pr]

end Relative

end LieModule.ChevalleyEilenberg.RelativeKoszul
