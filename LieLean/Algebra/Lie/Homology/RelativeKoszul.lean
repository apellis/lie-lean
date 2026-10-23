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
    show p ∘ₗ V.subtype = LinearMap.id from LinearMap.ext hp, ExteriorAlgebra.map_id,
    AlgHom.id_apply]

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
    simpa only [hq] using relDiff_add_delta_basisWord (hp := hp) (b := b) (Ψ := Ψ)
      (hlead := hlead) (s := s) (l := l) hl n hr
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

/-! ### Weights in coordinates -/

variable (wt : J → Dual K H)

/-- The weight `Σ wt(lᵢ)` of a word `l`. -/
def wordWt (l : List J) : Dual K H := (l.map wt).sum

/-- The weight `Σ mⱼ wt(j)` of a monomial `x^m`. -/
def monoWt (m : J →₀ ℕ) : Dual K H := m.sum fun j k ↦ k • wt j

@[simp] lemma wordWt_nil : wordWt wt [] = 0 := rfl

@[simp] lemma wordWt_cons (j : J) (l : List J) : wordWt wt (j :: l) = wt j + wordWt wt l := by
  simp [wordWt]

lemma monoWt_single_add (i : J) (m : J →₀ ℕ) :
    monoWt wt (Finsupp.single i 1 + m) = wt i + monoWt wt m := by
  rw [monoWt, Finsupp.sum_add_index' (h := fun j (k : ℕ) ↦ k • wt j) (fun _ ↦ zero_smul ℕ _)
    (fun _ _ _ ↦ add_smul _ _ _),
    Finsupp.sum_single_index (h := fun j (k : ℕ) ↦ k • wt j) (zero_smul ℕ _), one_smul,
    monoWt]

/-- The span of the basis words of weight `μ`. -/
def wordSpan (μ : Dual K H) : Submodule K (ExteriorAlgebra K V) :=
  Submodule.span K {e | ∃ l, wordWt wt l = μ ∧ e = basisWord b l}

lemma basisWord_mem_wordSpan (l : List J) : basisWord b l ∈ wordSpan b wt (wordWt wt l) :=
  Submodule.subset_span ⟨l, rfl, rfl⟩

lemma ι_mul_mem_wordSpan (j : J) {μ : Dual K H} {e : ExteriorAlgebra K V}
    (he : e ∈ wordSpan b wt μ) : ι K (b j) * e ∈ wordSpan b wt (wt j + μ) := by
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨l, rfl, rfl⟩ := he
    have : ι K (b j) * basisWord b l = basisWord b (j :: l) := by simp [basisWord]
    rw [this, ← wordWt_cons]
    exact basisWord_mem_wordSpan b wt _
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

lemma contract_basisWord_mem (i : J) (l : List J) :
    Koszul.contract b i (basisWord b l) ∈ wordSpan b wt (wordWt wt l - wt i) := by
  classical
  induction l with
  | nil => simp [basisWord, Koszul.contract, CliffordAlgebra.contractLeft_one]
  | cons j l ih =>
    have hw : basisWord b (j :: l) = Koszul.wedge b j (basisWord b l) := by simp [basisWord]
    rw [hw, Koszul.contract_wedge]
    refine sub_mem ?_ ?_
    · by_cases hij : i = j
      · subst hij
        refine Submodule.smul_mem _ _ ?_
        simpa using basisWord_mem_wordSpan b wt l
      · simp [Basis.coord_apply, Basis.repr_self, Ne.symm hij]
    · have := ι_mul_mem_wordSpan b wt j ih
      rw [wordWt_cons, add_sub_assoc]
      simpa using this

lemma contract_basisWord_eq_zero {i : J} {l : List J} (hi : i ∉ l) :
    Koszul.contract b i (basisWord b l) = 0 := by
  classical
  induction l with
  | nil => simp [basisWord, Koszul.contract, CliffordAlgebra.contractLeft_one]
  | cons j l ih =>
    have hw : basisWord b (j :: l) = Koszul.wedge b j (basisWord b l) := by simp [basisWord]
    have hij : i ≠ j := fun h ↦ hi (h ▸ List.mem_cons_self)
    rw [hw, Koszul.contract_wedge, ih (fun h ↦ hi (List.mem_cons_of_mem j h))]
    simp [Basis.coord_apply, Basis.repr_self, Ne.symm hij]

/-- The basis words span the exterior algebra. -/
lemma span_basisWord : Submodule.span K (Set.range (basisWord b)) = ⊤ := by
  refine eq_top_iff.mpr fun e _ ↦ ?_
  clear ‹e ∈ ⊤›
  induction e using exterior_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], by simp [basisWord]⟩)
  | add e e' h h' => exact add_mem h h'
  | ι_mul y e h =>
    have hy : y ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      induction h using Submodule.span_induction with
      | mem e he =>
        obtain ⟨l, rfl⟩ := he
        exact Submodule.subset_span ⟨j :: l, by simp [basisWord]⟩
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
      | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/-- Weight coordinates: the basis vectors `b j` are weight vectors of weight `wt j` for `ρ.D`,
and the monomial `x^m` corresponds to a weight vector of weight `c + Σ mⱼ wt(j)`. -/
structure IsWeightCoord (ρ : DerivAction K H L X) (Ψ : X ≃ₗ[K] P) (c : Dual K H) : Prop where
  basis : ∀ a j, ρ.D a (b j : L) = wt j a • (b j : L)
  monomial : ∀ a m, ρ.φ a (Ψ.symm (MvPolynomial.monomial m 1)) =
    (c + monoWt wt m) a • Ψ.symm (MvPolynomial.monomial m 1)

variable (ρ) in
/-- The coordinate tensors of weight `ν`. -/
def coordWt (ν : Dual K H) : Submodule K EP :=
  (Module.End.weightSpaceOf ρ.θ ν).comap (ofCoord Ψ)

variable {Ψ b wt} {c : Dual K H}

omit [LieModule K L X] in
lemma extDeriv_map_basisWord (hw : IsWeightCoord b wt ρ Ψ c) (a : H) (l : List J) :
    extDeriv (ρ.D a) (ExteriorAlgebra.map V.subtype (basisWord b l)) =
      wordWt wt l a • ExteriorAlgebra.map V.subtype (basisWord b l) := by
  induction l with
  | nil => simp [basisWord]
  | cons j l ih =>
    have e : ExteriorAlgebra.map V.subtype (basisWord b (j :: l)) =
        ι K (b j : L) * ExteriorAlgebra.map V.subtype (basisWord b l) := by
      simp [basisWord, map_mul, ExteriorAlgebra.map_apply_ι]
    rw [e, extDeriv_ι_mul, ih, hw.basis, map_smul, smul_mul_assoc, mul_smul_comm, ← add_smul,
      wordWt_cons, LinearMap.add_apply]

omit [LieModule K L X] in
lemma extDeriv_map_mem (hw : IsWeightCoord b wt ρ Ψ c) (a : H) {μ : Dual K H}
    {e : ExteriorAlgebra K V} (he : e ∈ wordSpan b wt μ) :
    extDeriv (ρ.D a) (ExteriorAlgebra.map V.subtype e) = μ a • ExteriorAlgebra.map V.subtype e := by
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨l, rfl, rfl⟩ := he
    exact extDeriv_map_basisWord hw a l
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, map_smul, hx, smul_comm]

omit [LieModule K L X] in
lemma tmul_mem_coordWt (hw : IsWeightCoord b wt ρ Ψ c) {μ : Dual K H}
    {e : ExteriorAlgebra K V} (he : e ∈ wordSpan b wt μ) (m : J →₀ ℕ) (r : K) :
    e ⊗ₜ MvPolynomial.monomial m r ∈ coordWt Ψ ρ (μ + c + monoWt wt m) := by
  intro a
  have hm : MvPolynomial.monomial m r = r • MvPolynomial.monomial m (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [ofCoord_tmul, ρ.θ_tmul, extDeriv_map_mem hw a he, hm, map_smul, map_smul, hw.monomial,
    smul_comm r, tmul_smul, tmul_smul, ← smul_tmul', tmul_smul, smul_smul, smul_smul, ← add_smul,
    add_assoc, LinearMap.add_apply, LinearMap.add_apply, mul_comm]
  rw [smul_smul]
  congr 1
  simp only [LinearMap.add_apply]
  ring

omit [LieModule K L X] in
lemma delta_mem_coordWt (hw : IsWeightCoord b wt ρ Ψ c) (s : Finset J) (l : List J)
    (m : J →₀ ℕ) (r : K) :
    Koszul.delta b s (basisWord b l ⊗ₜ MvPolynomial.monomial m r) ∈
      coordWt Ψ ρ (wordWt wt l + c + monoWt wt m) := by
  simp only [Koszul.delta, LinearMap.sum_apply, Koszul.deltaTerm_tmul]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
  convert tmul_mem_coordWt hw (contract_basisWord_mem b wt i l) _ r using 2
  rw [monoWt_single_add]
  abel

include hp in
omit [LieModule K L X] in
lemma prZero_of_mem {z : EP} (hz : z ∈ coordWt Ψ ρ 0) : prZero p Ψ hT z = z := by
  rw [prZero, LinearMap.comp_apply, LinearMap.comp_apply, Module.End.weightProj_of_mem hT hz,
    toCoord_ofCoord (hp := hp)]

omit [LieModule K L X] in
lemma prZero_of_mem_ne {ν : Dual K H} (hν : ν ≠ 0) {z : EP} (hz : z ∈ coordWt Ψ ρ ν) :
    prZero p Ψ hT z = 0 := by
  rw [prZero, LinearMap.comp_apply, LinearMap.comp_apply,
    Module.End.weightProj_of_mem_ne hT hν hz, map_zero]

include hp in
omit [LieModule K L X] in
/-- The weight-`0` projection commutes with the Koszul differential. -/
lemma prZero_delta (hw : IsWeightCoord b wt ρ Ψ c) (s : Finset J) (z : EP) :
    prZero p Ψ hT (Koszul.delta b s z) = Koszul.delta b s (prZero p Ψ hT z) := by
  induction z with
  | add z z' h h' => simp only [map_add, h, h']
  | tmul e q =>
    have he : e ∈ Submodule.span K (Set.range (basisWord b)) :=
      (span_basisWord b).symm ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨l, rfl⟩ := he
      induction q using MvPolynomial.induction_on' with
      | monomial m r =>
        have hg := tmul_mem_coordWt hw (basisWord_mem_wordSpan b wt l) m r
        have hd := delta_mem_coordWt hw s l m r
        by_cases hν : wordWt wt l + c + monoWt wt m = 0
        · rw [hν] at hg hd
          rw [prZero_of_mem hp hT hd, prZero_of_mem hp hT hg]
        · rw [prZero_of_mem_ne hT hν hd, prZero_of_mem_ne hT hν hg, map_zero]
      | add q q' h h' => simp only [tmul_add, map_add, h, h']
    | zero => simp only [zero_tmul, map_zero]
    | add e e' _ _ h h' => simp only [add_tmul, map_add, h, h']
    | smul r e _ h => simp only [← smul_tmul', map_smul, h]

omit [LieRingModule L X] [LieModule K L X] in
lemma supportedTensors_le_rectangle (s : Finset J) (q n : ℕ) :
    supportedTensors b s q n ≤ rectangle q n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨l, r, hl, -, hr, rfl⟩
  exact tmul_mem_rectangle (hl ▸ Koszul.basisWord_mem_exteriorPower b l) hr

include hp in
omit [LieModule K L X] in
lemma prZero_mem_supportedTensors (hw : IsWeightCoord b wt ρ Ψ c) {s : Finset J} {q n : ℕ}
    {z : EP} (hz : z ∈ supportedTensors b s q n) :
    prZero p Ψ hT z ∈ supportedTensors b s q n := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, r, hl, hs, hr, rfl⟩ := hz
    rw [MvPolynomial.as_sum r, tmul_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm ↦ ?_
    have hmem : basisWord b l ⊗ₜ MvPolynomial.monomial m (r.coeff m) ∈
        supportedTensors b s q n :=
      Submodule.subset_span ⟨l, _, hl, hs,
        (MvPolynomial.monomial_mem_restrictSupport K).mpr (Or.inl (hr hm)), rfl⟩
    have hg := tmul_mem_coordWt hw (basisWord_mem_wordSpan b wt l) m (r.coeff m)
    by_cases hν : wordWt wt l + c + monoWt wt m = 0
    · rw [hν] at hg
      rwa [prZero_of_mem hp hT hg]
    · rw [prZero_of_mem_ne hT hν hg]
      exact zero_mem _
  | zero => simp only [map_zero, zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

include hp in
omit [LieModule K L X] in
lemma prZero_mem_rectangle (hw : IsWeightCoord b wt ρ Ψ c) {q n : ℕ} {z : EP}
    (hz : z ∈ rectangle q n) : prZero p Ψ hT z ∈ rectangle q n := by
  obtain ⟨s, hs⟩ := Koszul.exists_support_rectangle b q n hz
  exact supportedTensors_le_rectangle s q n (prZero_mem_supportedTensors hp hT hw hs)

omit [LieRingModule L X] [LieModule K L X] in
lemma delta_univ_eq [Fintype J] {s : Finset J} {q n : ℕ} {z : EP}
    (hz : z ∈ supportedTensors b s q n) : Koszul.delta b Finset.univ z = Koszul.delta b s z := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, r, -, hs, -, rfl⟩ := hz
    simp only [Koszul.delta, LinearMap.sum_apply]
    symm
    refine Finset.sum_subset (Finset.subset_univ s) fun i _ hi ↦ ?_
    rw [Koszul.deltaTerm_tmul, contract_basisWord_eq_zero b fun h ↦ hi (hs i h), zero_tmul]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r x _ hx => rw [map_smul, map_smul, hx]

/-! ### Exactness -/

omit [LieRingModule L X] [LieModule K L X] in
lemma map_mem_exteriorPower {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) {q : ℕ} {ω : ExteriorAlgebra K M} (hω : ω ∈ ⋀[K]^q M) :
    ExteriorAlgebra.map f ω ∈ ⋀[K]^q N := by
  have h : (⋀[K]^q M).map (ExteriorAlgebra.map f).toLinearMap ≤ ⋀[K]^q N := by
    rw [exteriorPower, Submodule.map_pow]
    refine pow_le_pow_left' ?_ q
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨f y, by simp⟩
  exact h ⟨ω, hω, rfl⟩

omit [LieRingModule L X] [LieModule K L X] in
lemma toCoord_mem_rectangle {q : ℕ} {t : EX} (ht : t ∈ chainsIn K L X q) :
    ∃ n, toCoord p Ψ t ∈ rectangle q n := by
  obtain ⟨t, rfl⟩ := ht
  induction t with
  | tmul ω x =>
    refine ⟨(Ψ x).totalDegree, ?_⟩
    rw [incl_tmul, toCoord_tmul]
    exact tmul_mem_rectangle (map_mem_exteriorPower p ω.2)
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl)
  | add t t' h h' =>
    obtain ⟨n, hn⟩ := h
    obtain ⟨n', hn'⟩ := h'
    refine ⟨max n n', ?_⟩
    rw [map_add, map_add]
    exact add_mem (Koszul.rectangle_mono q (le_max_left _ _) hn)
      (Koszul.rectangle_mono q (le_max_right _ _) hn')

omit [LieRingModule L X] [LieModule K L X] in
lemma ofCoord_mem_chainsIn {q n : ℕ} {z : EP} (hz : z ∈ rectangle q n) :
    ofCoord Ψ z ∈ chainsIn K L X q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, r, -, rfl⟩ := hz
    rw [ofCoord_tmul]
    exact tmul_mem_chainsIn (map_mem_exteriorPower _ he) _
  | zero => simp only [map_zero, zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

variable [Fintype J]

variable (p Ψ b) in
/-- The relative differential on weight `0`, extended by minus the Koszul differential on the
other weights. -/
def relKoszulOp : Module.End K EP :=
  relDiff p Ψ ∘ₗ prZero p Ψ hT - Koszul.delta b Finset.univ ∘ₗ (LinearMap.id - prZero p Ψ hT)

lemma relKoszulOp_apply (z : EP) : relKoszulOp p Ψ b hT z =
    relDiff p Ψ (prZero p Ψ hT z) - Koszul.delta b Finset.univ (z - prZero p Ψ hT z) := rfl

include hp in
lemma prZero_relKoszulOp (hr : IsRelData η ρ p) (hw : IsWeightCoord b wt ρ Ψ c) (z : EP) :
    prZero p Ψ hT (relKoszulOp p Ψ b hT z) = relDiff p Ψ (prZero p Ψ hT z) := by
  rw [relKoszulOp_apply, map_sub, prZero_relDiff_prZero Ψ hp hT hr, prZero_delta hp hT hw,
    map_sub, prZero_prZero Ψ hp hT hr, sub_self, map_zero, sub_zero]

include hp in
lemma relKoszulOp_relKoszulOp (hr : IsRelData η ρ p) (hw : IsWeightCoord b wt ρ Ψ c) (z : EP) :
    relKoszulOp p Ψ b hT (relKoszulOp p Ψ b hT z) = 0 := by
  have h := prZero_relKoszulOp hp hT hr hw z
  rw [relKoszulOp_apply (z := relKoszulOp p Ψ b hT z), h, relDiff_relDiff_prZero Ψ hT hr,
    relKoszulOp_apply (z := z), sub_sub_cancel_left, map_neg,
    ← Module.End.mul_apply, Koszul.delta_sq, LinearMap.zero_apply, neg_zero, sub_zero]

include hp in
lemma isLeadingKoszul_relKoszulOp (hlead : IsLeading Ψ b) (hw : IsWeightCoord b wt ρ Ψ c) :
    Koszul.IsLeadingKoszul b (relKoszulOp p Ψ b hT) := by
  intro s q n z hz
  have h1 := prZero_mem_supportedTensors hp hT hw hz
  rw [relKoszulOp_apply, map_sub, delta_univ_eq hz, delta_univ_eq h1]
  convert relDiff_add_delta_mem hp hlead s q n h1 using 1
  abel

omit [Fintype J] in
include hp hT in
/-- **Exactness of relative chains.** Under the weight and leading-term hypotheses, every chain
`t` of weight `0` and positive degree whose differential lies in `⨆ₐ η(a) ∧ C` is a boundary
modulo `⨆ₐ η(a) ∧ C`. This is the hypothesis of
`LieModule.ChevalleyEilenberg.DerivAction.exists_δ_eq_of_relExact`. -/
theorem relExact [CharZero K] [Finite J] (hlead : IsLeading Ψ b) (hr : IsRelData η ρ p)
    (hw : IsWeightCoord b wt ρ Ψ c) {k : ℕ} (t : EX) (ht : t ∈ ρ.chainPiece (k + 1) 0)
    (hdt : diff K L X t ∈ wedgeRange K L X η) :
    ∃ s ∈ ρ.chainPiece (k + 2) 0, t - diff K L X s ∈ wedgeRange K L X η := by
  have := Fintype.ofFinite J
  obtain ⟨n, hz⟩ := toCoord_mem_rectangle (p := p) (Ψ := Ψ) ht.1
  have hPt : Pr hT t = t := Module.End.weightProj_of_mem hT ht.2
  have hprz : prZero p Ψ hT (toCoord p Ψ t) = toCoord p Ψ t := by
    rw [prZero_toCoord Ψ hp hT hr, hPt]
  have hrel : relDiff p Ψ (toCoord p Ψ t) = 0 := by
    have := relDiff_toCoord_Pr Ψ hT hr t
    rw [hPt] at this
    rw [this]
    exact toCoord_eq_zero_of_mem Ψ hr hdt
  have hDz : relKoszulOp p Ψ b hT (toCoord p Ψ t) = 0 := by
    rw [relKoszulOp_apply, hprz, hrel, sub_self, map_zero, sub_zero]
  obtain ⟨y, hy, hDy⟩ := Koszul.exists_primitive_of_isLeadingKoszul b
    (isLeadingKoszul_relKoszulOp hp hT hlead hw) (relKoszulOp_relKoszulOp hp hT hr hw) (k + 1) n
    (Nat.succ_pos k) hz hDz
  have hy0 : relDiff p Ψ (prZero p Ψ hT y) = toCoord p Ψ t := by
    have := congrArg (prZero p Ψ hT) hDy
    rwa [prZero_relKoszulOp hp hT hr hw, hprz] at this
  refine ⟨ofCoord Ψ (prZero p Ψ hT y),
    ⟨ofCoord_mem_chainsIn (Ψ := Ψ) (prZero_mem_rectangle hp hT hw hy), ?_⟩, ?_⟩
  · rw [ofCoord_prZero Ψ hp hT hr]
    exact Module.End.weightProj_mem hT 0 _
  · refine mem_of_toCoord_eq_zero Ψ hr ?_
    rw [map_sub, ← hy0, relDiff, LinearMap.comp_apply, LinearMap.comp_apply, sub_self]

end Relative

end LieModule.ChevalleyEilenberg.RelativeKoszul
