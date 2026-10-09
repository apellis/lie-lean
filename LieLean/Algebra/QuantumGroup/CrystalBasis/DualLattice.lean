/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lattices over a subring of a field: bounds, duals, stabilization

Let `A` be a commutative ring with an algebra structure on a field `k`, `ϖ ∈ A`, and `V` a
`k`-vector space. For `A`-submodules `Λ ⊆ V` (lattices) we record:

* if every element of `k` is `ϖ^{-m} a` (`a ∈ A`), every vector in the `k`-span of `Λ` lies in
  some `ϖ^{-m} Λ` (`QuantumGroup.DualLattice.exists_pow_smul_mem`);
* the dual lattice `Λ^∨ = {x | B(x, Λ) ⊆ A}` of a bilinear form (`QuantumGroup.DualLattice.dual`),
  `(span_A b)^∨ = span_A b^*` for a `k`-basis `b` and its `B`-dual basis, hence `Λ^∨∨ = Λ` for
  symmetric nondegenerate `B` (`QuantumGroup.DualLattice.dual_dual_span`);
* stability of duals under perturbation: if `Λ^∨ ⊆ ϖ^{-e} Λ` for `B` and `B' ≡ B` modulo `ϖ^m`
  on `Λ × Λ` with `m > e`, then `Λ^∨` is the same for `B` and `B'`
  (`QuantumGroup.DualLattice.dual_eq_of_sub`);
* over a discrete valuation ring, a decreasing sequence of lattices squeezed between `L₀` and a
  finitely generated lattice containing `L₀` up to a power of `ϖ` stabilizes
  (`QuantumGroup.DualLattice.exists_stable`).

These are used in Kashiwara's grand-loop argument.
-/

open Pointwise

namespace LieLean.QuantumGroup

namespace DualLattice

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra A k] (ϖ : A)
  {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower A k V]

/-! ### Bounds -/

section Bound

variable {ϖ} (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hk

/-- Every vector of the `k`-span of `Λ` lies in some `ϖ^{-m} Λ`. -/
theorem exists_pow_smul_mem {Λ : Submodule A V} {x : V}
    (hx : x ∈ Submodule.span k (Λ : Set V)) : ∃ m : ℕ, ϖ ^ m • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m₁, h₁⟩ := ha
    obtain ⟨m₂, h₂⟩ := hb
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add, pow_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h₁
    · rw [mul_smul]; exact Submodule.smul_mem _ _ h₂
  | smul c a _ ha =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨m', b, hb⟩ := hk c
    refine ⟨m' + m, ?_⟩
    have : ϖ ^ (m' + m) • c • a = b • (ϖ ^ m • a) := by
      rw [← algebraMap_smul k (ϖ ^ (m' + m)), ← algebraMap_smul k b, ← algebraMap_smul k (ϖ ^ m),
        smul_smul, smul_smul, ← hb, pow_add, map_mul]
      ring_nf
    rw [this]
    exact Submodule.smul_mem _ _ hm

/-- A finitely generated `A`-submodule of the `k`-span of `Λ` lies in some `ϖ^{-m} Λ`. -/
theorem exists_pow_smul_le {Λ N : Submodule A V} (hN : N.FG)
    (hNs : ∀ x ∈ N, x ∈ Submodule.span k (Λ : Set V)) : ∃ m : ℕ, ∀ x ∈ N, ϖ ^ m • x ∈ Λ := by
  classical
  obtain ⟨s, rfl⟩ := hN
  choose m hm using fun x : s ↦ exists_pow_smul_mem hk (hNs x (Submodule.subset_span x.2))
  refine ⟨s.attach.sup m, fun x hx ↦ ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have hle : m ⟨x, hx⟩ ≤ s.attach.sup m := Finset.le_sup (f := m) (by simp)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hm ⟨x, hx⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha

end Bound

/-! ### Dual lattices -/

/-- The dual lattice `Λ^∨ = {x | B(x, Λ) ⊆ A}`. -/
def dual (B : LinearMap.BilinForm k V) (Λ : Submodule A V) : Submodule A V where
  carrier := {x | ∀ y ∈ Λ, B x y ∈ (algebraMap A k).range}
  add_mem' {x x'} hx hx' y hy := by
    obtain ⟨a, ha⟩ := hx y hy
    obtain ⟨a', ha'⟩ := hx' y hy
    exact ⟨a + a', by rw [map_add, ha, ha', map_add, LinearMap.add_apply]⟩
  zero_mem' y _ := ⟨0, by simp⟩
  smul_mem' c x hx y hy := by
    obtain ⟨a, ha⟩ := hx y hy
    refine ⟨c * a, ?_⟩
    rw [← algebraMap_smul k c x, map_smul, LinearMap.smul_apply, ← ha, smul_eq_mul, map_mul]

variable {ϖ}

lemma mem_dual {B : LinearMap.BilinForm k V} {Λ : Submodule A V} {x : V} :
    x ∈ dual B Λ ↔ ∀ y ∈ Λ, B x y ∈ (algebraMap A k).range := Iff.rfl

/-- `(span_A b)^∨ = span_A b^*` for a `k`-basis `b` and its `B`-dual basis. -/
theorem dual_span_basis {ι : Type*} [DecidableEq ι] [Finite ι] {B : LinearMap.BilinForm k V}
    (hB : B.Nondegenerate) (b : Module.Basis ι k V) :
    dual B (Submodule.span A (Set.range b)) = Submodule.span A (Set.range (B.dualBasis hB b)) := by
  have := Fintype.ofFinite ι
  ext x
  constructor
  · intro hx
    choose a ha using fun j ↦ hx (b j) (Submodule.subset_span ⟨j, rfl⟩)
    have hx' : x = ∑ j, a j • B.dualBasis hB b j := by
      conv_lhs => rw [← (B.dualBasis hB b).sum_repr x]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, ← ha, algebraMap_smul]
    rw [hx']
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [LinearMap.BilinForm.apply_dualBasis_left]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩
      | zero => exact ⟨0, by simp⟩
      | add y y' _ _ hy hy' =>
        obtain ⟨a, ha⟩ := hy; obtain ⟨a', ha'⟩ := hy'
        exact ⟨a + a', by rw [map_add, map_add, ha, ha']⟩
      | smul c y _ hy =>
        obtain ⟨a, ha⟩ := hy
        exact ⟨c * a, by rw [← algebraMap_smul k c y, map_smul, ← ha, smul_eq_mul, map_mul]⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha => exact Submodule.smul_mem _ c ha

/-- `(span_A b)^∨∨ = span_A b` for a symmetric nondegenerate form ([HK] Lemma 5.3.13). -/
theorem dual_dual_span {ι : Type*} [Finite ι] {B : LinearMap.BilinForm k V}
    (hB : B.Nondegenerate) (hs : B.IsSymm) (b : Module.Basis ι k V) :
    dual B (dual B (Submodule.span A (Set.range b))) = Submodule.span A (Set.range b) := by
  classical
  rw [dual_span_basis hB b, dual_span_basis hB (B.dualBasis hB b)]
  congr 2
  ext j
  apply (B.dualBasis hB (B.dualBasis hB b)).repr.injective
  ext i
  rw [Module.Basis.repr_self, LinearMap.BilinForm.dualBasis_repr_apply, hs.eq,
    LinearMap.BilinForm.apply_dualBasis_left, Finsupp.single_apply]


lemma dual_antitone {B : LinearMap.BilinForm k V} {Λ Λ' : Submodule A V} (h : Λ ≤ Λ') :
    dual B Λ' ≤ dual B Λ := fun _ hx y hy ↦ hx y (h hy)

lemma apply_smul_left_A (B : LinearMap.BilinForm k V) (a : A) (x y : V) :
    B (a • x) y = algebraMap A k a * B x y := by
  rw [← algebraMap_smul k a x, map_smul, LinearMap.smul_apply, smul_eq_mul]

lemma apply_smul_right_A (B : LinearMap.BilinForm k V) (a : A) (x y : V) :
    B x (a • y) = algebraMap A k a * B x y := by
  rw [← algebraMap_smul k a y, map_smul, smul_eq_mul]

section Bounds

variable (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
include hk

/-- For a nondegenerate form and a finitely generated `A`-lattice `M` spanning `V`,
`M^∨ ⊆ ϖ^{-e} M` for some `e`. -/
theorem exists_pow_smul_mem_of_mem_dual {B : LinearMap.BilinForm k V} (hB : B.Nondegenerate)
    {M : Submodule A V} (hM : M.FG) (hspan : Submodule.span k (M : Set V) = ⊤) :
    ∃ e : ℕ, ∀ x ∈ dual B M, ϖ ^ e • x ∈ M := by
  classical
  obtain ⟨s, rfl⟩ := hM
  rw [Submodule.span_span_of_tower] at hspan
  obtain ⟨t, hts, hspan_t, hli⟩ := exists_linearIndependent k (s : Set V)
  have htfin : t.Finite := (s.finite_toSet).subset hts
  have : Finite t := htfin.to_subtype
  let b : Module.Basis t k V := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan_t, hspan])
  have hb : Set.range b = t := by
    simp [b, Module.Basis.coe_mk]
  have hmem : ∀ j : t, ∃ m : ℕ, ϖ ^ m • B.dualBasis hB b j ∈ Submodule.span A (s : Set V) :=
    fun j ↦ exists_pow_smul_mem hk (by rw [Submodule.span_span_of_tower, hspan]; trivial)
  choose m hm using hmem
  have := Fintype.ofFinite t
  refine ⟨Finset.univ.sup m, fun x hx ↦ ?_⟩
  have hx' : x ∈ dual B (Submodule.span A (Set.range b)) :=
    dual_antitone (Submodule.span_mono (by rw [hb]; exact hts)) hx
  rw [dual_span_basis hB b] at hx'
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) (Finset.mem_univ j))
    rw [hd, add_comm, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hm j)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

/-- If `ϖ^c Λ ⊆ M` with `M` finitely generated, every vector lies in some `ϖ^{-n} Λ^∨`. -/
theorem exists_pow_smul_mem_dual (B : LinearMap.BilinForm k V) {M : Submodule A V} (hM : M.FG)
    {Λ : Submodule A V} {c : ℕ} (hΛ : ∀ y ∈ Λ, ϖ ^ c • y ∈ M) (x : V) :
    ∃ n : ℕ, ϖ ^ n • x ∈ dual B Λ := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have hg : ∀ g : s, ∃ n : ℕ, B (ϖ ^ n • x) g ∈ (algebraMap A k).range := fun g ↦ by
    obtain ⟨n, a, ha⟩ := hk (B x g)
    exact ⟨n, a, by rw [apply_smul_left_A, ha]⟩
  choose n hn using hg
  refine ⟨Finset.univ.sup n + c, fun y hy ↦ ?_⟩
  have key : ∀ z ∈ Submodule.span A (s : Set V),
      B (ϖ ^ Finset.univ.sup n • x) z ∈ (algebraMap A k).range := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
        (Finset.le_sup (f := n) (Finset.mem_univ (⟨z, hz⟩ : s)))
      obtain ⟨a, ha⟩ := hn ⟨z, hz⟩
      refine ⟨ϖ ^ d * a, ?_⟩
      rw [hd, add_comm, pow_add, mul_smul, apply_smul_left_A, map_mul, ha]
    | zero => exact ⟨0, by simp⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨a, ha⟩ := hz
      obtain ⟨a', ha'⟩ := hz'
      exact ⟨a + a', by rw [map_add, map_add, ha, ha']⟩
    | smul c z _ hz =>
      obtain ⟨a, ha⟩ := hz
      exact ⟨c * a, by rw [apply_smul_right_A, map_mul, ha]⟩
  obtain ⟨a, ha⟩ := key _ (hΛ y hy)
  refine ⟨a, ?_⟩
  rw [ha, apply_smul_right_A, pow_add, mul_smul, apply_smul_left_A, apply_smul_left_A,
    apply_smul_left_A]
  ring

omit hk in
/-- A finitely generated torsion-free lattice over a PID `A ⊆ k`. -/
lemma isTorsionFree_of_injective [IsDomain A] (hinj : Function.Injective (algebraMap A k))
    (M : Submodule A V) : Module.IsTorsionFree A M := ⟨fun r hr m₁ m₂ h ↦ by
  have hr0 : algebraMap A k r ≠ 0 := fun h0 ↦ hr.ne_zero (hinj (by rw [h0, map_zero]))
  refine Subtype.ext (smul_right_injective V hr0 ?_)
  simpa [algebraMap_smul] using congrArg Subtype.val h⟩

/-- Over a principal ideal domain `A ⊆ k` with `k = A[ϖ⁻¹]`, a finitely generated `A`-lattice
spanning `V` is the `A`-span of a `k`-basis. -/
theorem exists_basis_span_eq [IsDomain A] [IsPrincipalIdealRing A]
    (hinj : Function.Injective (algebraMap A k)) (hϖ0 : algebraMap A k ϖ ≠ 0)
    {M : Submodule A V} (hM : M.FG) (hspan : Submodule.span k (M : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), Submodule.span A (Set.range b) = M := by
  classical
  have : Module.Finite A M := Module.Finite.iff_fg.2 hM
  have := isTorsionFree_of_injective hinj M
  obtain ⟨n, bA⟩ := Module.basisOfFiniteTypeTorsionFree' (R := A) (M := M)
  let b : Fin n → V := fun j ↦ (bA j : V)
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range bA := by
      ext x; simp [b]
    rw [this, ← Submodule.map_span, bA.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent k b := by
    rw [linearIndependent_iff']
    intro s g hg j hj
    choose m a ha using fun j ↦ hk (g j)
    set N := Finset.univ.sup m
    have hga : ∀ j, algebraMap A k (ϖ ^ N) * g j = algebraMap A k (ϖ ^ (N - m j) * a j) := by
      intro j
      have hle : m j ≤ N := Finset.le_sup (f := m) (Finset.mem_univ j)
      rw [map_mul, ← ha, ← mul_assoc, ← map_mul, ← pow_add, Nat.sub_add_cancel hle]
    have hzero : ∑ i ∈ s, (ϖ ^ (N - m i) * a i) • bA i = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_zero]
      have : ∑ i ∈ s, (ϖ ^ (N - m i) * a i) • b i =
          algebraMap A k (ϖ ^ N) • ∑ i ∈ s, g i • b i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← algebraMap_smul k, ← hga, smul_smul]
      rw [this, hg, smul_zero]
    have h0 := linearIndependent_iff'.1 bA.linearIndependent s _ hzero j hj
    have := hga j
    rw [h0, map_zero] at this
    exact (mul_eq_zero.1 this).resolve_left (by rw [map_pow]; exact pow_ne_zero _ hϖ0)
  have hsp : ⊤ ≤ Submodule.span k (Set.range b) := by
    rw [← hspan, ← hspanA, Submodule.span_span_of_tower]
  exact ⟨n, Module.Basis.mk hli hsp, by rw [Module.Basis.coe_mk, hspanA]⟩

/-- **`M^∨∨ = M`** for a finitely generated full lattice over a principal ideal domain and a
symmetric nondegenerate form ([HK] Lemma 5.3.13). -/
theorem dual_dual_of_fg [IsDomain A] [IsPrincipalIdealRing A]
    (hinj : Function.Injective (algebraMap A k)) (hϖ0 : algebraMap A k ϖ ≠ 0)
    {B : LinearMap.BilinForm k V} (hB : B.Nondegenerate) (hs : B.IsSymm) {M : Submodule A V}
    (hM : M.FG) (hspan : Submodule.span k (M : Set V) = ⊤) : dual B (dual B M) = M := by
  obtain ⟨n, b, hb⟩ := exists_basis_span_eq hk hinj hϖ0 hM hspan
  rw [← hb, dual_dual_span hB hs b]

end Bounds

/-! ### Perturbation -/

/-- If `Λ^∨ ⊆ ϖ^{-e} Λ` for `B` (and every vector lies in some `ϖ^{-n} Λ^∨`), and `B' ≡ B` modulo
`ϖ^m` on `Λ × Λ` with `m > e`, then `B` and `B'` have the same dual lattice. -/
theorem dual_eq_of_sub (hϖ0 : algebraMap A k ϖ ≠ 0) {B B' : LinearMap.BilinForm k V}
    {Λ : Submodule A V} {e m : ℕ} (hem : e + 1 ≤ m)
    (hbound : ∀ x ∈ dual B Λ, ϖ ^ e • x ∈ Λ) (hfin : ∀ x : V, ∃ n : ℕ, ϖ ^ n • x ∈ dual B Λ)
    (hsub : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ a : A, B x y - B' x y = algebraMap A k (ϖ ^ m * a)) :
    dual B' Λ = dual B Λ := by
  have hpow : ∀ n : ℕ, algebraMap A k (ϖ ^ n) ≠ 0 := fun n ↦ by
    rw [map_pow]; exact pow_ne_zero _ hϖ0
  -- the difference on `ϖ^{-s} Λ × Λ`
  have hdiff : ∀ (s : ℕ) (x : V), ϖ ^ s • x ∈ Λ → s ≤ m → ∀ y ∈ Λ,
      ∃ a : A, B x y - B' x y = algebraMap A k (ϖ ^ (m - s) * a) := by
    intro s x hx hsm y hy
    obtain ⟨a, ha⟩ := hsub _ hx y hy
    refine ⟨a, mul_left_cancel₀ (hpow s) ?_⟩
    rw [← algebraMap_smul k, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, ← mul_sub] at ha
    rw [ha, ← map_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hsm]
  ext x
  constructor
  · intro hx
    classical
    obtain ⟨n, hn⟩ := hfin x
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      refine ih ?_
      intro y hy
      have h1 : B' (ϖ ^ n • x) y ∈ (algebraMap A k).range := by
        obtain ⟨a, ha⟩ := hx y hy
        exact ⟨ϖ ^ n * a, by rw [← algebraMap_smul k, map_smul, LinearMap.smul_apply, ← ha,
          smul_eq_mul, map_mul]⟩
      have hb := hbound _ hn
      rw [smul_smul, ← pow_add] at hb
      have hb' : ϖ ^ (e + 1) • ϖ ^ n • x ∈ Λ := by
        rw [smul_smul, ← pow_add, show e + 1 + n = e + (n + 1) by omega]; exact hb
      obtain ⟨a, ha⟩ := hdiff (e + 1) (ϖ ^ n • x) hb' hem y hy
      obtain ⟨c, hc⟩ := h1
      exact ⟨c + ϖ ^ (m - (e + 1)) * a, by
        rw [map_add, hc, ← ha]; ring⟩
  · intro hx y hy
    obtain ⟨a, ha⟩ := hdiff e x (hbound x hx) (by omega) y hy
    obtain ⟨c, hc⟩ := hx y hy
    exact ⟨c - ϖ ^ (m - e) * a, by rw [map_sub, hc, ← ha]; ring⟩

/-! ### Stabilization over a discrete valuation ring -/

section Stable

variable [IsDomain A] [IsDiscreteValuationRing A]

lemma isArtinian_quotient_pow (n : ℕ) (hϖ : ϖ ≠ 0) :
    IsArtinian A (A ⧸ Ideal.span {ϖ ^ n}) :=
  ((isFiniteLength_iff_isNoetherian_isArtinian).1 (isFiniteLength_quotient_span_singleton A
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hϖ)))).2

/-- A finitely generated `A`-module killed by `ϖⁿ` is Artinian. -/
lemma isArtinian_of_fg_of_pow_smul {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] (hϖ : ϖ ≠ 0) {n : ℕ} (hn : ∀ x : M, ϖ ^ n • x = 0) : IsArtinian A M := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  have := isArtinian_quotient_pow (ϖ := ϖ) n hϖ
  have hle : ∀ x : M, Ideal.span {ϖ ^ n} ≤ LinearMap.ker (LinearMap.toSpanSingleton A M x) := by
    intro x
    rw [Ideal.span_le]
    rintro _ rfl
    simp [hn x]
  let φ : s → (A ⧸ Ideal.span {ϖ ^ n}) →ₗ[A] M := fun x ↦
    (Ideal.span {ϖ ^ n}).liftQ (LinearMap.toSpanSingleton A M x) (hle x)
  let f : (s → A ⧸ Ideal.span {ϖ ^ n}) →ₗ[A] M :=
    { toFun := fun c ↦ ∑ x, φ x (c x)
      map_add' := fun c c' ↦ by simp [Finset.sum_add_distrib]
      map_smul' := fun a c ↦ by simp [Finset.smul_sum] }
  refine isArtinian_of_surjective _ f ?_
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  refine ⟨Pi.single ⟨x, hx⟩ (Submodule.Quotient.mk 1), ?_⟩
  change ∑ y, φ y (Pi.single (M := fun _ ↦ A ⧸ Ideal.span {ϖ ^ n}) ⟨x, hx⟩
    (Submodule.Quotient.mk 1) y) = x
  rw [Finset.sum_eq_single ⟨x, hx⟩ (fun b _ hb ↦ by simp [hb]) (by simp), Pi.single_eq_same]
  change (Submodule.liftQ _ _ _) (Submodule.Quotient.mk 1) = x
  rw [Submodule.liftQ_apply]
  simp

/-- A decreasing sequence of `A`-submodules `s n`, all containing `L₀`, with `s 0` finitely
generated and `ϖᴺ s 0 ⊆ L₀`, stabilizes. -/
theorem exists_stable (hϖ : ϖ ≠ 0) (s : ℕ → Submodule A V) (hs : Antitone s) {L₀ : Submodule A V}
    (hL₀ : ∀ n, L₀ ≤ s n) (hfg : (s 0).FG) {N : ℕ} (hN : ∀ x ∈ s 0, ϖ ^ N • x ∈ L₀) :
    ∃ n, ∀ m, n ≤ m → s m = s n := by
  set P := L₀.comap (s 0).subtype
  have hfin : Module.Finite A (s 0) := Module.Finite.iff_fg.2 hfg
  have hart : IsArtinian A ((s 0) ⧸ P) := isArtinian_of_fg_of_pow_smul hϖ (n := N)
    (fun x ↦ by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hN x.1 x.2)
  let t : ℕ →o (Submodule A ((s 0) ⧸ P))ᵒᵈ :=
    ⟨fun n ↦ ((s n).comap (s 0).subtype).map P.mkQ, fun a b hab ↦
      Submodule.map_mono (Submodule.comap_mono (hs hab))⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes t
  refine ⟨n, fun m hm ↦ ?_⟩
  have h := hn m hm
  have key : ∀ j, (s j).comap (s 0).subtype = (t j).comap P.mkQ := by
    intro j
    change _ = (((s j).comap (s 0).subtype).map P.mkQ).comap P.mkQ
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono (hL₀ j))]
  have h' : (s m).comap (s 0).subtype = (s n).comap (s 0).subtype := by
    rw [key, key, ← h]
  apply le_antisymm (hs hm)
  intro x hx
  have hx0 : x ∈ s 0 := hs (Nat.zero_le n) hx
  have := (Submodule.ext_iff.1 h' ⟨x, hx0⟩).2 hx
  exact this

end Stable

end DualLattice

end LieLean.QuantumGroup
