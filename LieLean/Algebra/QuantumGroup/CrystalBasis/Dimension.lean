/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module

/-!
# Weight multiplicities from crystal bases

Let `(L, B)` be a crystal base of an integrable `U`-module `M`, over a principal ideal domain `A`
with fraction field `k`, at a non-unit `c ∈ A`. For every weight `Λ` with `M^Λ` finite-dimensional,
the `A`-module `L_Λ = L ∩ M^Λ` is free of rank `dim M^Λ`, and `B` has exactly `dim M^Λ` elements of
weight `Λ` ([HK] Thm. 4.2.5).

## Main results

* `LieLean.QuantumGroup.IsCrystalLattice.finrank_latticeWeightSpace`: `rank_A L_Λ = dim_k M^Λ`.
* `LieLean.QuantumGroup.IsCrystalBase.card_weight`: `#B_Λ = dim_k M^Λ`.

## Proof

A basis of the free `A`-module `L` is a `k`-basis of `M` (`k` is the fraction field and `L` spans
`M`), so `L_Λ` lies in a finitely generated free submodule of `L` and is free of finite rank; its
basis is a `k`-basis of `M^Λ`. Lifts of the elements of `B_Λ` to `L_Λ` are linearly independent
over `A` (divide a relation by the generator of the ideal of its coefficients and reduce modulo
`c`), and their images span `L_Λ / c L_Λ ≅ (A/cA)^{rank L_Λ}`, since `L` is graded. Hong and
Kang instead use `A₀/qA₀ ⊗ L_λ ≅ L_λ / q L_λ`; the argument here is reconstructed.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.2.
-/

open Module Pointwise

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]
  [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1} {hM : IsIntegrable R v M}

variable {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M}

variable (R v) in
/-- The weight-`Λ` part `L_Λ = L ∩ M^Λ` of an `A`-submodule `L` of `M`. -/
def latticeWeightSpace (L : Submodule A M) (Λ : Y →+ ℤ) : Submodule A M :=
  L ⊓ (weightSpace R v M Λ).restrictScalars A

omit [NeZero v] in
lemma mem_latticeWeightSpace {Λ : Y →+ ℤ} {m : M} :
    m ∈ latticeWeightSpace R v L Λ ↔ m ∈ L ∧ m ∈ weightSpace R v M Λ :=
  Iff.rfl


/-! ### Lattices spanning `M` over the fraction field -/

section FractionRing

variable [IsDomain A] [IsFractionRing A k]

omit [NeZero v] in
/-- If `L` spans `M` over the fraction field `k`, every vector has a nonzero multiple in `L`. -/
lemma exists_smul_mem_of_span_eq_top (hL : Submodule.span k (L : Set M) = ⊤) (m : M) :
    ∃ a : A, a ≠ 0 ∧ a • m ∈ L := by
  have hm : m ∈ Submodule.span k (L : Set M) := hL ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem b hax
    · rw [mul_smul]
      exact L.smul_mem a hby
  | smul κ x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) κ
    refine ⟨s * a, mul_ne_zero (nonZeroDivisors.coe_ne_zero s) ha, ?_⟩
    have : ((s : A) * a) • (κ • x) = r • (a • x) := by
      rw [← hrs, ← algebraMap_smul k ((s : A) * a), ← algebraMap_smul k r,
        ← algebraMap_smul k a, smul_smul, smul_smul, map_mul, mul_comm (algebraMap A k s),
        mul_assoc, IsLocalization.mk'_spec', mul_comm]
    rw [this]
    exact L.smul_mem r hax

omit [NeZero v] [IsDomain A] in
/-- A basis of a free `A`-submodule spanning `M` over `k` is a `k`-basis of `M`. -/
lemma linearIndependent_basis {ι : Type*} (b : Basis ι A L) :
    LinearIndependent k fun j ↦ (b j : M) :=
  (LinearIndependent.iff_fractionRing A k).mp (b.linearIndependent.map' L.subtype L.ker_subtype)

omit [NeZero v] [IsDomain A] [IsFractionRing A k] in
lemma span_basis_eq_top (hL : Submodule.span k (L : Set M) = ⊤) {ι : Type*} (b : Basis ι A L) :
    Submodule.span k (Set.range fun j ↦ (b j : M)) = ⊤ := by
  refine eq_top_iff.mpr (hL ▸ Submodule.span_le.mpr fun m hm ↦ ?_)
  have h1 : (⟨m, hm⟩ : L) ∈ Submodule.span A (Set.range b) := b.mem_span _
  have h2 : m ∈ Submodule.span A (Set.range fun j ↦ (b j : M)) := by
    have := Submodule.mem_map_of_mem (f := L.subtype) h1
    rwa [Submodule.map_span, ← Set.range_comp] at this
  exact Submodule.span_le_restrictScalars A k _ h2

omit [NeZero v] [IsDomain A] in
/-- The coordinates of `y ∈ L` in the `k`-basis of `M` given by a basis of `L`. -/
lemma basis_repr_coe (hL : Submodule.span k (L : Set M) = ⊤) {ι : Type*} (b : Basis ι A L)
    (y : L) (j : ι) :
    (Basis.mk (linearIndependent_basis b) (span_basis_eq_top hL b).ge).repr y j =
      algebraMap A k (b.repr y j) := by
  set kb := Basis.mk (linearIndependent_basis b) (span_basis_eq_top hL b).ge
  have hy : (y : M) = kb.repr.symm (Finsupp.mapRange (algebraMap A k) (map_zero _) (b.repr y)) := by
    rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by simp)]
    conv_lhs => rw [← b.linearCombination_repr y]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Submodule.coe_smul, algebraMap_smul, Basis.mk_apply]
  rw [hy, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]

end FractionRing

/-! ### The weight parts of a crystal lattice -/

section PID

variable [IsDomain A] [IsFractionRing A k] [IsPrincipalIdealRing A]

namespace IsCrystalLattice

omit [IsDomain A] in
/-- `L_Λ` is finitely generated if `M^Λ` is finite-dimensional. -/
theorem fg_latticeWeightSpace (hL : IsCrystalLattice hv hM L) (Λ : Y →+ ℤ)
    [FiniteDimensional k (weightSpace R v M Λ)] : (latticeWeightSpace R v L Λ).FG := by
  classical
  have := hL.free
  set b := Module.Free.chooseBasis A L
  set kb := Basis.mk (linearIndependent_basis b) (span_basis_eq_top hL.span_eq_top b).ge
  set f := Module.finBasis k (weightSpace R v M Λ)
  set J₀ : Finset _ := Finset.univ.biUnion fun s ↦ (kb.repr (f s)).support
  set N := Submodule.span A ((fun j ↦ (b j : M)) '' (J₀ : Set _))
  have hN : N.FG := Submodule.fg_span (J₀.finite_toSet.image _)
  have hle : latticeWeightSpace R v L Λ ≤ N := by
    rintro y ⟨hyL, hyΛ⟩
    have hk : ∀ j ∉ J₀, kb.repr y j = 0 := by
      intro j hj
      have hy : y = ∑ s, f.repr ⟨y, hyΛ⟩ s • (f s : M) := by
        have := congrArg Subtype.val (f.sum_repr ⟨y, hyΛ⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      rw [hy, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun s _ ↦ ?_
      have : j ∉ (kb.repr (f s)).support := fun h ↦
        hj (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, h⟩)
      rw [map_smul, Finsupp.smul_apply, Finsupp.notMem_support_iff.mp this, smul_zero]
    have hA : ∀ j ∉ J₀, b.repr ⟨y, hyL⟩ j = 0 := fun j hj ↦ by
      have h := basis_repr_coe hL.span_eq_top b ⟨y, hyL⟩ j
      rw [show ((⟨y, hyL⟩ : L) : M) = y from rfl, hk j hj] at h
      exact IsFractionRing.injective A k (by rw [← h, map_zero])
    have hmem : (⟨y, hyL⟩ : L) ∈ Submodule.span A (b '' J₀) := by
      refine (Finsupp.mem_span_image_iff_linearCombination A).mpr
        ⟨b.repr ⟨y, hyL⟩, (Finsupp.mem_supported A _).mpr fun j hj ↦ ?_,
          b.linearCombination_repr _⟩
      by_contra h
      exact (Finsupp.mem_support_iff.mp hj) (hA j h)
    have := Submodule.mem_map_of_mem (f := L.subtype) hmem
    rwa [Submodule.map_span, ← Set.image_comp] at this
  have : IsNoetherian A N := isNoetherian_of_fg_of_noetherian N hN
  have hfg := (IsNoetherian.noetherian ((latticeWeightSpace R v L Λ).comap N.subtype)).map
    N.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at hfg

omit [IsDomain A] in
theorem finite_latticeWeightSpace (hL : IsCrystalLattice hv hM L) (Λ : Y →+ ℤ)
    [FiniteDimensional k (weightSpace R v M Λ)] : Module.Finite A (latticeWeightSpace R v L Λ) :=
  Module.Finite.iff_fg.mpr (hL.fg_latticeWeightSpace Λ)

/-- `L_Λ` is a free `A`-module if `M^Λ` is finite-dimensional. -/
theorem free_latticeWeightSpace (hL : IsCrystalLattice hv hM L) (Λ : Y →+ ℤ)
    [FiniteDimensional k (weightSpace R v M Λ)] : Module.Free A (latticeWeightSpace R v L Λ) := by
  have := hL.finite_latticeWeightSpace Λ
  have : Module.IsTorsionFree A M := Module.IsTorsionFree.trans_faithfulSMul A k M
  infer_instance

/-- **[HK] Thm. 4.2.5**, first part: `rank_A L_Λ = dim_k M^Λ`. -/
theorem finrank_latticeWeightSpace (hL : IsCrystalLattice hv hM L) (Λ : Y →+ ℤ)
    [FiniteDimensional k (weightSpace R v M Λ)] :
    finrank A (latticeWeightSpace R v L Λ) = finrank k (weightSpace R v M Λ) := by
  classical
  have := hL.finite_latticeWeightSpace Λ
  have := hL.free_latticeWeightSpace Λ
  set Lw := latticeWeightSpace R v L Λ
  set β := Module.Free.chooseBasis A Lw
  let g : Module.Free.ChooseBasisIndex A Lw → weightSpace R v M Λ := fun s ↦ ⟨β s, (β s).2.2⟩
  have hli : LinearIndependent k g := by
    refine LinearIndependent.of_comp (weightSpace R v M Λ).subtype ?_
    exact (LinearIndependent.iff_fractionRing A k).mp
      (β.linearIndependent.map' Lw.subtype Lw.ker_subtype)
  have hsp : ⊤ ≤ Submodule.span k (Set.range g) := by
    rintro ⟨m, hm⟩ -
    obtain ⟨a, ha, ham⟩ := exists_smul_mem_of_span_eq_top hL.span_eq_top m
    have hamΛ : a • m ∈ Lw := ⟨ham, Submodule.smul_of_tower_mem _ a hm⟩
    have h1 : (⟨a • m, hamΛ⟩ : Lw) ∈ Submodule.span A (Set.range β) := β.mem_span _
    have h2 := Submodule.mem_map_of_mem
      (f := (Submodule.inclusion (fun x (hx : x ∈ Lw) ↦ hx.2) :
        Lw →ₗ[A] (weightSpace R v M Λ).restrictScalars A)) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    have h3 := Submodule.span_le_restrictScalars A k _ h2
    have h4 : (a : A) • (⟨m, hm⟩ : weightSpace R v M Λ) ∈ Submodule.span k (Set.range g) := h3
    rw [← algebraMap_smul k] at h4
    exact (Submodule.smul_mem_iff _ (by
      simpa using (IsFractionRing.injective A k).ne ha)).mp h4
  rw [finrank_eq_card_basis (Basis.mk hli hsp), Module.finrank_eq_card_chooseBasisIndex]

end IsCrystalLattice

namespace IsCrystalBase

variable {hL : IsCrystalLattice hv hM L} {c : A}
  {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}

/-- **[HK] Thm. 4.2.5**: for a crystal base `(L, B)` at a non-unit `c` and a weight `Λ` with
`M^Λ` finite-dimensional, `B` has exactly `dim_k M^Λ` elements of weight `Λ`. Hong and Kang work
with `A = A₀ ⊂ F(q)` and `c = q`; here `A` is any principal ideal domain with fraction field `k`.
-/
theorem card_weight (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (Λ : Y →+ ℤ)
    [FiniteDimensional k (weightSpace R v M Λ)] :
    Nat.card {b : B // hB.wt b = Λ} = finrank k (weightSpace R v M Λ) := by
  classical
  have := hL.finite_latticeWeightSpace Λ
  have := hL.free_latticeWeightSpace Λ
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have : Module.IsTorsionFree A M := Module.IsTorsionFree.trans_faithfulSMul A k M
  set Lw := latticeWeightSpace R v L Λ
  have hTF : Module.IsTorsionFree A Lw := inferInstance
  rw [← hL.finrank_latticeWeightSpace Λ]
  choose x hx hxb using fun b : B ↦ hB.exists_mk_eq b
  have hxw : ∀ b : {b : B // hB.wt b = Λ}, ((x b : L) : M) ∈ Lw := fun b ↦
    ⟨(x b).2, by have := hx b.1; rwa [b.2] at this⟩
  let y : {b : B // hB.wt b = Λ} → Lw := fun b ↦ ⟨x b, hxw b⟩
  -- the lifts are linearly independent over `A`
  have hli : LinearIndependent A y := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (Ideal.span (g '' ↑s))).principal
    have hgd : ∀ j ∈ s, g j ∈ Ideal.span {d} := fun j hj ↦ by
      rw [← Ideal.submodule_span_eq, ← hd]
      exact Ideal.subset_span (Set.mem_image_of_mem g hj)
    by_cases hd0 : d = 0
    · simpa [hd0] using hgd i hi
    exfalso
    choose! g' hg' using fun j hj ↦ Ideal.mem_span_singleton'.mp (hgd j hj)
    have h0 : ∑ j ∈ s, g' j • y j = 0 := by
      have : d • ∑ j ∈ s, g' j • y j = 0 := by
        rw [Finset.smul_sum, ← hg]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [smul_smul, mul_comm, hg' j hj]
      exact ((Module.isTorsionFree_iff_smul_eq_zero.mp hTF) d _ this).resolve_left hd0
    have h1 : ∑ j ∈ s, Ideal.Quotient.mk (Ideal.span {c}) (g' j) • ((j.1 : B) :
        L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) = 0 := by
      let ψ : Lw →ₗ[A] L ⧸ (Ideal.span {c} • ⊤ : Submodule A L) :=
        (Ideal.span {c} • ⊤ : Submodule A L).mkQ ∘ₗ Submodule.inclusion inf_le_left
      have := (map_sum ψ (fun j ↦ g' j • y j) s).symm.trans
        ((congrArg ψ h0).trans (map_zero ψ))
      rw [← this]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smul, ← hxb j.1]
      rfl
    have hc' := linearIndependent_iff'.mp
      (hB.linearIndependent.comp (fun j : {b : B // hB.wt b = Λ} ↦ j.1)
        Subtype.val_injective) s _ h1
    have hd' : d ∈ Ideal.span {c * d} := by
      have hle : Ideal.span (g '' ↑s) ≤ Ideal.span {c * d} := by
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨j, hj, rfl⟩
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp
          (Ideal.Quotient.eq_zero_iff_mem.mp (hc' j hj))
        rw [← hg' j hj, ← ht]
        exact Ideal.mem_span_singleton'.mpr ⟨t, by ring⟩
      refine hle ?_
      rw [hd]
      exact Submodule.mem_span_singleton_self d
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hd'
    have : t * c = 1 := by
      have h2 : (t * c - 1) * d = 0 := by linear_combination ht
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hd0)
    exact hc (IsUnit.of_mul_eq_one_right t this)
  have hcard := hli.cardinalMk_le_finrank
  have : Finite {b : B // hB.wt b = Λ} :=
    Cardinal.lt_aleph0_iff_finite.mp (hcard.trans_lt Cardinal.natCast_lt_aleph0)
  have : Fintype {b : B // hB.wt b = Λ} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  refine le_antisymm hli.fintype_card_le_finrank ?_
  -- the images of the lifts span `L_Λ / c L_Λ ≅ (A/cA)^r`
  set r := finrank A Lw
  let β := Module.finBasisOfFinrankEq A Lw rfl
  let q : A →ₗ[A] A ⧸ Ideal.span {c} := (Ideal.span {c}).mkQ
  let θ : Lw →ₗ[A] (Fin r → A ⧸ Ideal.span {c}) := LinearMap.pi fun s ↦ q ∘ₗ β.coord s
  have hθs : Function.Surjective θ := by
    intro t
    choose a ha using fun s ↦ Ideal.Quotient.mk_surjective (t s)
    refine ⟨β.equivFun.symm a, funext fun s ↦ ?_⟩
    simp only [θ, LinearMap.pi_apply, LinearMap.comp_apply, Basis.coord_apply, q]
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply, ← ha s]
    rfl
  have hθc : ∀ z : Lw, c • θ z = 0 := fun z ↦ by
    funext s
    simp only [θ, LinearMap.pi_apply, LinearMap.comp_apply, q, Submodule.mkQ_apply,
      Pi.smul_apply, Pi.zero_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩)
  have key : ∀ z : Lw, θ z ∈ Submodule.span A (Set.range (θ ∘ y)) := by
    intro z
    have hz : (Submodule.Quotient.mk (⟨z, z.2.1⟩ : L) :
        L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) ∈
        Submodule.span (A ⧸ Ideal.span {c}) B := hB.span_eq_top ▸ Submodule.mem_top
    obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hz
    choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (f i)
    have h1 : (z : M) - ∑ i, a i • ((x (g i) : L) : M) ∈ c • L := by
      have e : (Submodule.Quotient.mk (⟨z, z.2.1⟩ : L) :
          L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) =
          Submodule.Quotient.mk (∑ i, a i • x (g i)) := by
        rw [← hfg]
        have e' : ∀ i, f i • ((g i : B) : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) =
            (Ideal.span {c} • ⊤ : Submodule A L).mkQ (a i • x (g i)) := fun i ↦ by
          rw [← ha i, ← hxb (g i)]
          rfl
        rw [Finset.sum_congr rfl fun i _ ↦ e' i, ← map_sum]
        rfl
      have := (IntegrableSl2.mk_eq_mk_iff c _ _).mp e
      simpa [Submodule.coe_sum] using this
    have h2 := LinearMap.map_mem_smul_of_mem c (hL.weightSetProj_mem {Λ}) h1
    rw [map_sub, weightSetProj_singleton_of_mem hv hM z.2.2, map_sum] at h2
    simp only [LinearMap.map_smul_of_tower, weightSetProj_of_mem hv hM _ (hx _),
      Set.mem_singleton_iff] at h2
    obtain ⟨ℓ, hℓ, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h2
    set w := (z : M) - ∑ i, a i • (if hB.wt (g i) = Λ then ((x (g i) : L) : M) else 0)
    have hwΛ : w ∈ weightSpace R v M Λ := by
      refine sub_mem z.2.2 (Submodule.sum_mem _ fun i _ ↦ ?_)
      split_ifs with h
      · exact Submodule.smul_of_tower_mem _ _ (h ▸ hx (g i))
      · rw [smul_zero]
        exact zero_mem _
    let ℓ' : Lw := ⟨weightSetProj hv hM {Λ} ℓ, hL.weightSetProj_mem _ ℓ hℓ,
      weightSetProj_singleton_mem hv hM Λ ℓ⟩
    have hz : z = ∑ i, a i • (if h : hB.wt (g i) = Λ then y ⟨g i, h⟩ else 0) + c • ℓ' := by
      apply Subtype.ext
      have : w = c • weightSetProj hv hM {Λ} ℓ := by
        rw [← weightSetProj_singleton_of_mem hv hM hwΛ, ← hw, LinearMap.map_smul_of_tower]
      simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, ℓ', ← this, w]
      have hs : ∑ i, a i • (((if h : hB.wt (g i) = Λ then y ⟨g i, h⟩ else 0 : Lw)) : M) =
          ∑ i, a i • (if hB.wt (g i) = Λ then ((x (g i) : L) : M) else 0) :=
        Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp [y]
      rw [hs, add_sub_cancel]
    rw [hz, map_add, map_smul, hθc, add_zero, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    split_ifs with h
    · exact Submodule.subset_span ⟨⟨g i, h⟩, rfl⟩
    · rw [map_zero]
      exact zero_mem _
  have htop : Submodule.span (A ⧸ Ideal.span {c}) (Set.range (θ ∘ y)) = ⊤ := by
    refine eq_top_iff.mpr fun t _ ↦ ?_
    obtain ⟨z, rfl⟩ := hθs t
    exact Submodule.span_le_restrictScalars A _ _ (key z)
  have := finrank_range_le_card (R := A ⧸ Ideal.span {c}) (θ ∘ y)
  rwa [Set.finrank, htop, finrank_top, Module.finrank_fin_fun] at this

end IsCrystalBase

end PID

end LieLean.QuantumGroup
