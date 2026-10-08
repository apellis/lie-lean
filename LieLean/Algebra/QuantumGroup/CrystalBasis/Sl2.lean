/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase

/-!
# Crystal bases of integrable `U_q(𝔰𝔩₂)`-modules

For an integrable `U_q(𝔰𝔩₂)`-module `M` (`QuantumGroup.IntegrableSl2`), a commutative ring `A`
acting compatibly and `c ∈ A`, a *crystal base* (`QuantumGroup.IntegrableSl2.IsCrystalBase`) is a
free Kashiwara-stable `A`-submodule `L` spanning `M` with a basis `B` of the `A/cA`-module `L/cL`
of classes of weight vectors such that `ẽ B, f̃ B ⊆ B ∪ {0}` and `f̃ b = b' ↔ ẽ b' = b`
([HK] Def. 4.2.3 for `𝔤 = 𝔰𝔩₂`). A crystal base of an integrable `U`-module restricts to a crystal
base of every `nodeSl2` (`QuantumGroup.IsCrystalBase.isCrystalBase_nodeSl2`).

*String bases.* Let `ηₜ ∈ M^{pₜ}` (`t ∈ ι`) be primitive vectors such that for every `p` the
`ηₜ` with `pₜ = p` form a basis of the primitive vectors of weight `p`. Then the vectors
`F^{(j)} ηₜ` (`j ≤ pₜ`) form a basis of `M` (`IntegrableSl2.linearIndependent_dF`,
`IntegrableSl2.span_dF`), and if `A ⊆ k` (`FaithfulSMul A k`), their `A`-span `L` together with
their classes `B` in `L/cL` is a crystal base (`IntegrableSl2.isCrystalBase_stringLattice`):
the existence theorem for crystal bases of integrable `U_q(𝔰𝔩₂)`-modules ([HK] Ex. 4.2.6,
Thm. 4.3.1; there for finite-dimensional modules, here for all integrable ones).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §§4.2–4.3.
-/

open Finset Pointwise

namespace LieLean.QuantumGroup

/-! ### Bases of `L / c L` -/

section QuotientBasis

variable {A L : Type*} [CommRing A] [AddCommGroup L] [Module A L] (c : A)

/-- The classes of a basis of `L` are linearly independent in `L / c L` over `A / cA`. -/
lemma linearIndependent_mk_basis {ι : Type*} (b : Module.Basis ι A L) :
    LinearIndependent (A ⧸ Ideal.span {c})
      (fun i ↦ (Submodule.Quotient.mk (b i) : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose g' hg' using fun i ↦ Ideal.Quotient.mk_surjective (I := Ideal.span {c}) (g i)
  simp_rw [← hg', Module.Quotient.mk_smul_mk] at hg
  rw [show ∑ i ∈ s, (Submodule.Quotient.mk (g' i • b i) :
      L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) =
      Submodule.Quotient.mk (∑ i ∈ s, g' i • b i) from (map_sum (Submodule.mkQ _) _ _).symm,
    Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hg
  obtain ⟨y, -, hy⟩ := hg
  have h := congrArg (fun z ↦ b.repr z i) hy
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Module.Basis.repr_self,
    Finsupp.smul_single, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply] at h
  rw [Finset.sum_ite_eq' s i] at h
  simp only [hi, ↓reduceIte, mul_one] at h
  rw [← hg', Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨_, (mul_comm _ _).trans h⟩

/-- The classes of a basis of `L` span `L / c L` over `A / cA`. -/
lemma span_mk_basis {ι : Type*} (b : Module.Basis ι A L) :
    Submodule.span (A ⧸ Ideal.span {c}) (Set.range
      (fun i ↦ (Submodule.Quotient.mk (b i) : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)))) =
      ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
    show (Submodule.Quotient.mk (∑ i ∈ (b.repr x).support, (b.repr x) i • b i) :
      L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) =
      ∑ i ∈ (b.repr x).support, Submodule.Quotient.mk ((b.repr x) i • b i) from
      map_sum (Submodule.mkQ _) _ _]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [← Module.Quotient.mk_smul_mk]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end QuotientBasis

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  (V : IntegrableSl2 q M) (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]

/-! ### Crystal bases at one colour -/

/-- A crystal base of an integrable `U_q(𝔰𝔩₂)`-module ([HK] Def. 4.2.3 for `𝔰𝔩₂`): a free
Kashiwara-stable `A`-submodule `L` spanning `M` over `k`, and a basis `B` of the `A/cA`-module
`L/cL` of classes of weight vectors with `ẽ B, f̃ B ⊆ B ∪ {0}` and `f̃ b = b' ↔ ẽ b' = b`. -/
structure IsCrystalBase (L : Submodule A M) (c : A)
    (B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))) : Prop where
  isKashiwaraStable : V.IsKashiwaraStable hq0 hq L
  span_eq_top : Submodule.span k (L : Set M) = ⊤
  free : Module.Free A L
  linearIndependent : LinearIndependent (A ⧸ Ideal.span {c}) (Subtype.val : B → _)
  span_quot_eq_top : Submodule.span (A ⧸ Ideal.span {c}) B = ⊤
  exists_wt : ∀ b ∈ B, ∃ n, ∃ x : L, (x : M) ∈ V.wt n ∧ Submodule.Quotient.mk x = b
  eQ_mem : ∀ b ∈ B, V.eTildeQ hq0 hq isKashiwaraStable.eTilde_mem c b ∈ B ∨
    V.eTildeQ hq0 hq isKashiwaraStable.eTilde_mem c b = 0
  fQ_mem : ∀ b ∈ B, V.fTildeQ hq0 hq isKashiwaraStable.fTilde_mem c b ∈ B ∨
    V.fTildeQ hq0 hq isKashiwaraStable.fTilde_mem c b = 0
  fQ_eq_iff : ∀ b ∈ B, ∀ b' ∈ B, V.fTildeQ hq0 hq isKashiwaraStable.fTilde_mem c b = b' ↔
    V.eTildeQ hq0 hq isKashiwaraStable.eTilde_mem c b' = b

/-! ### String bases -/

variable {V} {ι : Type*} {p : ι → ℕ} {η : ι → M}

/-- The index `(pₜ - 2j, j)` of the string summand containing `F^{(j)} ηₜ`. -/
def stringIndex (p : ι → ℕ) (x : Σ t, Fin (p t + 1)) : ℤ × ℕ :=
  ((p x.1 : ℤ) - 2 * (x.2 : ℕ), (x.2 : ℕ))

include hq0 hq in
/-- The vectors `F^{(j)} ηₜ` (`j ≤ pₜ`) are linearly independent if the primitive vectors
`ηₜ ∈ M^{pₜ}` with equal `pₜ` are. -/
theorem linearIndependent_dF (hη : ∀ t, η t ∈ V.prim (p t))
    (hind : ∀ p₀ : ℕ, LinearIndependent k (fun t : {t // p t = p₀} ↦ η t)) :
    LinearIndependent k (fun x : Σ t, Fin (p t + 1) ↦ V.dF x.2 (η x.1)) := by
  classical
  let F := stringIndex p
  have hmem : ∀ i (x : {x // F x = i}), η x.1.1 ∈ V.stringSummand i := by
    rintro i ⟨⟨t, j⟩, rfl⟩
    rw [mem_stringSummand (by simp only [stringIndex]; omega)]
    convert hη t using 2
    simp only [stringIndex]
    ring
  set f : ∀ i, {x // F x = i} → V.stringSummand i := fun i x ↦ ⟨η x.1.1, hmem i x⟩
  have hf : ∀ i, LinearIndependent k (f i) := by
    rintro ⟨n, j⟩
    refine LinearIndependent.of_comp (V.stringSummand (n, j)).subtype ?_
    -- reduce to the independence of the `ηₜ` with `pₜ = (n + 2j).toNat`
    let g : {x // F x = (n, j)} → {t // p t = (n + 2 * j).toNat} := fun x ↦
      ⟨x.1.1, by
        have h := x.2
        simp only [F, stringIndex, Prod.mk.injEq] at h
        omega⟩
    have hg : Function.Injective g := by
      rintro ⟨⟨t, j₁⟩, h₁⟩ ⟨⟨t', j₂⟩, h₂⟩ h
      simp only [g, Subtype.mk.injEq] at h
      subst h
      simp only [F, stringIndex, Prod.mk.injEq] at h₁ h₂
      have : j₁ = j₂ := Fin.ext (by omega)
      subst this
      rfl
    exact (hind _).comp g hg
  have hy := DFinsupp.linearIndependent_single f hf
  have hy' := hy.comp (Equiv.sigmaFiberEquiv F).symm (Equiv.injective _)
  have hmap := hy'.map' (V.stringEquiv hq0 hq).toLinearMap (LinearEquiv.ker _)
  convert hmap using 1
  ext x
  simp only [Function.comp_apply, LinearEquiv.coe_coe]
  have e : (Equiv.sigmaFiberEquiv F).symm x = ⟨F x, ⟨x, rfl⟩⟩ := rfl
  rw [e]
  exact (stringMap_lof (F x) ⟨η x.1, hmem _ ⟨x, rfl⟩⟩).symm

include hq0 hq in
/-- The vectors `F^{(j)} ηₜ` (`j ≤ pₜ`) span `M` if for every `p` the `ηₜ` with `pₜ = p` span the
primitive vectors of weight `p`. -/
theorem span_dF (hspan : ∀ p₀ : ℕ,
      V.prim p₀ ≤ Submodule.span k (Set.range fun t : {t // p t = p₀} ↦ η t)) :
    Submodule.span k (Set.range fun x : Σ t, Fin (p t + 1) ↦ V.dF x.2 (η x.1)) = ⊤ := by
  rw [eq_top_iff, ← V.iSup_wt, iSup_le_iff]
  intro n m hm
  refine wt_induction (V := V) hq0 hq (P := fun m ↦ m ∈ Submodule.span k _)
    (zero_mem _) (fun _ _ ↦ add_mem) (fun c _ ↦ Submodule.smul_mem _ c) ?_ hm
  intro p₀ j ζ hjp _ hζ hE
  have h := Submodule.map_mono (f := V.dF j) (hspan p₀)
  rw [Submodule.map_span] at h
  refine Submodule.span_le.2 ?_ (h ⟨ζ, ⟨hζ, hE⟩, rfl⟩)
  rintro _ ⟨_, ⟨⟨t, ht⟩, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨⟨t, ⟨j, by omega⟩⟩, rfl⟩

/-! ### The crystal base spanned by a string basis -/

lemma sigma_ext {x y : Σ t, Fin (p t + 1)} (h1 : x.1 = y.1) (h2 : (x.2 : ℕ) = y.2) : x = y := by
  obtain ⟨t, j⟩ := x
  obtain ⟨t', j'⟩ := y
  dsimp only at h1 h2
  subst h1
  rw [Fin.ext h2]

lemma sigma_eq_iff {t t' : ι} {j : Fin (p t + 1)} {j' : Fin (p t' + 1)} :
    (⟨t, j⟩ : Σ t, Fin (p t + 1)) = ⟨t', j'⟩ ↔ t = t' ∧ (j : ℕ) = j' :=
  ⟨fun h ↦ by cases h; simp, fun h ↦ sigma_ext h.1 h.2⟩

variable (V A η) in
/-- The `A`-span of the vectors `F^{(j)} ηₜ`, `j ≤ pₜ`. -/
def stringLattice (p : ι → ℕ) : Submodule A M :=
  Submodule.span A (Set.range fun x : Σ t, Fin (p t + 1) ↦ V.dF x.2 (η x.1))

variable (V A η) in
/-- The vector `F^{(j)} ηₜ` of `stringLattice`. -/
noncomputable def stringVec (x : Σ t, Fin (p t + 1)) : V.stringLattice A η p :=
  ⟨V.dF x.2 (η x.1), Submodule.subset_span ⟨x, rfl⟩⟩

variable [FaithfulSMul A k]

include hq0 hq in
lemma linearIndependent_stringVec (hη : ∀ t, η t ∈ V.prim (p t))
    (hind : ∀ p₀ : ℕ, LinearIndependent k (fun t : {t // p t = p₀} ↦ η t)) :
    LinearIndependent A (fun x : Σ t, Fin (p t + 1) ↦ V.dF x.2 (η x.1)) :=
  (linearIndependent_dF hq0 hq hη hind).restrict_scalars' A

/-- The basis `F^{(j)} ηₜ` of `stringLattice`. -/
noncomputable def stringLatticeBasis (hη : ∀ t, η t ∈ V.prim (p t))
    (hind : ∀ p₀ : ℕ, LinearIndependent k (fun t : {t // p t = p₀} ↦ η t)) :
    Module.Basis (Σ t, Fin (p t + 1)) A (V.stringLattice A η p) :=
  Module.Basis.span (linearIndependent_stringVec hq0 hq hη hind)

lemma stringLatticeBasis_apply (hη : ∀ t, η t ∈ V.prim (p t))
    (hind : ∀ p₀ : ℕ, LinearIndependent k (fun t : {t // p t = p₀} ↦ η t))
    (x : Σ t, Fin (p t + 1)) : stringLatticeBasis hq0 hq hη hind x = V.stringVec A η x :=
  Module.Basis.span_apply _ x

omit [FaithfulSMul A k] [Algebra A k] [IsScalarTower A k M] in
include hq0 hq in
lemma eTilde_stringVec (hη : ∀ t, η t ∈ V.prim (p t)) (x : Σ t, Fin (p t + 1)) :
    V.eTilde hq0 hq (V.stringVec A η x) =
      if h : (x.2 : ℕ) = 0 then 0
      else (V.stringVec A η (p := p) ⟨x.1, ⟨x.2 - 1, by omega⟩⟩ : M) := by
  obtain ⟨t, j, hj⟩ := x
  split_ifs with h
  · simp only at h
    subst h
    change V.eTilde hq0 hq (V.dF 0 (η t)) = 0
    rw [dF_zero]
    exact eTilde_of_primitive hq0 hq (hη t).2 (hη t).1
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    exact eTilde_dF_succ (p := (p t : ℤ)) hq0 hq (hη t).2 (hη t).1 (by omega)

omit [FaithfulSMul A k] [Algebra A k] [IsScalarTower A k M] in
include hq0 hq in
lemma fTilde_stringVec (hη : ∀ t, η t ∈ V.prim (p t)) (x : Σ t, Fin (p t + 1)) :
    V.fTilde hq0 hq (V.stringVec A η x) =
      if h : (x.2 : ℕ) < p x.1 then (V.stringVec A η (p := p) ⟨x.1, ⟨x.2 + 1, by omega⟩⟩ : M)
      else 0 := by
  obtain ⟨t, j, hj⟩ := x
  change V.fTilde hq0 hq (V.dF j (η t)) = _
  rw [fTilde_dF (p := (p t : ℤ)) hq0 hq (hη t).2 (hη t).1]
  split_ifs with h
  · rfl
  · exact dF_eq_zero_of_primitive hq0 hq (hη t).1 (hη t).2 (by simp only [not_lt] at h; omega)

omit [FaithfulSMul A k] [Algebra A k] [IsScalarTower A k M] in
lemma stringVec_mem_wt (hη : ∀ t, η t ∈ V.prim (p t)) (x : Σ t, Fin (p t + 1)) :
    (V.stringVec A η x : M) ∈ V.wt ((p x.1 : ℤ) - 2 * (x.2 : ℕ)) :=
  dF_mem (hη x.1).1 _

omit [FaithfulSMul A k] in
include hq0 hq in
/-- The span of a string basis is Kashiwara-stable. -/
theorem isKashiwaraStable_stringLattice (hη : ∀ t, η t ∈ V.prim (p t)) :
    V.IsKashiwaraStable hq0 hq (V.stringLattice A η p) := by
  have key : ∀ T : Module.End k M,
      (∀ x : Σ t, Fin (p t + 1), T (V.stringVec A η x : M) ∈ V.stringLattice A η p) →
      ∀ m ∈ V.stringLattice A η p, T m ∈ V.stringLattice A η p := by
    intro T hT m hm
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨x, rfl⟩ := hx; exact hT x
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  refine ⟨fun m hm n ↦ key _ (fun x ↦ ?_) m hm, key _ (fun x ↦ ?_), key _ (fun x ↦ ?_)⟩
  · rw [wtProj_of_mem (stringVec_mem_wt hη x)]
    split_ifs
    · exact (V.stringVec A η x).2
    · exact zero_mem _
  · rw [eTilde_stringVec hq0 hq hη]
    split_ifs
    · exact zero_mem _
    · exact (V.stringVec A η _).2
  · rw [fTilde_stringVec hq0 hq hη]
    split_ifs
    · exact (V.stringVec A η _).2
    · exact zero_mem _

include hq0 hq in
lemma mk_stringVec_injective (hη : ∀ t, η t ∈ V.prim (p t))
    (hind : ∀ p₀ : ℕ, LinearIndependent k (fun t : {t // p t = p₀} ↦ η t)) {c : A}
    (hc : ¬IsUnit c) :
    Function.Injective fun x : Σ t, Fin (p t + 1) ↦
      (Submodule.Quotient.mk (V.stringVec A η x) :
        V.stringLattice A η p ⧸ (Ideal.span {c} • ⊤ : Submodule A (V.stringLattice A η p))) := by
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have h := (linearIndependent_mk_basis c (stringLatticeBasis hq0 hq hη hind)).injective
  simpa only [stringLatticeBasis_apply] using h

include hq0 hq in
/-- Existence of crystal bases of integrable `U_q(𝔰𝔩₂)`-modules ([HK] Ex. 4.2.6, Thm. 4.3.1, there
for finite-dimensional modules): if the primitive vectors `ηₜ ∈ M^{pₜ}` with `pₜ = p` form a basis
of the primitive vectors of weight `p` for every `p`, the `A`-span `L` of the `F^{(j)} ηₜ`
(`j ≤ pₜ`) and their classes in `L / c L` form a crystal base. -/
theorem isCrystalBase_stringLattice (hη : ∀ t, η t ∈ V.prim (p t))
    (hind : ∀ p₀ : ℕ, LinearIndependent k (fun t : {t // p t = p₀} ↦ η t))
    (hspan : ∀ p₀ : ℕ,
      V.prim p₀ ≤ Submodule.span k (Set.range fun t : {t // p t = p₀} ↦ η t))
    {c : A} (hc : ¬IsUnit c) :
    V.IsCrystalBase hq0 hq (V.stringLattice A η p) c
      (Set.range fun x ↦ Submodule.Quotient.mk (V.stringVec A η x)) := by
  have hL := isKashiwaraStable_stringLattice (A := A) hq0 hq hη
  have hinj := mk_stringVec_injective hq0 hq hη hind hc
  set b := stringLatticeBasis (A := A) hq0 hq hη hind
  set Q := V.stringLattice A η p ⧸ (Ideal.span {c} • ⊤ : Submodule A (V.stringLattice A η p))
  have hB : (Set.range fun x ↦ (Submodule.Quotient.mk (V.stringVec A η x) : Q)) =
      Set.range fun x ↦ (Submodule.Quotient.mk (b x) : Q) := by
    simp only [b, stringLatticeBasis_apply]
  have hli := linearIndependent_mk_basis c b
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hne : ∀ x, (Submodule.Quotient.mk (V.stringVec A η x) : Q) ≠ 0 := fun x ↦ by
    have := hli.ne_zero x
    simpa only [b, stringLatticeBasis_apply] using this
  have heQ : ∀ x : Σ t, Fin (p t + 1), V.eTildeQ hq0 hq hL.eTilde_mem c
      (Submodule.Quotient.mk (V.stringVec A η x) : Q) = if h : (x.2 : ℕ) = 0 then 0 else
        Submodule.Quotient.mk (V.stringVec A η (p := p) ⟨x.1, ⟨x.2 - 1, by omega⟩⟩) := by
    intro x
    rw [eTildeQ_mk]
    split_ifs with h
    · have e : (⟨V.eTilde hq0 hq (V.stringVec A η x), hL.eTilde_mem _ (V.stringVec A η x).2⟩ :
          V.stringLattice A η p) = 0 :=
        Subtype.ext ((eTilde_stringVec hq0 hq hη x).trans (by simp [h]))
      rw [e, Submodule.Quotient.mk_zero]
    · congr 1
      exact Subtype.ext ((eTilde_stringVec hq0 hq hη x).trans (by simp [h]))
  have hfQ : ∀ x : Σ t, Fin (p t + 1), V.fTildeQ hq0 hq hL.fTilde_mem c
      (Submodule.Quotient.mk (V.stringVec A η x) : Q) = if h : (x.2 : ℕ) < p x.1 then
        Submodule.Quotient.mk (V.stringVec A η (p := p) ⟨x.1, ⟨x.2 + 1, by omega⟩⟩) else 0 := by
    intro x
    rw [fTildeQ_mk]
    split_ifs with h
    · congr 1
      exact Subtype.ext ((fTilde_stringVec hq0 hq hη x).trans (by simp [h]))
    · have e : (⟨V.fTilde hq0 hq (V.stringVec A η x), hL.fTilde_mem _ (V.stringVec A η x).2⟩ :
          V.stringLattice A η p) = 0 :=
        Subtype.ext ((fTilde_stringVec hq0 hq hη x).trans (by simp [h]))
      rw [e, Submodule.Quotient.mk_zero]
  refine
    { isKashiwaraStable := hL
      span_eq_top := ?_
      free := Module.Free.of_basis b
      linearIndependent := by rw [hB]; exact hli.linearIndepOn_id
      span_quot_eq_top := by rw [hB]; exact span_mk_basis c b
      exists_wt := ?_
      eQ_mem := ?_
      fQ_mem := ?_
      fQ_eq_iff := ?_ }
  · rw [eq_top_iff, ← span_dF hq0 hq hspan]
    exact Submodule.span_mono (by rintro _ ⟨x, rfl⟩; exact Submodule.subset_span ⟨x, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, _, stringVec_mem_wt hη x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    rw [heQ]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl ⟨_, rfl⟩
  · rintro _ ⟨x, rfl⟩
    rw [hfQ]
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr rfl
  · rintro _ ⟨⟨t, j⟩, rfl⟩ _ ⟨⟨t', j'⟩, rfl⟩
    rw [heQ, hfQ]
    dsimp only
    split_ifs with h h'
    · simp only [hinj.eq_iff, sigma_eq_iff]
      constructor
      · rintro ⟨rfl, h2⟩; omega
      · intro h3; exact absurd h3.symm (hne _)
    · simp only [hinj.eq_iff, sigma_eq_iff]
      constructor
      · rintro ⟨rfl, h2⟩; exact ⟨rfl, by omega⟩
      · rintro ⟨rfl, h2⟩; exact ⟨rfl, by omega⟩
    · constructor
      · intro h3; exact absurd h3.symm (hne _)
      · intro h3; exact absurd h3.symm (hne _)
    · constructor
      · intro h3; exact absurd h3.symm (hne _)
      · simp only [hinj.eq_iff, sigma_eq_iff]
        rintro ⟨rfl, h2⟩
        omega

end IntegrableSl2

/-- A crystal base of an integrable `U`-module restricts to a crystal base of `nodeSl2` at every
node. -/
theorem IsCrystalBase.isCrystalBase_nodeSl2 {k I Y : Type*} [Field k] [AddCommGroup Y]
    [DecidableEq I] {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}
    {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
    [IsScalarTower k (QuantumGroup R v) M] [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1}
    {hM : IsIntegrable R v M} {A : Type*} [CommRing A] [Algebra A k] [Module A M]
    [IsScalarTower A k M] {L : Submodule A M} {hL : IsCrystalLattice hv hM L} {c : A}
    {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))} (hB : IsCrystalBase hL c B) (i : I) :
    (nodeSl2 R v M hv hM i).IsCrystalBase (pow_d_ne_zero i) (pow_d_ne_one hv i) L c B where
  isKashiwaraStable := hL.isKashiwaraStable i
  span_eq_top := hL.span_eq_top
  free := hL.free
  linearIndependent := hB.linearIndependent
  span_quot_eq_top := hB.span_eq_top
  exists_wt b hb := by
    obtain ⟨Λ, x, hx, hxb⟩ := hB.exists_weight b hb
    exact ⟨Λ (R.coroot i), x, mem_nodeWt_of_mem hx, hxb⟩
  eQ_mem := hB.eQ_mem i
  fQ_mem := hB.fQ_mem i
  fQ_eq_iff := hB.fQ_eq_iff i

end LieLean.QuantumGroup
