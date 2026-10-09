/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.HighestWeightMaps
import LieLean.Algebra.QuantumGroup.CrystalBasis.CrystalBase

/-!
# The lattice `L(Λ)` and the set `B(Λ)` of `L_q(Λ)`

Let `U = U_q(𝔤)` (`QuantumGroup R v`) for an `X`-regular root datum, `v` not a root of unity, and
`Λ` dominant. Kashiwara's candidate crystal base of the irreducible module `L_q(Λ)` is
`L(Λ) = Σ A f̃_{i₁} ⋯ f̃_{iᵣ} v_Λ` and `B(Λ) = {f̃_{i₁} ⋯ f̃_{iᵣ} v_Λ mod c L(Λ)} \ {0}`.

## Main definitions

* `QuantumGroup.IrreducibleModule.fWord`: `f̃_{i₁} ⋯ f̃_{iᵣ} v_Λ`.
* `QuantumGroup.IrreducibleModule.lattice`, `QuantumGroup.IrreducibleModule.base`: `L(Λ)`, `B(Λ)`
  (for any `A`-algebra structure on `k` and `c ∈ A`).

## Main results

* `QuantumGroup.F_smul_mem_span_kashiwaraF`: in an integrable module, `Fᵢ x` for a weight vector `x`
  of weight `μ` is a combination of vectors `f̃ᵢ^{j+1} u` with `u` of weight `μ + j αᵢ`.
* `QuantumGroup.IrreducibleModule.span_fWord`: the vectors `f̃_{i₁} ⋯ f̃_{iᵣ} v_Λ` span `L_q(Λ)`
  over `k`; hence `L(Λ)` spans `L_q(Λ)` (`span_lattice`).
* `L(Λ)` is graded by the weight spaces and stable under the `f̃ᵢ` (`weightSetProj_mem_lattice`,
  `kashiwaraF_mem_lattice`).

The spanning argument is by induction on the depth `Λ - μ`, decomposing into `i`-strings; cf. [HK]
§5.1. The formulation is ours.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, Ch. 5.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

/-! ### Scalars from a subring -/

/-- `U` is an algebra over every ring `A` over which `k` is an algebra. For `A = k` this agrees
(definitionally) with the given `k`-algebra structure; it has low priority. -/
instance (priority := 100) instAlgebraOfAlgebra {A : Type*} [CommSemiring A] [Algebra A k] :
    Algebra A (QuantumGroup R v) :=
  inferInstanceAs (Algebra A (RingQuot _))

instance {A : Type*} [CommSemiring A] [Algebra A k] : IsScalarTower A k (QuantumGroup R v) :=
  inferInstanceAs (IsScalarTower A k (RingQuot _))

/-! ### `Fᵢ` through Kashiwara operators -/

section Strings

variable [NeZero v] {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  (hM : IsIntegrable R v M) (i : I)

lemma weightSetProj_singleton_mem (Λ : Y →+ ℤ) (m : M) :
    weightSetProj hv hM {Λ} m ∈ weightSpace R v M Λ := by
  have hm : m ∈ ⨆ Λ', weightSpace R v M Λ' := by rw [hM.iSup_weightSpace_eq_top]; trivial
  induction hm using Submodule.iSup_induction' with
  | mem Λ' m hm =>
    classical
    rw [weightSetProj_of_mem hv hM _ hm]
    split_ifs with h
    · rw [Set.mem_singleton_iff] at h; exact h ▸ hm
    · exact zero_mem _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb

/-- The projection onto `M^{Λ - αᵢ}` after `f̃ᵢ` is `f̃ᵢ` after the projection onto `M^Λ`. -/
lemma weightSetProj_singleton_kashiwaraF (Λ : Y →+ ℤ) (m : M) :
    weightSetProj hv hM {Λ - R.root i} (kashiwaraF R v M hv hM i m) =
      kashiwaraF R v M hv hM i (weightSetProj hv hM {Λ} m) := by
  have := ext_weightSpace hM
    (f := weightSetProj hv hM {Λ - R.root i} ∘ₗ kashiwaraF R v M hv hM i)
    (g := kashiwaraF R v M hv hM i ∘ₗ weightSetProj hv hM {Λ}) fun Λ' m hm ↦ by
      classical
      simp only [LinearMap.comp_apply]
      rw [weightSetProj_of_mem hv hM _ (kashiwaraF_mem_weightSpace hv hM i hm),
        weightSetProj_of_mem hv hM _ hm]
      simp only [Set.mem_singleton_iff, sub_left_inj]
      split_ifs <;> simp
  exact LinearMap.congr_fun this m

lemma weightSetProj_singleton_kashiwaraF_pow (Λ : Y →+ ℤ) (j : ℕ) (m : M) :
    weightSetProj hv hM {Λ - j • R.root i} ((kashiwaraF R v M hv hM i ^ j) m) =
      (kashiwaraF R v M hv hM i ^ j) (weightSetProj hv hM {Λ} m) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, succ_nsmul, ← sub_sub,
      weightSetProj_singleton_kashiwaraF, ih]

/-- On an `Eᵢ`-primitive vector, `f̃ᵢ^j = Fᵢ^{(j)}`. -/
lemma kashiwaraF_pow_of_primitive {p : ℤ} {η : M} (hη : E R v i • η = 0)
    (hp : η ∈ nodeWt R v M i p) (j : ℕ) :
    (kashiwaraF R v M hv hM i ^ j) η = (nodeSl2 R v M hv hM i).dF j η := by
  induction j with
  | zero => simp [qDivPow]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    exact IntegrableSl2.fTilde_dF (V := nodeSl2 R v M hv hM i) _ _ hη hp j

/-- `Fᵢ x`, for `x` of weight `μ`, is a combination of vectors `f̃ᵢ^{j+1} u` with `u` of weight
`μ + j αᵢ`: write `x = Σⱼ Fᵢ^{(j)} ηⱼ` with `ηⱼ` primitive, so `Fᵢ x = Σⱼ [j+1] f̃ᵢ^{j+1} ηⱼ`, and
project onto weight spaces. -/
theorem F_smul_mem_span_kashiwaraF {μ : Y →+ ℤ} {x : M} (hx : x ∈ weightSpace R v M μ) :
    F R v i • x ∈ Submodule.span k {y | ∃ (j : ℕ) (u : M),
      u ∈ weightSpace R v M (μ + j • R.root i) ∧ y = (kashiwaraF R v M hv hM i ^ (j + 1)) u} := by
  classical
  set V := nodeSl2 R v M hv hM i
  obtain ⟨N, η, hη, -, -, hsum⟩ := IntegrableSl2.exists_sum_dF (V := V) (pow_d_ne_zero i)
    (pow_d_ne_one hv i) (mem_nodeWt_of_mem (i := i) hx)
  have hF : F R v i • x = ∑ j ∈ Finset.range N, qInt (v ^ D.d i) (j + 1) •
      (kashiwaraF R v M hv hM i ^ (j + 1)) (η j) := by
    change V.F x = _
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [V.F_dF (pow_d_ne_zero i) (pow_d_ne_one hv i),
      kashiwaraF_pow_of_primitive hv hM i (hη j).2 (hη j).1]
  have hFx : F R v i • x ∈ weightSpace R v M (μ - R.root i) := F_smul_mem_weightSpace hx i
  have hP := weightSetProj_of_mem hv hM {μ - R.root i} hFx
  simp only [Set.mem_singleton_iff, ↓reduceIte] at hP
  rw [← hP, hF, map_sum]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, _,
    weightSetProj_singleton_mem hv hM (μ + j • R.root i) (η j), ?_⟩)
  rw [← weightSetProj_singleton_kashiwaraF_pow]
  congr 2
  rw [succ_nsmul]
  abel_nf

end Strings

/-! ### `L(Λ)` and `B(Λ)` -/

section Irreducible

variable [NeZero v] (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {Λ : Y →+ ℤ}
  (hΛ : ∀ i, 0 ≤ Λ (R.coroot i))

omit [DecidableEq I] in
lemma _root_.LusztigCartanDatum.RootDatum.rootSum_injective (hR : R.IsXRegular) :
    Function.Injective R.rootSum := fun ν ν' h ↦ by
  by_contra hne
  obtain ⟨μ, hμ⟩ := R.exists_rootSum_ne hR hne
  exact hμ (by rw [h])

namespace IrreducibleModule

/-- The vector `f̃_{i₁} ⋯ f̃_{iᵣ} v_Λ` of `L_q(Λ)`. -/
def fWord : List I → IrreducibleModule R v Λ
  | [] => hwv R v Λ
  | i :: w => kashiwaraF R v _ hv' (isIntegrable hR hv' hΛ) i (fWord w)

@[simp] lemma fWord_nil : fWord hR hv' hΛ [] = hwv R v Λ := rfl

@[simp] lemma fWord_cons (i : I) (w : List I) :
    fWord hR hv' hΛ (i :: w) =
      kashiwaraF R v _ hv' (isIntegrable hR hv' hΛ) i (fWord hR hv' hΛ w) := rfl

lemma fWord_mem_weightSpace (w : List I) :
    fWord hR hv' hΛ w ∈
      weightSpace R v (IrreducibleModule R v Λ) (Λ - R.rootSum (LusztigF.wordWeight w)) := by
  induction w with
  | nil => simpa using hwv_mem_weightSpace
  | cons i w ih =>
    rw [fWord_cons, LusztigF.wordWeight_cons, R.rootSum_add, R.rootSum_single, one_smul,
      add_comm, ← sub_sub]
    exact kashiwaraF_mem_weightSpace hv' _ i ih

include hv' in
/-- The weights of `L_q(Λ)` lie in `Λ - ℕ[I]`. -/
theorem exists_eq_sub_rootSum {Λ' : Y →+ ℤ} {x : IrreducibleModule R v Λ}
    (hx : x ∈ weightSpace R v (IrreducibleModule R v Λ) Λ') (hx0 : x ≠ 0) :
    ∃ ν, Λ' = Λ - R.rootSum ν := by
  by_contra! h
  have hle := weightSpace_quotient_le_map hv' VermaModule.iSup_weightSpace_eq_top
    (VermaModule.maxSubmodule R v Λ) Λ'
  rw [VermaModule.weightSpace_eq_bot hv' h, Submodule.map_bot] at hle
  exact hx0 ((Submodule.mem_bot k).1 (hle hx))

/-- The vectors `f̃_{i₁} ⋯ f̃_{iᵣ} v_Λ` span `L_q(Λ)` over `k` (cf. [HK] §5.1). -/
theorem span_fWord : Submodule.span k (Set.range (fWord (Λ := Λ) hR hv' hΛ)) = ⊤ := by
  set W := Submodule.span k (Set.range (fWord (Λ := Λ) hR hv' hΛ))
  set hI := isIntegrable hR hv' hΛ
  have hW : ∀ i, ∀ m ∈ W, kashiwaraF R v _ hv' hI i m ∈ W := by
    intro i m hm
    have : W.map (kashiwaraF R v _ hv' hI i) ≤ W := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w, rfl⟩
      exact Submodule.subset_span ⟨i :: w, rfl⟩
    exact this ⟨m, hm, rfl⟩
  have hWpow : ∀ i j, ∀ m ∈ W, (kashiwaraF R v _ hv' hI i ^ j) m ∈ W := by
    intro i j
    induction j with
    | zero => intro m hm; simpa using hm
    | succ j ih => intro m hm; rw [pow_succ', Module.End.mul_apply]; exact hW i _ (ih m hm)
  have key : ∀ ν : I →₀ ℕ,
      weightSpace R v (IrreducibleModule R v Λ) (Λ - R.rootSum ν) ≤ W := by
    intro ν
    induction hn : (ν.sum fun _ n ↦ n) using Nat.strong_induction_on generalizing ν with
    | _ n ih =>
    intro x hx
    have hle := weightSpace_quotient_le_map hv' VermaModule.iSup_weightSpace_eq_top
      (VermaModule.maxSubmodule R v Λ) (Λ - R.rootSum ν)
    rw [VermaModule.weightSpace_eq_map hv' hR ν] at hle
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hle hx
    clear hx hle
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      cases w with
      | nil =>
        have : (VermaModule.maxSubmodule R v Λ).mkQ.restrictScalars k
            (VermaModule.toVerma R v Λ (LusztigF.monomial k [])) = hwv R v Λ := by
          simp [VermaModule.toVerma_apply, hwv]
        rw [this]
        exact Submodule.subset_span ⟨[], rfl⟩
      | cons i w =>
        simp only [Set.mem_ofPred_eq] at hw
        set z : IrreducibleModule R v Λ := Submodule.Quotient.mk
          (VermaModule.toVerma R v Λ (LusztigF.monomial k w))
        have hz : z ∈ weightSpace R v (IrreducibleModule R v Λ)
            (Λ - R.rootSum (LusztigF.wordWeight w)) :=
          map_mem_weightSpace (VermaModule.maxSubmodule R v Λ).mkQ
            (VermaModule.toVerma_mem_weightSpace (LusztigF.monomial_mem_weightSpace w))
        have hxz : (VermaModule.maxSubmodule R v Λ).mkQ.restrictScalars k
            (VermaModule.toVerma R v Λ (LusztigF.monomial k (i :: w))) = F R v i • z := by
          simp only [LinearMap.coe_restrictScalars, Submodule.mkQ_apply, z,
            LusztigF.monomial_cons, VermaModule.toVerma_apply, map_mul, mul_smul, minusHom_θ,
            Submodule.Quotient.mk_smul]
        rw [hxz]
        refine (Submodule.span_le.2 ?_) (F_smul_mem_span_kashiwaraF hv' hI i hz)
        rintro _ ⟨j, u, hu, rfl⟩
        refine hWpow i (j + 1) u ?_
        by_cases hu0 : u = 0
        · rw [hu0]; exact zero_mem _
        obtain ⟨ν', hν'⟩ := exists_eq_sub_rootSum hv' hu hu0
        have hroot : R.rootSum (ν' + Finsupp.single i j) = R.rootSum (LusztigF.wordWeight w) := by
          rw [R.rootSum_add, R.rootSum_single]
          have := congrArg (fun μ ↦ Λ - μ) hν'
          simp only [sub_sub_cancel] at this
          rw [← this]
          abel
        have hνw := LusztigCartanDatum.RootDatum.rootSum_injective hR hroot
        have hlt : (ν'.sum fun _ n ↦ n) < n := by
          rw [← hn, ← hw, LusztigF.wordWeight_cons, ← hνw,
            Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp),
            Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]
          omega
        rw [hν'] at hu
        exact ih _ hlt ν' rfl hu
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff, ← hI.iSup_weightSpace_eq_top]
  refine iSup_le fun Λ' ↦ ?_
  intro x hx
  by_cases hx0 : x = 0
  · rw [hx0]; exact zero_mem _
  obtain ⟨ν, rfl⟩ := exists_eq_sub_rootSum hv' hx hx0
  exact key ν hx

variable (A : Type*) [CommRing A] [Algebra A k]

/-- Kashiwara's lattice `L(Λ) = Σ A f̃_{i₁} ⋯ f̃_{iᵣ} v_Λ` ([HK] §5.1). -/
def lattice : Submodule A (IrreducibleModule R v Λ) :=
  Submodule.span A (Set.range (fWord (Λ := Λ) hR hv' hΛ))

lemma fWord_mem_lattice (w : List I) : fWord hR hv' hΛ w ∈ lattice hR hv' hΛ A :=
  Submodule.subset_span ⟨w, rfl⟩

lemma hwv_mem_lattice : hwv R v Λ ∈ lattice hR hv' hΛ A :=
  fWord_mem_lattice hR hv' hΛ A []

/-- `L(Λ)` spans `L_q(Λ)` over `k`. -/
theorem span_lattice : Submodule.span k (lattice hR hv' hΛ A : Set (IrreducibleModule R v Λ)) = ⊤ :=
  eq_top_iff.2 <| (span_fWord hR hv' hΛ).symm.le.trans <|
    Submodule.span_mono (by rintro _ ⟨w, rfl⟩; exact fWord_mem_lattice hR hv' hΛ A w)

/-- `f̃ᵢ L(Λ) ⊆ L(Λ)`. -/
theorem kashiwaraF_mem_lattice (i : I) {m : IrreducibleModule R v Λ}
    (hm : m ∈ lattice hR hv' hΛ A) :
    kashiwaraF R v _ hv' (isIntegrable hR hv' hΛ) i m ∈ lattice hR hv' hΛ A := by
  have : (lattice hR hv' hΛ A).map
      ((kashiwaraF R v _ hv' (isIntegrable hR hv' hΛ) i).restrictScalars A) ≤
      lattice hR hv' hΛ A := by
    rw [lattice, Submodule.map_span_le]
    rintro _ ⟨w, rfl⟩
    exact fWord_mem_lattice hR hv' hΛ A (i :: w)
  exact this ⟨m, hm, rfl⟩

/-- `L(Λ)` is graded by the weight spaces. -/
theorem weightSetProj_mem_lattice (S : Set (Y →+ ℤ)) {m : IrreducibleModule R v Λ}
    (hm : m ∈ lattice hR hv' hΛ A) :
    weightSetProj hv' (isIntegrable hR hv' hΛ) S m ∈ lattice hR hv' hΛ A := by
  have : (lattice hR hv' hΛ A).map
      ((weightSetProj hv' (isIntegrable hR hv' hΛ) S).restrictScalars A) ≤
      lattice hR hv' hΛ A := by
    rw [lattice, Submodule.map_span_le]
    rintro _ ⟨w, rfl⟩
    classical
    rw [LinearMap.coe_restrictScalars,
      weightSetProj_of_mem hv' _ S (fWord_mem_weightSpace hR hv' hΛ w)]
    split_ifs
    · exact fWord_mem_lattice hR hv' hΛ A w
    · exact zero_mem _
  exact this ⟨m, hm, rfl⟩

/-- Kashiwara's `B(Λ)`: the nonzero classes of the `f̃_{i₁} ⋯ f̃_{iᵣ} v_Λ` in `L(Λ)/c L(Λ)`
([HK] §5.1). -/
def base (c : A) : Set (lattice hR hv' hΛ A ⧸
    (Ideal.span {c} • ⊤ : Submodule A (lattice hR hv' hΛ A))) :=
  (Set.range fun w ↦ Submodule.Quotient.mk ⟨fWord hR hv' hΛ w, fWord_mem_lattice hR hv' hΛ A w⟩) \
    {0}

end IrreducibleModule

end Irreducible

end LieLean.QuantumGroup
