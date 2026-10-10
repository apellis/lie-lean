/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.TriangularBasis

/-!
# The triangular `𝒜`-basis of `𝒜U̇` ([Lus] 23.2.2 (b))

Over `ℚ(v)`, `𝒜 = ℤ[v, v⁻¹]`. Let `(bᵢ)` be a basis of `U⁻` and `(b'ⱼ)` a basis of `U⁺` consisting
of weight vectors, with `bᵢ ∈ 𝒜U⁻`, `b'ⱼ ∈ 𝒜U⁺`, and such that the monomials `F_w` (resp. `E_w`) in
divided powers have `𝒜`-coordinates; that is, `(bᵢ)` is an `𝒜`-basis of `𝒜U⁻` (the image of `𝒜f`)
which is also a `ℚ(v)`-basis of `U⁻`, and likewise for `(b'ⱼ)`. Then the elements
`bᵢ 1_λ b'ⱼ` (`λ ∈ X`) of the triangular basis of `U̇` ([Lus] 23.2.1) form an `𝒜`-basis of `𝒜U̇`
(`Modified.aTriangularBasis`; [Lus] 23.2.2 (b), where Lusztig takes `bᵢ = b⁻`, `b'ⱼ = b'⁺` for an
`𝒜`-basis `B` of `𝒜f`).

## Main results

* `projW χ`: the projection `U → U_χ` along `U = ⊕_χ U_χ`.
* `Modified.aMinus R`: `𝒜U⁻`, the `𝒜`-combinations of the monomials `F_w`.
* `Modified.triFun_mem_aForm`, `Modified.mem_laurentCoords_of_mem_aForm`: the `bᵢ 1_λ b'ⱼ` lie in
  `𝒜U̇`, and the elements of `𝒜U̇` have `𝒜`-coordinates in the triangular basis.
* `Modified.aTriangularBasis`: **[Lus] 23.2.2 (b)**.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.2.1, 23.2.2.
-/

open LieLean Finset

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-! ### Projections to weight spaces -/

include hv in
lemma isCompl_otherWeights (χ : Y →+ ℤ) :
    IsCompl (adWeightSpace R v χ) (otherWeights R v χ) :=
  isCompl_iff.2 ⟨disjoint_iff.2 (inf_otherWeights hv χ), codisjoint_iff.2 (sup_otherWeights χ)⟩

variable (R) in
/-- The projection `U → U_χ` along `U = ⊕_χ U_χ`. -/
def projW (χ : Y →+ ℤ) : QuantumGroup R v →ₗ[k] QuantumGroup R v :=
  (adWeightSpace R v χ).subtype ∘ₗ Submodule.projectionOnto _ _ (isCompl_otherWeights hv χ)

lemma projW_of_mem {χ : Y →+ ℤ} {x : QuantumGroup R v} (hx : x ∈ adWeightSpace R v χ) :
    projW R hv χ x = x := by
  have := Submodule.projectionOnto_apply_left (isCompl_otherWeights (R := R) hv χ) ⟨x, hx⟩
  simp only [projW, LinearMap.comp_apply, Submodule.subtype_apply]
  exact congrArg Subtype.val this

lemma projW_of_mem_ne {χ χ' : Y →+ ℤ} (h : χ' ≠ χ) {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ') : projW R hv χ x = 0 := by
  have hx' : x ∈ otherWeights R v χ :=
    Submodule.mem_iSup_of_mem χ' (Submodule.mem_iSup_of_mem h hx)
  have := Submodule.projectionOnto_apply_of_mem_right (isCompl_otherWeights (R := R) hv χ) hx'
  simp [projW, this]

/-! ### `𝒜U⁻` and homogeneous components -/

namespace Modified

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X

variable (R) in
/-- `𝒜U⁻`: the `𝒜`-combinations of the monomials `F_w` in divided powers (the image of `𝒜f` under
`x ↦ x⁻`). -/
def aMinus : AddSubgroup (QuantumGroup R 𝕧) :=
  AddSubgroup.closure {x | ∃ (c : 𝕂) (w : List (I × ℕ)), IsLaurent c ∧ x = c • fPow R w}

variable (R) in
/-- The `𝒜`-combinations of the `F_w` of weight `χ`. -/
def aMinusW (χ : Y →+ ℤ) : AddSubgroup (QuantumGroup R 𝕧) :=
  AddSubgroup.closure {x | ∃ (c : 𝕂) (w : List (I × ℕ)), IsLaurent c ∧ -wtW R w = χ ∧
    x = c • fPow R w}

variable (R) in
/-- The `𝒜`-combinations of the `E_w` of weight `χ`. -/
def aPlusW (χ : Y →+ ℤ) : AddSubgroup (QuantumGroup R 𝕧) :=
  AddSubgroup.closure {x | ∃ (c : 𝕂) (w : List (I × ℕ)), IsLaurent c ∧ wtW R w = χ ∧
    x = c • ePow R w}

lemma isGen_of_mem_aMinusW {χ : Y →+ ℤ} {x : QuantumGroup R 𝕧} (hx : x ∈ aMinusW R χ) :
    IsGen R x χ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, hc, rfl, rfl⟩ := hx
    exact (isGen_fPow w).smul hc
  | zero => exact isGen_zero χ
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => rw [← neg_one_smul 𝕂]; exact hx.smul isLaurent_neg_one

lemma isGen_of_mem_aPlusW {χ : Y →+ ℤ} {x : QuantumGroup R 𝕧} (hx : x ∈ aPlusW R χ) :
    IsGen R x χ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, hc, rfl, rfl⟩ := hx
    exact (isGen_ePow w).smul hc
  | zero => exact isGen_zero χ
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => rw [← neg_one_smul 𝕂]; exact hx.smul isLaurent_neg_one

lemma projW_mem_aMinusW {x : QuantumGroup R 𝕧} (hx : x ∈ aMinus R) (χ : Y →+ ℤ) :
    projW R ratFunc_X_not_root χ x ∈ aMinusW R χ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, hc, rfl⟩ := hx
    rw [map_smul]
    by_cases h : -wtW R w = χ
    · rw [projW_of_mem _ (h ▸ fPow_mem w)]
      exact AddSubgroup.subset_closure ⟨c, w, hc, h, rfl⟩
    · rw [projW_of_mem_ne _ h (fPow_mem w), smul_zero]; exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

lemma projW_mem_aPlusW {x : QuantumGroup R 𝕧} (hx : x ∈ aPlus R) (χ : Y →+ ℤ) :
    projW R ratFunc_X_not_root χ x ∈ aPlusW R χ := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, hc, rfl⟩ := hx
    rw [map_smul]
    by_cases h : wtW R w = χ
    · rw [projW_of_mem _ (h ▸ ePow_mem w)]
      exact AddSubgroup.subset_closure ⟨c, w, hc, h, rfl⟩
    · rw [projW_of_mem_ne _ h (ePow_mem w), smul_zero]; exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

lemma isGen_of_mem_aMinus {x : QuantumGroup R 𝕧} (hx : x ∈ aMinus R) {χ : Y →+ ℤ}
    (hχ : x ∈ adWeightSpace R 𝕧 χ) : IsGen R x χ := by
  have := projW_mem_aMinusW hx χ
  rw [projW_of_mem _ hχ] at this
  exact isGen_of_mem_aMinusW this

lemma isGen_of_mem_aPlus {x : QuantumGroup R 𝕧} (hx : x ∈ aPlus R) {χ : Y →+ ℤ}
    (hχ : x ∈ adWeightSpace R 𝕧 χ) : IsGen R x χ := by
  have := projW_mem_aPlusW hx χ
  rw [projW_of_mem _ hχ] at this
  exact isGen_of_mem_aPlusW this

/-! ### Coordinates of weight vectors -/

/-- In a basis of weight vectors, a weight vector of weight `χ` only involves basis vectors of
weight `χ`. -/
lemma basis_repr_eq_zero_of_mem {ι : Type*} {S : Subalgebra 𝕂 (QuantumGroup R 𝕧)}
    (b : Module.Basis ι 𝕂 S) (w : ι → Y →+ ℤ)
    (hb : ∀ i, (b i : QuantumGroup R 𝕧) ∈ adWeightSpace R 𝕧 (w i)) {χ : Y →+ ℤ} (y : S)
    (hy : (y : QuantumGroup R 𝕧) ∈ adWeightSpace R 𝕧 χ) {i : ι} (hi : w i ≠ χ) :
    b.repr y i = 0 := by
  classical
  set A := (b.repr y).support
  have hsum : y = ∑ i' ∈ A, b.repr y i' • b i' := by
    conv_lhs => rw [← b.linearCombination_repr y]
    rfl
  have hproj : (y : QuantumGroup R 𝕧) =
      ∑ i' ∈ A, (if w i' = χ then b.repr y i' • (b i' : QuantumGroup R 𝕧) else 0) := by
    rw [← projW_of_mem ratFunc_X_not_root hy]
    conv_lhs => rw [hsum]
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    refine sum_congr rfl fun i' _ ↦ ?_
    rw [SetLike.val_smul, map_smul]
    split_ifs with h
    · rw [projW_of_mem _ (h ▸ hb i')]
    · rw [projW_of_mem_ne _ h (hb i'), smul_zero]
  have hz : y = ∑ i' ∈ A.filter (fun i' ↦ w i' = χ), b.repr y i' • b i' := by
    apply Subtype.ext
    rw [hproj, AddSubmonoidClass.coe_finsetSum, sum_filter]
    refine sum_congr rfl fun i' _ ↦ ?_
    split_ifs <;> simp
  rw [hz, map_sum, Finsupp.finsetSum_apply]
  refine sum_eq_zero fun i' hi' ↦ ?_
  have hne : i' ≠ i := by
    rintro rfl
    exact hi (mem_filter.1 hi').2
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hne.symm,
    smul_zero]

/-! ### Elements with `𝒜`-coordinates -/

variable (R) in
/-- The elements of `U̇` whose coordinates in a basis `B` lie in `𝒜`. -/
def laurentCoords {T : Type*} (B : Module.Basis T 𝕂 (Modified R 𝕧)) :
    AddSubgroup (Modified R 𝕧) where
  carrier := {x | ∀ t, IsLaurent (B.repr x t)}
  zero_mem' t := by simpa using isLaurent_zero
  add_mem' hx hy t := by simpa using (hx t).add (hy t)
  neg_mem' hx t := by simpa using (hx t).neg

lemma smul_mem_laurentCoords {T : Type*} {B : Module.Basis T 𝕂 (Modified R 𝕧)} {c : 𝕂}
    (hc : IsLaurent c) {x : Modified R 𝕧} (hx : x ∈ laurentCoords R B) :
    c • x ∈ laurentCoords R B := fun t ↦ by
  simpa using hc.mul (hx t)

lemma basis_mem_laurentCoords {T : Type*} (B : Module.Basis T 𝕂 (Modified R 𝕧)) (t : T) :
    B t ∈ laurentCoords R B := fun t' ↦ by
  classical
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  exacts [isLaurent_one, isLaurent_zero]

section ABasis

variable {ι κ : Type*} (bm : Module.Basis ι 𝕂 (Algebra.adjoin 𝕂 (Set.range (F R 𝕧))))
  (bp : Module.Basis κ 𝕂 (Algebra.adjoin 𝕂 (Set.range (E R 𝕧)))) (wm : ι → Y →+ ℤ)
  (wp : κ → Y →+ ℤ) (hm : ∀ i, (bm i : QuantumGroup R 𝕧) ∈ adWeightSpace R 𝕧 (-wm i))
  (hp : ∀ j, (bp j : QuantumGroup R 𝕧) ∈ adWeightSpace R 𝕧 (wp j))

include hm hp in
lemma triFun_mem_aForm (hbm : ∀ i, (bm i : QuantumGroup R 𝕧) ∈ aMinus R)
    (hbp : ∀ j, (bp j : QuantumGroup R 𝕧) ∈ aPlus R) (t : ι × (Y →+ ℤ) × κ) :
    triFun bm bp wm wp hm hp t ∈ aForm R :=
  ((isGen_of_mem_aMinus (hbm t.1) (hm t.1)).mul (isGen_of_mem_aPlus (hbp t.2.2) (hp t.2.2))).elt_mem
    (by abel) _

include hm hp in
lemma elt_fPow_ePow_mem_laurentCoords
    (hbmF : ∀ w i, IsLaurent (bm.repr ⟨fPow R w, fPow_mem_minus w⟩ i))
    (hbpE : ∀ w j, IsLaurent (bp.repr ⟨ePow R w, ePow_mem_plus w⟩ j))
    {w w' : List (I × ℕ)} {L l : Y →+ ℤ}
    (h : fPow R w * ePow R w' ∈ adWeightSpace R 𝕧 (L - l)) :
    elt L l _ h ∈ laurentCoords R (triangularBasis ratFunc_X_not_root bm bp wm wp hm hp) := by
  classical
  by_cases hχ : L - l = wtW R w' - wtW R w
  swap
  · rw [elt_congr (eq_zero_of_mem_adWeightSpace (Ne.symm hχ) (fPow_mul_ePow_mem w w') h) h
      (zero_mem _), elt_zero']
    exact zero_mem _
  set a := bm.repr ⟨fPow R w, fPow_mem_minus w⟩
  set b := bp.repr ⟨ePow R w', ePow_mem_plus w'⟩
  have ha : ∀ i, a i ≠ 0 → wm i = wtW R w := fun i hi ↦ by
    by_contra hne
    exact hi (basis_repr_eq_zero_of_mem bm (fun i ↦ -wm i) hm ⟨fPow R w, fPow_mem_minus w⟩
      (fPow_mem w) (fun h' ↦ hne (neg_injective h')))
  have hb : ∀ j, b j ≠ 0 → wp j = wtW R w' := fun j hj ↦ by
    by_contra hne
    exact hj (basis_repr_eq_zero_of_mem bp wp hp ⟨ePow R w', ePow_mem_plus w'⟩ (ePow_mem w') hne)
  have hF : fPow R w = ∑ i ∈ a.support, a i • (bm i : QuantumGroup R 𝕧) := by
    have h0 := congrArg Subtype.val (bm.linearCombination_repr ⟨fPow R w, fPow_mem_minus w⟩)
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul] at h0
    exact h0.symm
  have hE : ePow R w' = ∑ j ∈ b.support, b j • (bp j : QuantumGroup R 𝕧) := by
    have h0 := congrArg Subtype.val (bp.linearCombination_repr ⟨ePow R w', ePow_mem_plus w'⟩)
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul] at h0
    exact h0.symm
  let g : ι × κ → QuantumGroup R 𝕧 := fun p ↦
    (a p.1 * b p.2) • ((bm p.1 : QuantumGroup R 𝕧) * bp p.2)
  have hg : ∀ p, g p ∈ adWeightSpace R 𝕧 (L - l) := fun p ↦ by
    by_cases h0 : a p.1 * b p.2 = 0
    · simp only [g, h0, zero_smul]; exact zero_mem _
    · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h0
      refine Submodule.smul_mem _ _ ?_
      rw [hχ, ← ha p.1 h1, ← hb p.2 h2, sub_eq_neg_add]
      exact mul_mem_adWeightSpace (hm p.1) (hp p.2)
  have hprod : fPow R w * ePow R w' = ∑ p ∈ a.support ×ˢ b.support, g p := by
    rw [hF, hE, sum_mul_sum, sum_product]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
    simp only [g, smul_mul_smul_comm]
  rw [elt_congr hprod h (Submodule.sum_mem _ fun p _ ↦ hg p), elt_sum _ g hg]
  refine AddSubgroup.sum_mem _ fun p _ ↦ ?_
  by_cases h0 : a p.1 * b p.2 = 0
  · rw [elt_congr (by simp only [g, h0, zero_smul]) (hg p) (zero_mem _), elt_zero']
    exact zero_mem _
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h0
    have hmem := bm_mul_bp_mem bm bp wm wp hm hp p.1 (l + wp p.2) p.2
    have hmem' : (bm p.1 : QuantumGroup R 𝕧) * bp p.2 ∈ adWeightSpace R 𝕧 (L - l) := by
      rw [hχ, ← ha p.1 h1, ← hb p.2 h2, sub_eq_neg_add]
      exact mul_mem_adWeightSpace (hm p.1) (hp p.2)
    rw [elt_smul _ _ _ hmem']
    refine smul_mem_laurentCoords ((hbmF w p.1).mul (hbpE w' p.2)) ?_
    have e : elt L l _ hmem' = triangularBasis ratFunc_X_not_root bm bp wm wp hm hp
        (p.1, l + wp p.2, p.2) := by
      rw [triangularBasis_apply, triFun]
      refine elt_index ?_ ?_ rfl _ _
      · change L = l + wp p.2 - wm p.1
        rw [ha p.1 h1, hb p.2 h2, add_sub_assoc, ← hχ]; abel
      · change l = l + wp p.2 - wp p.2
        abel
    rw [e]
    exact basis_mem_laurentCoords _ _

include hm hp in
lemma mem_laurentCoords_of_mem_aForm
    (hbmF : ∀ w i, IsLaurent (bm.repr ⟨fPow R w, fPow_mem_minus w⟩ i))
    (hbpE : ∀ w j, IsLaurent (bp.repr ⟨ePow R w, ePow_mem_plus w⟩ j))
    {x : Modified R 𝕧} (hx : x ∈ aForm R) :
    x ∈ laurentCoords R (triangularBasis ratFunc_X_not_root bm bp wm wp hm hp) := by
  have hx' : x ∈ aFormFE R := by rw [← aForm_eq_aFormFE]; exact hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, w', L, l, h, rfl⟩ := hx
    exact elt_fPow_ePow_mem_laurentCoords bm bp wm wp hm hp hbmF hbpE h
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => rw [laurent_smul]; exact smul_mem_laurentCoords ⟨a, rfl⟩ hx

/-- **The triangular `𝒜`-basis of `𝒜U̇`** ([Lus] 23.2.2 (b)): let `(bᵢ)`, `(b'ⱼ)` be bases of `U⁻`,
`U⁺` consisting of weight vectors, with `bᵢ ∈ 𝒜U⁻`, `b'ⱼ ∈ 𝒜U⁺` and such that the monomials `F_w`,
`E_w` in divided powers have `𝒜`-coordinates (so that `(bᵢ)`, `(b'ⱼ)` are `𝒜`-bases of `𝒜U⁻`,
`𝒜U⁺`). Then the elements `bᵢ 1_λ b'ⱼ` (`λ ∈ X`) form an `𝒜`-basis of `𝒜U̇`. Lusztig takes
`bᵢ = b⁻`, `b'ⱼ = b'⁺` for an `𝒜`-basis `B` of `𝒜f`. -/
def aTriangularBasis (hbm : ∀ i, (bm i : QuantumGroup R 𝕧) ∈ aMinus R)
    (hbp : ∀ j, (bp j : QuantumGroup R 𝕧) ∈ aPlus R)
    (hbmF : ∀ w i, IsLaurent (bm.repr ⟨fPow R w, fPow_mem_minus w⟩ i))
    (hbpE : ∀ w j, IsLaurent (bp.repr ⟨ePow R w, ePow_mem_plus w⟩ j)) :
    Module.Basis (ι × (Y →+ ℤ) × κ) 𝒜 (aForm R).toSubmodule := by
  classical
  set B := triangularBasis ratFunc_X_not_root bm bp wm wp hm hp
  let f : ι × (Y →+ ℤ) × κ → (aForm R).toSubmodule := fun t ↦
    ⟨B t, by rw [triangularBasis_apply]; exact triFun_mem_aForm bm bp wm wp hm hp hbm hbp t⟩
  refine Module.Basis.mk (v := f) ?_ ?_
  · rw [linearIndependent_iff']
    intro s g hg t ht
    have h1 : ∑ t ∈ s, LusztigF.integralLaurentEval (g t) • B t = 0 := by
      have := congrArg Subtype.val hg
      simpa [f, laurent_smul] using this
    have h2 := linearIndependent_iff'.1 B.linearIndependent s _ h1 t ht
    exact LusztigF.integralLaurentEval_injective (by rw [h2, map_zero])
  · rintro ⟨x, hx⟩ -
    have hL := mem_laurentCoords_of_mem_aForm bm bp wm wp hm hp hbmF hbpE hx
    choose a ha using hL
    have hsum : (⟨x, hx⟩ : (aForm R).toSubmodule) =
        ∑ t ∈ (B.repr x).support, a t • f t := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, f, laurent_smul, ha]
      conv_lhs => rw [← B.linearCombination_repr x]
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun t _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

lemma aTriangularBasis_apply (hbm : ∀ i, (bm i : QuantumGroup R 𝕧) ∈ aMinus R)
    (hbp : ∀ j, (bp j : QuantumGroup R 𝕧) ∈ aPlus R)
    (hbmF : ∀ w i, IsLaurent (bm.repr ⟨fPow R w, fPow_mem_minus w⟩ i))
    (hbpE : ∀ w j, IsLaurent (bp.repr ⟨ePow R w, ePow_mem_plus w⟩ j)) (t : ι × (Y →+ ℤ) × κ) :
    (aTriangularBasis bm bp wm wp hm hp hbm hbp hbmF hbpE t : Modified R 𝕧) =
      triFun bm bp wm wp hm hp t := by
  simp [aTriangularBasis, triangularBasis_apply]

end ABasis

end Modified

end LieLean.QuantumGroup
