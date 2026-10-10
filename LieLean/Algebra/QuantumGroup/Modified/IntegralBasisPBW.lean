/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBW
import LieLean.Algebra.QuantumGroup.Modified.IntegralBasis

/-!
# A triangular `𝒜`-basis of `𝒜U̇` in simply-laced finite type

[Lus] 23.2.2 (b) takes an `𝒜`-basis of `𝒜f` as input (Lusztig uses the canonical basis). In
simply-laced finite type the integral PBW monomials of a reduced expression of `w₀` are such a
basis ([Lus] 41.1.7, `Modified.span_pbwDiv_longest_eq`), on `U⁺` and, through the Chevalley
involution, on `U⁻`. Here we check the hypotheses of `Modified.aTriangularBasis` for these bases
(`Modified.pbwPlusBasis`, `Modified.pbwMinusBasis`), which gives an explicit `𝒜`-basis of `𝒜U̇`
(`Modified.aTriangularBasisPBW`).

## Main results

* `Modified.pbwWt`, `Modified.pbwDiv_mem_adWeightSpace`: weights of the integral PBW monomials.
* `Modified.pbwPlusBasis`, `Modified.pbwMinusBasis`: `ℚ(v)`-bases of `U⁺`, `U⁻` consisting of
  integral PBW monomials (resp. their images under `ω`), simply-laced finite type.
* `Modified.aTriangularBasisPBW`, `Modified.aTriangularBasisPBW_apply`: the resulting `𝒜`-basis
  `ω(E_c) 1_λ E_{c'}` of `𝒜U̇`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.2.2, 41.1.7.
-/

open LieLean Finset

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

namespace Modified

attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

/-! ### Weights of the integral PBW monomials -/

variable (R) in
/-- The weight of `pbwDiv R ω c`. -/
def pbwWt : (ω : List I) → (Fin ω.length → ℕ) → Y →+ ℤ
  | [], _ => 0
  | i :: ω, c => c ⟨0, Nat.succ_pos _⟩ • R.root i + (pbwWt ω fun n ↦ c n.succ).comp (reflY R i)

lemma pbwDiv_mem_adWeightSpace (ω : List I) (c : Fin ω.length → ℕ) :
    pbwDiv R ω c ∈ adWeightSpace R 𝕧 (pbwWt R ω c) := by
  induction ω with
  | nil => simpa [CoxeterSystem.pbwDivMonomial, pbwWt] using one_mem_adWeightSpace
  | cons i ω ih =>
    rw [pbwDiv, CoxeterSystem.pbwDivMonomial_cons, pbwWt, Ta_apply]
    exact mul_mem_adWeightSpace (qDivPow_E_mem _ i _)
      ((braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i).map_mem_adWeightSpace (ih _))

/-! ### The basis of `U⁺` -/

lemma aPlus_le_plus {x : QuantumGroup R 𝕧} (hx : x ∈ aPlus R) :
    x ∈ Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, -, rfl⟩ := hx
    exact Subalgebra.smul_mem _ (ePow_mem_plus w) c
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

lemma span_laurent_le_span {ω : List I} {x : QuantumGroup R 𝕧}
    (hx : x ∈ Submodule.span 𝒜 (Set.range (pbwDiv R ω))) :
    x ∈ Submodule.span 𝕂 (Set.range (pbwDiv R ω)) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => rw [laurent_smul_U]; exact Submodule.smul_mem _ _ hx

/-- The `𝕂`-coordinates of an element of the `𝒜`-span of a linearly independent family lie in
`𝒜`. -/
lemma isLaurent_repr_of_mem_span {ι : Type*} {S : Subalgebra 𝕂 (QuantumGroup R 𝕧)}
    (b : Module.Basis ι 𝕂 S) {x : S}
    (hx : (x : QuantumGroup R 𝕧) ∈ Submodule.span 𝒜 (Set.range fun i ↦ (b i : QuantumGroup R 𝕧)))
    (i : ι) : IsLaurent (b.repr x i) := by
  classical
  have key : ∀ y : QuantumGroup R 𝕧,
      y ∈ Submodule.span 𝒜 (Set.range fun i ↦ (b i : QuantumGroup R 𝕧)) →
      ∃ hy : y ∈ S, ∀ i, IsLaurent (b.repr ⟨y, hy⟩ i) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      refine ⟨(b j).2, fun i ↦ ?_⟩
      rw [show (⟨(b j : QuantumGroup R 𝕧), (b j).2⟩ : S) = b j from rfl, b.repr_self,
        Finsupp.single_apply]
      split_ifs
      exacts [isLaurent_one, isLaurent_zero]
    | zero =>
      refine ⟨zero_mem _, fun i ↦ ?_⟩
      rw [show (⟨0, zero_mem _⟩ : S) = 0 from rfl, map_zero, Finsupp.zero_apply]
      exact isLaurent_zero
    | add y z _ _ hy hz =>
      obtain ⟨hy, hy'⟩ := hy
      obtain ⟨hz, hz'⟩ := hz
      refine ⟨add_mem hy hz, fun i ↦ ?_⟩
      rw [show (⟨y + z, add_mem hy hz⟩ : S) = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl, map_add,
        Finsupp.add_apply]
      exact (hy' i).add (hz' i)
    | smul a y _ hy =>
      obtain ⟨hy, hy'⟩ := hy
      refine ⟨by rw [laurent_smul_U]; exact S.smul_mem hy _, fun i ↦ ?_⟩
      rw [show (⟨a • y, by rw [laurent_smul_U]; exact S.smul_mem hy _⟩ : S) =
        LusztigF.integralLaurentEval a • ⟨y, hy⟩ from rfl, map_smul, Finsupp.smul_apply,
        smul_eq_mul]
      exact (show IsLaurent _ from ⟨a, rfl⟩).mul (hy' i)
  obtain ⟨_, h⟩ := key _ hx
  exact h i

variable (hSL : D.cartanMatrix.IsSimplyLaced) {W : Type*} [Group W] [Finite W]
  (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
  (hw₀ : cs.wordProd w = cs.longestElement)

omit [Finite W] in
include hSL hw in
lemma pbwDiv_mem_plus (c : Fin w.length → ℕ) :
    pbwDiv R w c ∈ Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) :=
  aPlus_le_plus (by simpa using pbwDiv_mem_aPlus (R := R) hSL w [] (by simpa using hw) c)

include hSL hw hw₀ in
lemma plus_le_span_pbwDiv :
    (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))).toSubmodule ≤
      Submodule.span 𝕂 (Set.range (pbwDiv R w)) := by
  let S := Submodule.span 𝕂 (Set.range (pbwDiv R w))
  have h1 : (1 : QuantumGroup R 𝕧) ∈ S :=
    span_laurent_le_span (CoxeterSystem.one_mem_pbwDivSpan (Ta R) (Ed R) Ed_zero w)
  intro x hx
  have hmul : ∀ y ∈ S, x * y ∈ S := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨c, rfl⟩ := hy
        have := qDivPow_E_mul_mem_span_pbwDiv (R := R) hSL cs hw
          (hw₀ ▸ cs.isLeftDescent_longestElement i) 1
          (Submodule.subset_span ⟨c, rfl⟩)
        rw [A2Integral.qDivPow_one'] at this
        exact span_laurent_le_span this
      | zero => rw [mul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    | algebraMap a =>
      intro y hy
      rw [← Algebra.smul_def]
      exact S.smul_mem a hy
    | add x z _ _ hx hz =>
      intro y hy; rw [add_mul]; exact add_mem (hx y hy) (hz y hy)
    | mul x z _ _ hx hz =>
      intro y hy; rw [mul_assoc]; exact hx _ (hz y hy)
  simpa using hmul 1 h1

include hSL hw hw₀ in
/-- **The integral PBW basis of `U⁺`** (simply-laced finite type): the divided-power PBW monomials
of a reduced expression of `w₀`. -/
def pbwPlusBasis :
    Module.Basis (Fin w.length → ℕ) 𝕂 (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))) :=
  let v : (Fin w.length → ℕ) → Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) :=
    fun c ↦ ⟨pbwDiv R w c, pbwDiv_mem_plus hSL cs hw c⟩
  Module.Basis.mk (v := v)
    (by
      refine LinearIndependent.of_comp
        (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))).toSubmodule.subtype ?_
      have hli := linearIndependent_pbwMonomial_of_isReduced (R := R) ratFunc_X_not_root
        (simplyLaced_mul_le_three hSL) hw
      have hu := hli.units_smul fun c ↦ Units.mk0
        (∏ t : Fin w.length, (qFactorial (𝕧 ^ D.d w[t]) (c t))⁻¹)
        (prod_ne_zero_iff.2 fun t _ ↦ inv_ne_zero (qFactorial_vd_ne_zero _ _))
      convert hu using 1
      ext c
      simp [v, pbwDiv_eq_smul])
    (by
      rintro ⟨x, hx⟩ -
      have hx' := plus_le_span_pbwDiv (R := R) hSL cs hw hw₀ hx
      have hmap : (Submodule.span 𝕂 (Set.range v)).map
          (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))).toSubmodule.subtype =
            Submodule.span 𝕂 (Set.range (pbwDiv R w)) := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      rw [← hmap] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rwa [show (⟨x, hx⟩ : Algebra.adjoin 𝕂 (Set.range (E R 𝕧))) = y from
        Subtype.ext hyx.symm])

lemma pbwPlusBasis_apply (c : Fin w.length → ℕ) :
    (pbwPlusBasis (R := R) hSL cs hw hw₀ c : QuantumGroup R 𝕧) = pbwDiv R w c := by
  simp [pbwPlusBasis]

/-! ### The basis of `U⁻` -/

lemma map_chevalley_plus :
    (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))).map (chevalleyEquiv R 𝕧 : _ →ₐ[𝕂] _) =
      Algebra.adjoin 𝕂 (Set.range (F R 𝕧)) := by
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  congr 2
  funext i
  exact chevalley_E R 𝕧 i

variable (R) in
/-- The Chevalley involution `U⁺ ≃ U⁻`. -/
def chevalleyPlusMinus :
    Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) ≃ₗ[𝕂] Algebra.adjoin 𝕂 (Set.range (F R 𝕧)) :=
  (((chevalleyEquiv R 𝕧).subalgebraMap _).trans
    (Subalgebra.equivOfEq _ _ map_chevalley_plus)).toLinearEquiv

lemma chevalleyPlusMinus_apply (x : Algebra.adjoin 𝕂 (Set.range (E R 𝕧))) :
    (chevalleyPlusMinus R x : QuantumGroup R 𝕧) = chevalley R 𝕧 x := rfl

include hSL hw hw₀ in
/-- **The integral PBW basis of `U⁻`**: the images of `pbwPlusBasis` under the Chevalley
involution. -/
def pbwMinusBasis :
    Module.Basis (Fin w.length → ℕ) 𝕂 (Algebra.adjoin 𝕂 (Set.range (F R 𝕧))) :=
  (pbwPlusBasis hSL cs hw hw₀).map (chevalleyPlusMinus R)

lemma pbwMinusBasis_apply (c : Fin w.length → ℕ) :
    (pbwMinusBasis (R := R) hSL cs hw hw₀ c : QuantumGroup R 𝕧) = chevalley R 𝕧 (pbwDiv R w c) := by
  rw [pbwMinusBasis, Module.Basis.map_apply, chevalleyPlusMinus_apply, pbwPlusBasis_apply]

lemma chevalley_mem_aMinus {x : QuantumGroup R 𝕧} (hx : x ∈ aPlus R) :
    chevalley R 𝕧 x ∈ aMinus R := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, hc, rfl⟩ := hx
    rw [map_smul, chevalley_ePow]
    exact AddSubgroup.subset_closure ⟨c, w, hc, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

include hSL hw hw₀ in
/-- **A triangular `𝒜`-basis of `𝒜U̇`** in simply-laced finite type ([Lus] 23.2.2 (b) with the
integral PBW bases of [Lus] 41.1.7): for a reduced expression of `w₀`, the elements
`ω(E_c) 1_λ E_{c'}` (`E_c` the integral PBW monomials, `ω` the Chevalley involution) form an
`𝒜`-basis of `𝒜U̇`. -/
def aTriangularBasisPBW :
    Module.Basis ((Fin w.length → ℕ) × (Y →+ ℤ) × (Fin w.length → ℕ)) 𝒜
      (aForm R).toSubmodule :=
  have hp : ∀ c, (pbwPlusBasis (R := R) hSL cs hw hw₀ c : QuantumGroup R 𝕧) ∈
      adWeightSpace R 𝕧 (pbwWt R w c) := fun c ↦ by
    rw [pbwPlusBasis_apply]; exact pbwDiv_mem_adWeightSpace w c
  have hm : ∀ c, (pbwMinusBasis (R := R) hSL cs hw hw₀ c : QuantumGroup R 𝕧) ∈
      adWeightSpace R 𝕧 (-pbwWt R w c) := fun c ↦ by
    rw [pbwMinusBasis_apply, ← wt_omegaAut (R := R)]
    exact map_mem_adWeightSpace (omegaAut R) (pbwDiv_mem_adWeightSpace w c)
  have haP : ∀ c, pbwDiv R w c ∈ aPlus R := fun c ↦ by
    simpa using pbwDiv_mem_aPlus (R := R) hSL w [] (by simpa using hw) c
  have hspan : ∀ x ∈ aPlus R, x ∈ Submodule.span 𝒜 (Set.range fun c ↦
      (pbwPlusBasis (R := R) hSL cs hw hw₀ c : QuantumGroup R 𝕧)) := fun x hx ↦ by
    have e : (Set.range fun c ↦ (pbwPlusBasis (R := R) hSL cs hw hw₀ c : QuantumGroup R 𝕧)) =
        Set.range (pbwDiv R w) := by
      congr 1
      funext c
      exact pbwPlusBasis_apply (R := R) hSL cs hw hw₀ c
    rw [e]
    have hx' : x ∈ (aPlus R : Set (QuantumGroup R 𝕧)) := hx
    rw [← coe_span_pbwDiv_longest (R := R) hSL cs hw hw₀] at hx'
    exact hx'
  aTriangularBasis (pbwMinusBasis hSL cs hw hw₀) (pbwPlusBasis hSL cs hw hw₀) (pbwWt R w)
    (pbwWt R w) hm hp
    (fun c ↦ by rw [pbwMinusBasis_apply]; exact chevalley_mem_aMinus (haP c))
    (fun c ↦ by rw [pbwPlusBasis_apply]; exact haP c)
    (fun w' c ↦ by
      rw [pbwMinusBasis, Module.Basis.map_repr, LinearEquiv.trans_apply]
      have e : (chevalleyPlusMinus R).symm ⟨fPow R w', fPow_mem_minus w'⟩ =
          ⟨ePow R w', ePow_mem_plus w'⟩ := by
        rw [LinearEquiv.symm_apply_eq]
        apply Subtype.ext
        rw [chevalleyPlusMinus_apply]
        exact (chevalley_ePow w').symm
      rw [e]
      exact isLaurent_repr_of_mem_span _ (hspan _ (ePow_mem_aPlus w')) c)
    (fun w' c ↦ isLaurent_repr_of_mem_span _ (hspan _ (ePow_mem_aPlus w')) c)

lemma aTriangularBasisPBW_apply (t : (Fin w.length → ℕ) × (Y →+ ℤ) × (Fin w.length → ℕ)) :
    (aTriangularBasisPBW (R := R) hSL cs hw hw₀ t : Modified R 𝕧) =
      elt (t.2.1 - pbwWt R w t.1) (t.2.1 - pbwWt R w t.2.2)
        (chevalley R 𝕧 (pbwDiv R w t.1) * pbwDiv R w t.2.2) (by
          have := mul_mem_adWeightSpace
            (map_mem_adWeightSpace (omegaAut R) (pbwDiv_mem_adWeightSpace (R := R) w t.1))
            (pbwDiv_mem_adWeightSpace (R := R) w t.2.2)
          rw [wt_omegaAut] at this
          convert this using 2 <;> first | rfl | abel) := by
  rw [aTriangularBasisPBW, aTriangularBasis_apply, triFun]
  exact elt_congr (by rw [pbwMinusBasis_apply, pbwPlusBasis_apply]) _ _

end Modified

end LieLean.QuantumGroup
