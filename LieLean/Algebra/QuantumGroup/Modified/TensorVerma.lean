/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Faithful
import LieLean.Algebra.QuantumGroup.Modified.FormRight
import LieLean.Algebra.QuantumGroup.Modified.LeftActOne

/-!
# `U̇ 1_ζ` and tensor products of Verma modules

Let `Λ, Λ' ∈ X` and `ζ = Λ' - Λ`. The `U`-module `ʷM_Λ ⊗ M_{Λ'}` (`ʷ` the twist by the Chevalley
involution, `QuantumGroup.ChevalleyTwist`) contains the vector `ξ ⊗ η` of weight `ζ`, `ξ` and
`η` the highest weight vectors. **[Lus] 23.3.1 (c)**: `u 1_ζ ↦ u (ξ ⊗ η)` is a linear isomorphism
`U̇ 1_ζ ≃ ʷM_Λ ⊗ M_{Λ'}`.

## Main definitions and results

* `QuantumGroup.Modified.weightAct`: for a vector `m` of weight `ζ` of a `U`-module, the map
  `U̇ → M`, `π_{λ',ζ}(u) ↦ u m`, zero on the components `ₗU_λ''` with `λ'' ≠ ζ` (cf. [Lus]
  23.1.4); `weightAct_leftActOne`: `u 1_ζ ↦ u m`.
* `QuantumGroup.Modified.smul_vermaTensorHwv_eq_zero_iff`,
  `surjective_smul_vermaTensorHwv`, `vermaTensorEquiv`: [Lus] 23.3.1 (c).
* `LinearMap.bijective_of_sub_mem_filtration`: a linear endomorphism that is the identity on the
  associated graded of an exhaustive filtration starting at `0` is bijective.

## Proof

The elements `y⁻ x⁺ 1_ζ` (`x, y ∈ f`) span `U̇ 1_ζ` (triangular decomposition). Since `Eᵢ η = 0`,
`x⁺ (ξ ⊗ η) = x⁺ξ ⊗ η`, and `y⁻ (a ⊗ η) = a ⊗ y⁻η` modulo the span of the `a' ⊗ y'⁻η` with
`y'` of smaller degree. Hence `y ⊗ x ↦ y⁻ x⁺ (ξ ⊗ η)` differs from the isomorphism
`y ⊗ x ↦ x⁺ξ ⊗ y⁻η`, `f ⊗ f ≃ ʷM_Λ ⊗ M_{Λ'}`, by a map lowering the degree of the first factor,
and is bijective. This is the argument of [Lus] 23.3.1 (b), organized as an induction on the
degree; the injectivity of `U̇ 1_ζ → f ⊗ f` used in the source is not needed, since the action
of `U̇` on vectors of weight `ζ` (`weightAct`) shows that `u 1_ζ = 0` implies `u (ξ ⊗ η) = 0`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.4, 23.3.1.
-/

open LieLean TensorProduct

noncomputable section

/-- A linear endomorphism `S` of `V` is bijective if `V` has an exhaustive filtration
`G 0 = 0 ⊆ G 1 ⊆ ⋯` with `S z - z ∈ G d` for `z ∈ G (d + 1)`. -/
theorem LinearMap.bijective_of_sub_mem_filtration {R V : Type*} [Ring R] [AddCommGroup V]
    [Module R V] (S : V →ₗ[R] V) (G : ℕ → Submodule R V) (h0 : G 0 = ⊥)
    (htop : ∀ z, ∃ d, z ∈ G d) (hS : ∀ d, ∀ z ∈ G (d + 1), S z - z ∈ G d) :
    Function.Bijective S := by
  have hinj : ∀ d, ∀ z ∈ G d, S z = 0 → z = 0 := by
    intro d
    induction d with
    | zero => intro z hz _; rw [h0] at hz; exact (Submodule.mem_bot R).1 hz
    | succ d ih =>
      intro z hz hSz
      refine ih z ?_ hSz
      have h := hS d z hz
      rw [hSz, zero_sub] at h
      exact neg_mem_iff.1 h
  have hsurj : ∀ d, ∀ w ∈ G d, ∃ u, S u = w := by
    intro d
    induction d with
    | zero => intro w hw; rw [h0] at hw; exact ⟨0, by rw [map_zero, (Submodule.mem_bot R).1 hw]⟩
    | succ d ih =>
      intro w hw
      obtain ⟨u, hu⟩ := ih _ (hS d w hw)
      exact ⟨w - u, by rw [map_sub, hu, sub_sub_cancel]⟩
  refine ⟨(injective_iff_map_eq_zero S).2 fun z hz ↦ ?_, fun w ↦ ?_⟩
  · obtain ⟨d, hd⟩ := htop z
    exact hinj d z hd hz
  · obtain ⟨d, hd⟩ := htop w
    exact hsurj d w hd

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

namespace Modified

attribute [local instance] decEqIdx

/-! ### The action of `U̇` on weight vectors -/

section WeightAct

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-- `U_χ M^ζ ⊆ M^{χ+ζ}`. -/
lemma smul_mem_weightSpace_of_mem_adWeightSpace {χ ζ : Y →+ ℤ} {u : QuantumGroup R v} {m : M}
    (hu : u ∈ adWeightSpace R v χ) (hm : m ∈ weightSpace R v M ζ) :
    u • m ∈ weightSpace R v M (χ + ζ) := fun μ ↦ by
  rw [← mul_smul, hu μ, smul_assoc, mul_smul, hm μ, smul_comm u, smul_smul,
    AddMonoidHom.add_apply, zpow_add₀ (NeZero.ne v)]

/-- The relations `N(λ', ζ)` kill the vectors of weight `ζ`. -/
lemma modRel_smul_eq_zero {L ζ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M ζ)
    {x : QuantumGroup R v} (hx : x ∈ modRel R v L ζ) : x • m = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · have hum := smul_mem_weightSpace_of_mem_adWeightSpace hu hm
      rw [sub_add_cancel] at hum
      rw [mul_smul, sub_smul, hum μ, algebraMap_smul, sub_self]
    · rw [mul_smul, sub_smul, hm μ, algebraMap_smul, sub_self, smul_zero]
  | zero => rw [zero_smul]
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_assoc, hx, smul_zero]

open scoped Classical in
variable (R) in
/-- `π_{λ',λ''}(u) ↦ u m` on the component `ₗU_λ''` if `λ'' = ζ`, zero otherwise. -/
def weightActComp (ζ : Y →+ ℤ) (m : M) (hm : m ∈ weightSpace R v M ζ)
    (p : (Y →+ ℤ) × (Y →+ ℤ)) : Comp R v p →ₗ[k] M :=
  if h : p.2 = ζ then
    Submodule.liftQ _ ((LinearMap.id.smulRight m) ∘ₗ (adWeightSpace R v (p.1 - p.2)).subtype)
      fun x hx ↦ LinearMap.mem_ker.2 (by
        have hx' : x.1 ∈ modRel R v p.1 p.2 := hx
        subst h
        exact modRel_smul_eq_zero hm hx')
  else 0

variable (R) in
/-- **The action of `U̇` on a vector `m` of weight `ζ`** (cf. [Lus] 23.1.4): `π_{λ',ζ}(u) ↦ u m`,
zero on the components `ₗU_λ''` with `λ'' ≠ ζ`. -/
def weightAct (ζ : Y →+ ℤ) (m : M) (hm : m ∈ weightSpace R v M ζ) : Modified R v →ₗ[k] M :=
  DirectSum.toModule k _ _ (weightActComp R ζ m hm)

open scoped Classical in
lemma weightAct_elt (ζ : Y →+ ℤ) (m : M) (hm : m ∈ weightSpace R v M ζ) (L l : Y →+ ℤ)
    {u : QuantumGroup R v} (hu : u ∈ adWeightSpace R v (L - l)) :
    weightAct R ζ m hm (elt L l u hu) = if l = ζ then u • m else 0 := by
  rw [weightAct, elt, DirectSum.toModule_lof]
  by_cases h : l = ζ
  · subst h
    simp only [weightActComp, Comp.mk, ↓reduceDIte, ↓reduceIte]
    rfl
  · simp [weightActComp, h]

/-- `u 1_ζ ↦ u m`. -/
theorem weightAct_leftActOne (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (ζ : Y →+ ℤ) (m : M)
    (hm : m ∈ weightSpace R v M ζ) (u : QuantumGroup R v) :
    weightAct R ζ m hm (leftActOne R hv ζ u) = u • m := by
  induction u using induction_adWeightSpace with
  | h0 => rw [map_zero, map_zero, zero_smul]
  | hadd a b ha hb => rw [map_add, map_add, ha, hb, add_smul]
  | hhom χ u hu => rw [leftActOne_eq_elt hv hu, weightAct_elt]; simp

end WeightAct

/-- `(u K_μ) 1_ζ = v^{⟨μ,ζ⟩} u 1_ζ`. -/
lemma leftActOne_mul_K (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (ζ : Y →+ ℤ) (u : QuantumGroup R v)
    (μ : Y) : leftActOne R hv ζ (u * K R v μ) = v ^ ζ μ • leftActOne R hv ζ u := by
  rw [leftActOne_apply, leftAct_mul, ← leftActOne_apply, leftActOne_K, map_smul,
    leftActOne_apply]

/-! ### [Lus] 23.3.1 (c) -/

section TensorVerma

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (Λ Λ' : Y →+ ℤ)

local notation "fQ" => LusztigF k I ⧸ serreSubmodule D v

variable (R v) in
/-- The vector `ξ ⊗ η` of `ʷM_Λ ⊗ M_{Λ'}`, `ξ` and `η` the highest weight vectors. -/
def vermaTensorHwv :
    TensorModule k (ChevalleyTwist R v (VermaModule R v Λ)) (VermaModule R v Λ') :=
  TensorModule.mk _ _ (ChevalleyTwist.toTwist R v _ (VermaModule.hwv R v Λ) ⊗ₜ[k]
    VermaModule.hwv R v Λ')

/-- `ξ ⊗ η` has weight `Λ' - Λ`. -/
lemma vermaTensorHwv_mem_weightSpace :
    vermaTensorHwv R v Λ Λ' ∈ weightSpace R v _ (Λ' - Λ) := by
  have hξ : ChevalleyTwist.toTwist R v _ (VermaModule.hwv R v Λ) ∈
      weightSpace R v (ChevalleyTwist R v (VermaModule R v Λ)) (-Λ) := fun μ ↦ by
    rw [ChevalleyTwist.smul_toTwist, chevalley_K, VermaModule.K_smul_hwv, LinearEquiv.map_smul,
      map_neg, AddMonoidHom.neg_apply]
  have h := TensorModule.tmul_mem_weightSpace hξ (VermaModule.hwv_mem_weightSpace (R := R)
    (v := v) (Λ := Λ'))
  rwa [neg_add_eq_sub] at h

/-- `x⁺ (a ⊗ η) = x⁺ a ⊗ η`, since `Eᵢ η = 0`. -/
lemma plusHom_smul_tmul_hwv {M₁ : Type*} [AddCommGroup M₁] [Module k M₁]
    [Module (QuantumGroup R v) M₁] [IsScalarTower k (QuantumGroup R v) M₁]
    (x : LusztigF k I) (a : M₁) :
    plusHom R v x • TensorModule.mk M₁ (VermaModule R v Λ') (a ⊗ₜ[k] VermaModule.hwv R v Λ') =
      TensorModule.mk _ _ ((plusHom R v x • a) ⊗ₜ[k] VermaModule.hwv R v Λ') := by
  induction x using FreeAlgebra.induction generalizing a with
  | grade0 c =>
    rw [AlgHom.commutes, algebraMap_smul, algebraMap_smul, ← map_smul, smul_tmul']
  | grade1 i =>
    rw [← LusztigF.θ, plusHom_θ, TensorModule.E_smul_tmul, VermaModule.E_smul_hwv, tmul_zero,
      add_zero]
  | mul a b ha hb => rw [_root_.map_mul, mul_smul, hb, ha, mul_smul]
  | add a b ha hb => rw [map_add, add_smul, ha, hb, add_smul, add_tmul, map_add]

/-! #### The filtration by degree -/

variable (k I) in
/-- The span of the monomials of length `< d` in `'f`. -/
def degSpan (d : ℕ) : Submodule k (LusztigF k I) :=
  Submodule.span k (LusztigF.monomial k '' {w | w.length < d})

omit [DecidableEq I] in
lemma monomial_mem_degSpan {w : List I} {d : ℕ} (h : w.length < d) :
    LusztigF.monomial k w ∈ degSpan k I d :=
  Submodule.subset_span ⟨w, h, rfl⟩

omit [DecidableEq I] in
lemma degSpan_mono {d d' : ℕ} (h : d ≤ d') : degSpan k I d ≤ degSpan k I d' :=
  Submodule.span_mono (Set.image_mono fun _ hw ↦ lt_of_lt_of_le hw h)

omit [DecidableEq I] in
lemma degSpan_zero : degSpan k I 0 = ⊥ := by
  simp [degSpan]

omit [DecidableEq I] in
lemma exists_mem_degSpan (y : LusztigF k I) : ∃ d, y ∈ degSpan k I d := by
  have hy : y ∈ Submodule.span k (Set.range (LusztigF.monomial k (I := I))) := by
    rw [LusztigF.span_monomial]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact ⟨w.length + 1, monomial_mem_degSpan (Nat.lt_succ_self _)⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd⟩ := hy
    obtain ⟨d', hd'⟩ := hz
    exact ⟨max d d', add_mem (degSpan_mono (le_max_left _ _) hd)
      (degSpan_mono (le_max_right _ _) hd')⟩
  | smul c y _ hy =>
    obtain ⟨d, hd⟩ := hy
    exact ⟨d, Submodule.smul_mem _ c hd⟩

omit [DecidableEq I] in
lemma θ_mul_mem_degSpan (i : I) {d : ℕ} {y : LusztigF k I} (hy : y ∈ degSpan k I d) :
    LusztigF.θ k i * y ∈ degSpan k I (d + 1) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [← LusztigF.monomial_cons]
    exact monomial_mem_degSpan (by simpa using hw)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

variable (R v) in
/-- `{y⁻ η | y ∈ 'f of degree < d}` in `M_{Λ'}`. -/
def vermaDegSpan (d : ℕ) : Submodule k (VermaModule R v Λ') :=
  (degSpan k I d).map (VermaModule.toVerma R v Λ')

omit [NeZero v] in
lemma vermaDegSpan_mono {d d' : ℕ} (h : d ≤ d') :
    vermaDegSpan R v Λ' d ≤ vermaDegSpan R v Λ' d' :=
  Submodule.map_mono (degSpan_mono h)

lemma K_smul_mem_vermaDegSpan (μ : Y) {d : ℕ} {b : VermaModule R v Λ'}
    (hb : b ∈ vermaDegSpan R v Λ' d) : K R v μ • b ∈ vermaDegSpan R v Λ' d := by
  obtain ⟨y, hy, rfl⟩ := hb
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [VermaModule.toVerma_mem_weightSpace (LusztigF.monomial_mem_weightSpace w) μ]
    exact Submodule.smul_mem _ _ ⟨_, monomial_mem_degSpan hw, rfl⟩
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, smul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ c hy

omit [NeZero v] in
lemma F_smul_toVerma (i : I) (y : LusztigF k I) :
    F R v i • VermaModule.toVerma R v Λ' y = VermaModule.toVerma R v Λ' (LusztigF.θ k i * y) := by
  rw [VermaModule.toVerma_apply, VermaModule.toVerma_apply, _root_.map_mul, minusHom_θ, mul_smul]

omit [NeZero v] in
lemma F_smul_mem_vermaDegSpan (i : I) {d : ℕ} {b : VermaModule R v Λ'}
    (hb : b ∈ vermaDegSpan R v Λ' d) : F R v i • b ∈ vermaDegSpan R v Λ' (d + 1) := by
  obtain ⟨y, hy, rfl⟩ := hb
  rw [F_smul_toVerma]
  exact ⟨_, θ_mul_mem_degSpan i hy, rfl⟩

variable (M₁ : Type*) [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁] in
/-- The span of the `a ⊗ b` with `b ∈ vermaDegSpan d`. -/
def tensorDegSpan (Λ' : Y →+ ℤ) (d : ℕ) :
    Submodule k (TensorModule k M₁ (VermaModule R v Λ')) :=
  Submodule.map₂ ((TensorProduct.mk k M₁ (VermaModule R v Λ')).compr₂
    (TensorModule.mk M₁ (VermaModule R v Λ')).toLinearMap) ⊤ (vermaDegSpan R v Λ' d)

section TensorDegSpan

variable {M₁ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]

omit [NeZero v] [Module (QuantumGroup R v) M₁] [IsScalarTower k (QuantumGroup R v) M₁] in
lemma tmul_mem_tensorDegSpan (a : M₁) {d : ℕ} {b : VermaModule R v Λ'}
    (hb : b ∈ vermaDegSpan R v Λ' d) :
    TensorModule.mk M₁ (VermaModule R v Λ') (a ⊗ₜ[k] b) ∈ tensorDegSpan M₁ Λ' d :=
  Submodule.apply_mem_map₂ _ Submodule.mem_top hb

omit [NeZero v] [Module (QuantumGroup R v) M₁] [IsScalarTower k (QuantumGroup R v) M₁] in
lemma tensorDegSpan_mono {d d' : ℕ} (h : d ≤ d') :
    tensorDegSpan (R := R) (v := v) M₁ Λ' d ≤ tensorDegSpan M₁ Λ' d' :=
  Submodule.map₂_le_map₂_right (vermaDegSpan_mono Λ' h)

lemma F_smul_mem_tensorDegSpan (i : I) {d : ℕ}
    {z : TensorModule k M₁ (VermaModule R v Λ')} (hz : z ∈ tensorDegSpan M₁ Λ' d) :
    F R v i • z ∈ tensorDegSpan M₁ Λ' (d + 1) := by
  have h : tensorDegSpan (R := R) (v := v) M₁ Λ' d ≤ (tensorDegSpan M₁ Λ' (d + 1)).comap
      (DistribSMul.toLinearMap k _ (F R v i)) := by
    refine Submodule.map₂_le.2 fun a _ b hb ↦ ?_
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
      Submodule.mem_comap, DistribSMul.toLinearMap_apply]
    rw [TensorModule.F_smul_tmul, map_add]
    exact add_mem (tmul_mem_tensorDegSpan Λ' _ (vermaDegSpan_mono Λ' (Nat.le_succ d)
      (K_smul_mem_vermaDegSpan Λ' _ hb))) (tmul_mem_tensorDegSpan Λ' _
        (F_smul_mem_vermaDegSpan Λ' i hb))
  exact h hz

/-- `y⁻ (a ⊗ η) = a ⊗ y⁻η` modulo `tensorDegSpan (length w)`, for `y = θ_w`. -/
lemma minusHom_monomial_smul_tmul_hwv_sub_mem (w : List I) (a : M₁) :
    minusHom R v (LusztigF.monomial k w) •
        TensorModule.mk M₁ (VermaModule R v Λ') (a ⊗ₜ[k] VermaModule.hwv R v Λ') -
      TensorModule.mk M₁ (VermaModule R v Λ')
        (a ⊗ₜ[k] VermaModule.toVerma R v Λ' (LusztigF.monomial k w)) ∈
      tensorDegSpan M₁ Λ' w.length := by
  induction w with
  | nil =>
    rw [LusztigF.monomial_nil, _root_.map_one, one_smul, VermaModule.toVerma_apply,
      _root_.map_one, one_smul, sub_self]
    exact zero_mem _
  | cons i w ih =>
    set b := VermaModule.toVerma R v Λ' (LusztigF.monomial k w)
    have hb : b ∈ vermaDegSpan R v Λ' (w.length + 1) :=
      ⟨_, monomial_mem_degSpan (Nat.lt_succ_self _), rfl⟩
    have e : minusHom R v (LusztigF.monomial k (i :: w)) •
          TensorModule.mk M₁ (VermaModule R v Λ') (a ⊗ₜ[k] VermaModule.hwv R v Λ') -
        TensorModule.mk M₁ (VermaModule R v Λ')
          (a ⊗ₜ[k] VermaModule.toVerma R v Λ' (LusztigF.monomial k (i :: w))) =
        F R v i • (minusHom R v (LusztigF.monomial k w) •
          TensorModule.mk M₁ (VermaModule R v Λ') (a ⊗ₜ[k] VermaModule.hwv R v Λ') -
          TensorModule.mk M₁ (VermaModule R v Λ') (a ⊗ₜ[k] b)) +
        TensorModule.mk M₁ (VermaModule R v Λ')
          ((F R v i • a) ⊗ₜ[k] (K R v (-ktilde R i) • b)) := by
      rw [smul_sub, TensorModule.F_smul_tmul, LusztigF.monomial_cons, _root_.map_mul, minusHom_θ,
        mul_smul, F_smul_toVerma, ← LusztigF.monomial_cons, map_add]
      abel
    rw [e, List.length_cons]
    exact add_mem (F_smul_mem_tensorDegSpan Λ' i ih)
      (tmul_mem_tensorDegSpan Λ' _ (K_smul_mem_vermaDegSpan Λ' _ hb))

end TensorDegSpan

/-! #### The maps `f ⊗ f → ʷM_Λ ⊗ M_{Λ'}` -/

variable (R) in
/-- `[y] ↦ y⁻`, `'f ⧸ J → U`. -/
def minusQ : fQ →ₗ[k] QuantumGroup R v :=
  (serreSubmodule D v).liftQ (minusHom R v).toLinearMap fun y hy ↦
    LinearMap.mem_ker.2 ((minusHom_eq_zero_iff R v hv' y).2 (mem_serreSubmodule.1 hy))

variable (R) in
/-- `[x] ↦ x⁺`, `'f ⧸ J → U`. -/
def plusQ : fQ →ₗ[k] QuantumGroup R v :=
  (serreSubmodule D v).liftQ (plusHom R v).toLinearMap fun y hy ↦
    LinearMap.mem_ker.2 ((plusHom_eq_zero_iff R v hv' y).2 (mem_serreSubmodule.1 hy))

variable (R) in
/-- `[y] ⊗ [x] ↦ y⁻ x⁺`, `f ⊗ f → U`. -/
def triMul : fQ ⊗[k] fQ →ₗ[k] QuantumGroup R v :=
  TensorProduct.lift ((LinearMap.mul k (QuantumGroup R v)).compl₁₂ (minusQ R hv') (plusQ R hv'))

lemma triMul_tmul (y x : LusztigF k I) :
    triMul R hv' (Submodule.Quotient.mk y ⊗ₜ Submodule.Quotient.mk x) =
      minusHom R v y * plusHom R v x :=
  rfl

/-- Every `u 1_ζ` is a `y⁻ x⁺ 1_ζ`, by the triangular decomposition. -/
lemma exists_leftActOne_eq_triMul (ζ : Y →+ ℤ) (u : QuantumGroup R v) :
    ∃ z, leftActOne R hv' ζ u = leftActOne R hv' ζ (triMul R hv' z) := by
  induction VermaModule.mem_triangularSpan_of u (NeZero.ne v) using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, μ, w', rfl⟩ := hx
    refine ⟨(v ^ R.rootSum (LusztigF.wordWeight w') μ * v ^ ζ μ) •
      (Submodule.Quotient.mk (LusztigF.monomial k w) ⊗ₜ
        Submodule.Quotient.mk (LusztigF.monomial k w')), ?_⟩
    rw [map_smul, map_smul, triMul_tmul, mul_assoc,
      K_mul_plusHom_of_mem (LusztigF.monomial_mem_weightSpace w') μ, mul_smul_comm, map_smul,
      ← mul_assoc, leftActOne_mul_K, smul_smul]
  | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz⟩ := hx
    obtain ⟨z', hz'⟩ := hy
    exact ⟨z + z', by rw [map_add, hz, hz', map_add, map_add]⟩
  | smul c x _ hx =>
    obtain ⟨z, hz⟩ := hx
    exact ⟨c • z, by rw [map_smul, hz, map_smul, map_smul]⟩

variable (R) in
/-- `[y] ⊗ [x] ↦ y⁻ x⁺ (ξ ⊗ η)`. -/
def triAct :
    fQ ⊗[k] fQ →ₗ[k]
      TensorModule k (ChevalleyTwist R v (VermaModule R v Λ)) (VermaModule R v Λ') :=
  (triMul R hv').smulRight (vermaTensorHwv R v Λ Λ')

variable (R) in
/-- `[y] ⊗ [x] ↦ x⁺ ξ ⊗ y⁻ η = ʷ(x⁻ η_Λ) ⊗ y⁻ η_{Λ'}`, a linear isomorphism. -/
def triEquiv :
    fQ ⊗[k] fQ ≃ₗ[k]
      TensorModule k (ChevalleyTwist R v (VermaModule R v Λ)) (VermaModule R v Λ') :=
  (TensorProduct.congr (VermaModule.equivSerreQuotient (R := R) Λ' hv')
    ((VermaModule.equivSerreQuotient (R := R) Λ hv').trans
      (ChevalleyTwist.toTwist R v _))).trans
    ((TensorProduct.comm k _ _).trans (TensorModule.mk _ _))

lemma triEquiv_tmul (y : fQ) (x : LusztigF k I) :
    triEquiv R hv' Λ Λ' (y ⊗ₜ Submodule.Quotient.mk x) =
      TensorModule.mk _ _ ((plusHom R v x • ChevalleyTwist.toTwist R v _
        (VermaModule.hwv R v Λ)) ⊗ₜ[k] VermaModule.equivSerreQuotient (R := R) Λ' hv' y) := by
  rw [ChevalleyTwist.smul_toTwist, chevalley_plusHom]
  rfl

/-- `triAct - triEquiv` lowers the degree of the first factor. -/
lemma triAct_sub_triEquiv_mem (w : List I) (x : LusztigF k I) :
    triAct R hv' Λ Λ' (Submodule.Quotient.mk (LusztigF.monomial k w) ⊗ₜ
        Submodule.Quotient.mk x) -
      triEquiv R hv' Λ Λ' (Submodule.Quotient.mk (LusztigF.monomial k w) ⊗ₜ
        Submodule.Quotient.mk x) ∈
      tensorDegSpan _ Λ' w.length := by
  rw [triEquiv_tmul, VermaModule.equivSerreQuotient_mk, ← VermaModule.toVerma_apply]
  change (minusHom R v (LusztigF.monomial k w) * plusHom R v x) • vermaTensorHwv R v Λ Λ' - _ ∈ _
  rw [mul_smul, vermaTensorHwv, plusHom_smul_tmul_hwv]
  exact minusHom_monomial_smul_tmul_hwv_sub_mem Λ' w _

/-- `triAct` is bijective. -/
theorem bijective_triAct : Function.Bijective (triAct R hv' Λ Λ') := by
  set e := triEquiv R hv' Λ Λ'
  set G : ℕ → Submodule k (fQ ⊗[k] fQ) := fun d ↦
    Submodule.map₂ (TensorProduct.mk k fQ fQ) ((degSpan k I d).map (Submodule.mkQ _)) ⊤
  have hGmono : ∀ {d d'}, d ≤ d' → G d ≤ G d' := fun h ↦
    Submodule.map₂_le_map₂_left (Submodule.map_mono (degSpan_mono h))
  have hW : ∀ d, ∀ z ∈ tensorDegSpan _ Λ' d, e.symm z ∈ G d := by
    intro d z hz
    have h : tensorDegSpan (ChevalleyTwist R v (VermaModule R v Λ)) Λ' d ≤ (G d).comap
        e.symm.toLinearMap := by
      refine Submodule.map₂_le.2 fun a _ b hb ↦ ?_
      obtain ⟨y, hy, rfl⟩ := hb
      obtain ⟨q, rfl⟩ := ((VermaModule.equivSerreQuotient (R := R) Λ hv').trans
        (ChevalleyTwist.toTwist R v _)).surjective a
      have e' : e (Submodule.Quotient.mk y ⊗ₜ q) = TensorModule.mk _ _
          (((VermaModule.equivSerreQuotient (R := R) Λ hv').trans
            (ChevalleyTwist.toTwist R v _)) q ⊗ₜ[k] VermaModule.toVerma R v Λ' y) := rfl
      simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
        Submodule.mem_comap]
      rw [← e', LinearEquiv.symm_apply_apply]
      exact Submodule.apply_mem_map₂ _ ⟨y, hy, rfl⟩ Submodule.mem_top
    exact h hz
  have hS : ∀ d, ∀ z ∈ G (d + 1),
      (e.symm.toLinearMap ∘ₗ triAct R hv' Λ Λ') z - z ∈ G d := by
    intro d z hz
    have h : G (d + 1) ≤ (G d).comap (e.symm.toLinearMap ∘ₗ triAct R hv' Λ Λ' - LinearMap.id) := by
      refine Submodule.map₂_le.2 fun p hp q _ ↦ ?_
      obtain ⟨y, hy, rfl⟩ := hp
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
      simp only [TensorProduct.mk_apply, Submodule.mem_comap]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        have hmem := hW d _ (tensorDegSpan_mono (R := R) (v := v) Λ' (Nat.le_of_lt_succ hw)
          (triAct_sub_triEquiv_mem hv' Λ Λ' w x))
        rwa [map_sub, LinearEquiv.symm_apply_apply] at hmem
      | zero => rw [map_zero, zero_tmul, map_zero]; exact zero_mem _
      | add y y' _ _ hy hy' => rw [map_add, add_tmul, map_add]; exact add_mem hy hy'
      | smul c y _ hy => rw [map_smul, ← smul_tmul', map_smul]; exact Submodule.smul_mem _ c hy
    simpa using h hz
  have hbij := LinearMap.bijective_of_sub_mem_filtration
    (e.symm.toLinearMap ∘ₗ triAct R hv' Λ Λ') G
    (by simp [G, degSpan_zero]) (fun z ↦ ?_) hS
  · have h : triAct R hv' Λ Λ' = e.toLinearMap ∘ₗ (e.symm.toLinearMap ∘ₗ triAct R hv' Λ Λ') := by
      ext; simp
    rw [h, LinearMap.coe_comp]
    exact e.bijective.comp hbij
  · induction z using TensorProduct.inductionOn with
    | tmul p q =>
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ p
      obtain ⟨d, hd⟩ := exists_mem_degSpan y
      exact ⟨d, Submodule.apply_mem_map₂ _ ⟨y, hd, rfl⟩ Submodule.mem_top⟩
    | add z z' hz hz' =>
      obtain ⟨d, hd⟩ := hz
      obtain ⟨d', hd'⟩ := hz'
      exact ⟨max d d', add_mem (hGmono (le_max_left _ _) hd) (hGmono (le_max_right _ _) hd')⟩

/-- **[Lus] 23.3.1 (c)**, injectivity: `u (ξ ⊗ η) = 0` in `ʷM_Λ ⊗ M_{Λ'}` if and only if
`u 1_{Λ'-Λ} = 0` in `U̇`. -/
theorem smul_vermaTensorHwv_eq_zero_iff (u : QuantumGroup R v) :
    u • vermaTensorHwv R v Λ Λ' = 0 ↔ leftActOne R hv' (Λ' - Λ) u = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨z, hz⟩ := exists_leftActOne_eq_triMul hv' (Λ' - Λ) u
    have hm := vermaTensorHwv_mem_weightSpace (R := R) (v := v) Λ Λ'
    have h' : triAct R hv' Λ Λ' z = 0 := by
      change triMul R hv' z • vermaTensorHwv R v Λ Λ' = 0
      rw [← weightAct_leftActOne hv' _ _ hm, ← hz, weightAct_leftActOne, h]
    rw [hz, (injective_iff_map_eq_zero _).1 (bijective_triAct hv' Λ Λ').1 z h', map_zero,
      map_zero]
  · rw [← weightAct_leftActOne hv' _ _ (vermaTensorHwv_mem_weightSpace Λ Λ'), h, map_zero]

include hv' in
/-- **[Lus] 23.3.1 (c)**, surjectivity: every vector of `ʷM_Λ ⊗ M_{Λ'}` is a `u (ξ ⊗ η)`. -/
theorem surjective_smul_vermaTensorHwv :
    Function.Surjective fun u : QuantumGroup R v ↦ u • vermaTensorHwv R v Λ Λ' := fun n ↦ by
  obtain ⟨z, rfl⟩ := (bijective_triAct hv' Λ Λ').2 n
  exact ⟨triMul R hv' z, rfl⟩

/-- **[Lus] 23.3.1 (c)**: `u 1_{Λ'-Λ} ↦ u (ξ ⊗ η)` is a linear isomorphism
`U̇ 1_{Λ'-Λ} ≃ ʷM_Λ ⊗ M_{Λ'}`. Here `U̇ 1_ζ` is the range of `u ↦ u 1_ζ` (`leftActOne`). -/
def vermaTensorEquiv :
    LinearMap.range (leftActOne R hv' (Λ' - Λ)) ≃ₗ[k]
      TensorModule k (ChevalleyTwist R v (VermaModule R v Λ)) (VermaModule R v Λ') :=
  LinearEquiv.ofBijective
    ((weightAct R (Λ' - Λ) _ (vermaTensorHwv_mem_weightSpace Λ Λ')).domRestrict _) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun n ↦ ?_⟩
    · rintro ⟨_, u, rfl⟩ h
      have h' : u • vermaTensorHwv R v Λ Λ' = 0 := by
        rw [← weightAct_leftActOne hv' _ _ (vermaTensorHwv_mem_weightSpace Λ Λ')]
        exact h
      exact Subtype.ext ((smul_vermaTensorHwv_eq_zero_iff hv' Λ Λ' u).1 h')
    · obtain ⟨u, rfl⟩ := surjective_smul_vermaTensorHwv hv' Λ Λ' n
      exact ⟨⟨_, u, rfl⟩, weightAct_leftActOne hv' _ _ _ u⟩

theorem vermaTensorEquiv_apply (u : QuantumGroup R v) :
    vermaTensorEquiv hv' Λ Λ' ⟨leftActOne R hv' (Λ' - Λ) u, u, rfl⟩ =
      u • vermaTensorHwv R v Λ Λ' :=
  weightAct_leftActOne hv' _ _ _ u

end TensorVerma

end Modified

end LieLean.QuantumGroup
