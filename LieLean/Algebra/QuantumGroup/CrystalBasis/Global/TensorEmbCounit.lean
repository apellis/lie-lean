/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorEmbCoordinates

/-!
# The coordinates `f(b; 1, b₂)` of `χ(b⁻η'')`

Let `χ : Λ_{λ+λ'} → Λ_λ ⊗ Λ_{λ'}` be the homomorphism with `χ(η'') = η ⊗ η'` (`tensorEmb`) and
write `χ(b⁻η'') = Σ f(b; b₁, b₂) b₁⁻η ⊗ b₂⁻η'` for `b ∈ B`. [Lus] Prop. 25.1.2 (c) computes the
coordinates with `b₁ = 1`: they are `f(b; 1, b₂) = δ_{b, b₂}` (and vanish if `b ∉ B(λ')`).

## Main results

* `hwCounit`: the linear form `y⁻η ↦ ε(y)` on `Λ_λ`, `ε` the counit of `f`; it is the coordinate
  at `1 ∈ B(λ)` (`repr_canonicalBasisHWBasis_one`) and kills `Fᵢ Λ_λ` (`hwCounit_F_smul`);
* `hwCounit_rTensor_tensorEmb_ev`: `(ε ⊗ 1)(χ(y⁻η'')) = y⁻η'`;
* `repr_tensorEmb_evq_one`: **[Lus] Prop. 25.1.2 (c)**.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 25.1.2.
-/

open TensorProduct

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### The counit of `f` -/

section Counit

variable (I) in
/-- The counit `ε : 'f → ℚ(v)`, `θᵢ ↦ 0`. -/
abbrev fCounit : LusztigF 𝕂 I →ₐ[𝕂] 𝕂 := FreeAlgebra.algebraMapInv

omit [Finite I] [DecidableEq I] in
@[simp] lemma fCounit_θ (i : I) : fCounit I (θ 𝕂 i) = 0 := by
  simp [θ, FreeAlgebra.algebraMapInv]

omit [Finite I] [DecidableEq I] in
lemma fCounit_serreElement (i j : I) : fCounit I (serreElement D 𝕧 i j) = 0 := by
  simp [serreElement, qSerreDiv, map_sum, map_mul]

omit [Finite I] [DecidableEq I] in
lemma fCounit_eq_zero_of_mem_serreIdeal {x : LusztigF 𝕂 I} (hx : x ∈ serreIdeal D 𝕧) :
    fCounit I x = 0 := by
  have h : serreIdeal D 𝕧 ≤ TwoSidedIdeal.ker (fCounit I) := by
    rw [serreIdeal, TwoSidedIdeal.span_le]
    rintro _ ⟨i, j, -, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
    exact fCounit_serreElement i j
  exact (TwoSidedIdeal.mem_ker _).1 (h hx)

omit [Finite I] [DecidableEq I] in
lemma fCounit_monomial_cons (i : I) (w : List I) : fCounit I (monomial 𝕂 (i :: w)) = 0 := by
  rw [monomial_cons, map_mul, fCounit_θ, zero_mul]

omit [Finite I] [DecidableEq I] in
lemma fCounit_rev (x : LusztigF 𝕂 I) : fCounit I (rev 𝕂 I x) = fCounit I x := by
  induction x using FreeAlgebra.induction with
  | grade0 c => rw [rev_algebraMap]
  | grade1 i => exact congrArg _ (rev_θ i)
  | mul a b ha hb => rw [rev_mul, map_mul, map_mul, ha, hb, mul_comm]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

omit [Finite I] [DecidableEq I] in
lemma evKernel_le_ker_fCounit (n : I → ℕ) :
    evKernel D n ≤ LinearMap.ker (fCounit I).toLinearMap := by
  refine sup_le (fun x hx ↦ ?_) ?_
  · exact fCounit_eq_zero_of_mem_serreIdeal (mem_serreSubmodule.1 hx)
  · rw [Submodule.span_le]
    rintro _ ⟨⟨a, i⟩, rfl⟩
    change fCounit I (FreeAlgebra.wordBasis 𝕂 I (powWord n (a, i))) = 0
    rw [← monomial_eq_wordBasis, powWord]
    cases a with
    | nil => rw [List.nil_append, List.replicate_succ]; exact fCounit_monomial_cons i _
    | cons j a => rw [List.cons_append]; exact fCounit_monomial_cons j _

variable (D) in
/-- The counit on `U⁻ = f`. -/
def umCounit : Um D 𝕧 →ₗ[𝕂] 𝕂 :=
  (serreSubmodule D 𝕧).liftQ (fCounit I).toLinearMap fun _ hx ↦
    fCounit_eq_zero_of_mem_serreIdeal (mem_serreSubmodule.1 hx)

omit [Finite I] [DecidableEq I] in
@[simp] lemma umCounit_mk (x : LusztigF 𝕂 I) :
    umCounit D (Submodule.Quotient.mk x) = fCounit I x :=
  rfl

omit [Finite I] [DecidableEq I] in
lemma umCounit_starU (x : Um D 𝕧) : umCounit D (starU D 𝕧 x) = umCounit D x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [starU_mk, umCounit_mk, umCounit_mk, fCounit_rev]

omit [Finite I] [DecidableEq I] in
lemma umCounit_f (i : I) (x : Um D 𝕧) : umCounit D (NegativePart.f D 𝕧 i x) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change fCounit I (θ 𝕂 i * y) = 0
  rw [map_mul, fCounit_θ, zero_mul]

omit [Finite I] [DecidableEq I] in
lemma umCounit_eq_zero_of_mem_Uw {ν : I →₀ ℕ} (hν : ν ≠ 0) {x : Um D 𝕧}
    (hx : x ∈ Uw D 𝕧 ν) : umCounit D x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Submodule.mkQ_apply, umCounit_mk]
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl, rfl⟩ := hz
    cases w with
    | nil => exact absurd rfl hν
    | cons i w => exact fCounit_monomial_cons i w
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

variable (D) in
/-- The unit `1 ∈ B`. -/
lemma one_mem_canonicalBasis : fWi (D := D) hvt [] ∈ canonicalBasis D :=
  Set.mem_iUnion.2 ⟨0, (mem_canonicalBasisAt_iff D).2 (Or.inl ⟨rfl, rfl⟩)⟩

omit [Finite I] in
lemma umCounit_fWi_nil : umCounit D (fWi (D := D) hvt []) = 1 := by
  change fCounit I 1 = 1
  exact map_one _

open Classical in
/-- On the canonical basis, the counit is `δ_{b,1}`. -/
lemma umCounit_of_mem_canonicalBasis {x : Um D 𝕧} (hx : x ∈ canonicalBasis D) :
    umCounit D x = if x = fWi hvt [] then 1 else 0 := by
  obtain ⟨ν, b, rfl⟩ := (mem_canonicalBasis_iff D).1 hx
  by_cases hν : ν = 0
  · subst hν
    simp [negGlobal_zero]
  · have h0 := umCounit_eq_zero_of_mem_Uw hν (negGlobal_mem D ν b).2.1
    rw [h0]
    split_ifs with h
    · rw [h, umCounit_fWi_nil] at h0
      exact (one_ne_zero h0).elim
    · rfl

/-- `1 ∈ B(λ)`. -/
lemma one_mem_canonicalBasisHW (Λ : Dom R) : fWi (D := D) hvt [] ∈ canonicalBasisHW D Λ := by
  refine (mem_canonicalBasisHW_iff D Λ).2 ⟨one_mem_canonicalBasis D, fun i h ↦ ?_⟩
  obtain ⟨y, hy⟩ := (mem_rightRange_iff D).1 h
  have h1 := congrArg (umCounit D) hy
  rw [umCounit_starU, umCounit_fWi_nil, pow_succ', Module.End.mul_apply, umCounit_f] at h1
  exact zero_ne_one h1

end Counit

/-! ### The coordinate at `1 ∈ B(λ)` -/

section HighestWeight

variable (Λ : Dom R)

/-- The element `1 ∈ B(λ)`. -/
abbrev hwOne : canonicalBasisHW D Λ := ⟨fWi hvt [], one_mem_canonicalBasisHW Λ⟩

include hR in
lemma ker_ev_le_ker_fCounit :
    LinearMap.ker (ev R 𝕧 Λ.1) ≤ LinearMap.ker (fCounit I).toLinearMap := by
  rw [ker_ev_eq hR Λ]
  exact evKernel_le_ker_fCounit _

/-- The linear form `y⁻η ↦ ε(y)` on `Λ_λ`. -/
def hwCounit : IrreducibleModule R 𝕧 Λ.1 →ₗ[𝕂] 𝕂 :=
  (LinearMap.ker (ev R 𝕧 Λ.1)).liftQ (fCounit I).toLinearMap (ker_ev_le_ker_fCounit hR Λ) ∘ₗ
    ((ev R 𝕧 Λ.1).quotKerEquivOfSurjective (ev_surjective Λ)).symm.toLinearMap

lemma hwCounit_ev (y : LusztigF 𝕂 I) : hwCounit hR Λ (ev R 𝕧 Λ.1 y) = fCounit I y := by
  have h₁ : ((ev R 𝕧 Λ.1).quotKerEquivOfSurjective (ev_surjective Λ)).symm (ev R 𝕧 Λ.1 y) =
      Submodule.Quotient.mk y :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp only [hwCounit, LinearMap.comp_apply, LinearEquiv.coe_coe, h₁, Submodule.liftQ_apply,
    AlgHom.toLinearMap_apply]

lemma hwCounit_evq (x : Um D 𝕧) : hwCounit hR Λ (evq hvt Λ x) = umCounit D x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [evq_mk, hwCounit_ev, umCounit_mk]

lemma hwCounit_hwv : hwCounit hR Λ (IrreducibleModule.hwv R 𝕧 Λ.1) = 1 := by
  rw [← ev_one, hwCounit_ev, map_one]

lemma hwCounit_F_smul (i : I) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwCounit hR Λ (F R 𝕧 i • m) = 0 := by
  obtain ⟨y, rfl⟩ := ev_surjective Λ m
  rw [← ev_ι_mul, hwCounit_ev, map_mul]
  change fCounit I (θ 𝕂 i) * _ = 0
  rw [fCounit_θ, zero_mul]

/-- `hwCounit` is the coordinate at `1 ∈ B(λ)` in the basis `b⁻η`. -/
theorem repr_canonicalBasisHWBasis_one (m : IrreducibleModule R 𝕧 Λ.1) :
    (canonicalBasisHWBasis Λ hR).repr m (hwOne Λ) = hwCounit hR Λ m := by
  have h : (canonicalBasisHWBasis Λ hR).coord (hwOne Λ) = hwCounit hR Λ :=
    (canonicalBasisHWBasis Λ hR).ext fun b ↦ by
      classical
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, canonicalBasisHWBasis_apply,
        hwCounit_evq, umCounit_of_mem_canonicalBasis (canonicalBasisHW_subset D Λ b.2),
        Finsupp.single_apply]
      simp only [hwOne, Subtype.ext_iff]
  rw [← h, Module.Basis.coord_apply]

end HighestWeight

/-! ### [Lus] Prop. 25.1.2 (c) -/

section Tensor

variable (Λ₁ Λ₂ : Dom R)

/-- `(ε ⊗ 1)(χ(y⁻η'')) = y⁻η'`. -/
theorem hwCounit_rTensor_tensorEmb_ev (y : LusztigF 𝕂 I) :
    TensorProduct.lid 𝕂 _ (((hwCounit hR Λ₁).rTensor _)
      ((TensorModule.mk _ _).symm (tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R 𝕧 (Λ₁ + Λ₂).1 y)))) =
      ev R 𝕧 Λ₂.1 y := by
  let φ : TensorModule 𝕂 (IrreducibleModule R 𝕧 Λ₁.1) (IrreducibleModule R 𝕧 Λ₂.1) →ₗ[𝕂]
      IrreducibleModule R 𝕧 Λ₂.1 :=
    (TensorProduct.lid 𝕂 _).toLinearMap ∘ₗ (hwCounit hR Λ₁).rTensor _ ∘ₗ
      (TensorModule.mk _ _).symm.toLinearMap
  have hφ : ∀ (i : I) z, φ (F R 𝕧 i • z) = F R 𝕧 i • φ z := fun i z ↦ by
    obtain ⟨z, rfl⟩ := (TensorModule.mk _ _).surjective z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      rw [TensorModule.F_smul_tmul]
      simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        map_add, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hwCounit_F_smul, zero_smul,
        zero_add, smul_comm (hwCounit hR Λ₁ x) (F R 𝕧 i) y]
    | add a b ha hb => simp only [map_add, smul_add, ha, hb]
  change φ _ = _
  let P : LusztigF 𝕂 I → Prop := fun y ↦
    φ (tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R 𝕧 (Λ₁ + Λ₂).1 y)) = ev R 𝕧 Λ₂.1 y
  have hP1 : P 1 := by
    simp only [P, ev_one]
    erw [tensorEmb_hwv]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hwCounit_hwv, one_smul]
  have key : ∀ a z, P z → P (a * z) := by
    intro a
    induction a using FreeAlgebra.induction with
    | grade0 c =>
      intro z hz
      simp only [P, ← Algebra.smul_def, map_smul, LinearMap.map_smul_of_tower] at hz ⊢
      rw [hz]
    | grade1 j =>
      intro z hz
      simp only [P, ev_ι_mul, map_smul] at hz ⊢
      rw [hφ, hz]
    | mul a b ha hb => intro z hz; rw [mul_assoc]; exact ha _ (hb z hz)
    | add a b ha hb =>
      intro z hz
      simp only [P, add_mul, map_add] at ha hb ⊢
      rw [ha z hz, hb z hz]
  have := key y 1 hP1
  rwa [mul_one] at this

/-- The coordinates `f(x; 1, b₂)` of `χ(x⁻η'')` are the coordinates of `x⁻η'`. -/
lemma repr_tensorEmb_ev_one (y : LusztigF 𝕂 I) (b₂ : canonicalBasisHW D Λ₂) :
    (tensorHWBasis hR Λ₁ Λ₂).repr (tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R 𝕧 (Λ₁ + Λ₂).1 y))
      (hwOne Λ₁, b₂) = (canonicalBasisHWBasis Λ₂ hR).repr (ev R 𝕧 Λ₂.1 y) b₂ := by
  rw [← hwCounit_rTensor_tensorEmb_ev hR Λ₁ Λ₂ y]
  generalize tensorEmb hvt hR Λ₁.2 Λ₂.2 (ev R 𝕧 (Λ₁ + Λ₂).1 y) = z
  obtain ⟨z, rfl⟩ := (TensorModule.mk _ _).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [repr_tensorHWBasis_mk, LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, map_smul, Finsupp.smul_apply, smul_eq_mul,
      repr_canonicalBasisHWBasis_one]
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply, ha, hb]

open Classical in
/-- **[Lus] Prop. 25.1.2 (c)**: for `b ∈ B` and `b₂ ∈ B(λ')`, `f(b; 1, b₂) = 1` if `b₂ = b` and
`f(b; 1, b₂) = 0` otherwise. (If `b⁻η' = 0`, i.e. `b ∉ B(λ')`, all `f(b; 1, b₂)` vanish.) -/
theorem repr_tensorEmb_evq_one {x : Um D 𝕧} (hx : x ∈ canonicalBasis D)
    (b₂ : canonicalBasisHW D Λ₂) :
    (tensorHWBasis hR Λ₁ Λ₂).repr (tensorEmb hvt hR Λ₁.2 Λ₂.2 (evq hvt (Λ₁ + Λ₂) x))
      (hwOne Λ₁, b₂) = if (b₂ : Um D 𝕧) = x then 1 else 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [evq_mk, repr_tensorEmb_ev_one, ← evq_mk hvt Λ₂ y]
  by_cases hx' : Submodule.Quotient.mk y ∈ canonicalBasisHW D Λ₂
  · rw [show evq hvt Λ₂ (Submodule.Quotient.mk y) = canonicalBasisHWBasis Λ₂ hR ⟨_, hx'⟩ from
      (canonicalBasisHWBasis_apply Λ₂ hR ⟨_, hx'⟩).symm, Module.Basis.repr_self,
      Finsupp.single_apply]
    simp only [Subtype.ext_iff, eq_comm]
  · rw [evq_eq_zero_of_notMem_canonicalBasisHW Λ₂ hR hx hx', map_zero, Finsupp.zero_apply]
    exact (ite_eq_right_iff.2 fun h ↦ absurd (h ▸ b₂.2) hx').symm

end Tensor

end LieLean.QuantumGroup
