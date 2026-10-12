/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PositiveComul
import LieLean.Algebra.QuantumGroup.TensorModule

/-!
# Original Verma quotient coordinates

The actual twisted-E image quotient is identified with the left skew kernel.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

/-! Concrete zero-string coordinates for the Chevalley-twisted original Verma module.
The quotient below is only a vector-space quotient, never a U-module quotient.
The source argument is Lusztig, Introduction to Quantum Groups, 38.1.8, printed 298–299.
-/
noncomputable section
open LieLean LusztigF TensorProduct
open LieLean.QuantumGroup
namespace VermaProjection
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (Λ : Y →+ ℤ)

/-- Actual radical/Serre comparison followed by the original Verma equivalence. -/
def vermaEquiv : Quotient D 𝕧 ≃ₗ[𝕂] VermaModule R 𝕧 Λ :=
  (negativeQuotientEquiv D).symm.trans (VermaModule.equivSerreQuotient Λ ratFunc_X_not_root)

@[simp] theorem vermaEquiv_toQuotient (x : LusztigF 𝕂 I) :
    vermaEquiv R Λ (toQuotient D 𝕧 x) = minusHom R 𝕧 x • VermaModule.hwv R 𝕧 Λ := by
  simp [vermaEquiv]

/-- Evaluation of the actual positive embedding on the lowest Verma generator. -/
theorem vermaEquiv_apply (x : Quotient D 𝕧) :
    vermaEquiv R Λ x = chevalley R 𝕧 (quotientPlus R x) • VermaModule.hwv R 𝕧 Λ := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  simp only [vermaEquiv_toQuotient, quotientPlus_toQuotient]
  congr 1
  induction x using FreeAlgebra.induction with
  | grade0 c => simp
  | grade1 j => simp
  | add a b ha hb => simp [ha, hb]
  | mul a b ha hb => simp [ha, hb]

/-- The actual E operator on the Chevalley twist, not the original highest action. -/
def lowestE (i : I) : Module.End 𝕂 (VermaModule R 𝕧 Λ) where
  toFun m := chevalley R 𝕧 (E R 𝕧 i) • m
  map_add' := smul_add _
  map_smul' c m := smul_comm _ c m

@[simp] theorem lowestE_vermaEquiv (i : I) (x : Quotient D 𝕧) :
    lowestE R Λ i (vermaEquiv R Λ x) =
      vermaEquiv R Λ (toQuotient D 𝕧 (θ 𝕂 i) * x) := by
  simp [lowestE, vermaEquiv_apply, mul_smul]

variable (D)
/-- The actual theta-left-multiplication image in Lusztig's original quotient. -/
def thetaImage (i : I) : Submodule 𝕂 (Quotient D 𝕧) :=
  LinearMap.range (LinearMap.mulLeft 𝕂 (toQuotient D 𝕧 (θ 𝕂 i)))

/-- Ordinary-power strings have their actual zero-string coefficient. -/
theorem projection_string (i : I) (n : ℕ) {a : LusztigF 𝕂 I}
    (ha : a ∈ skewGenerated D 𝕧 i) :
    quotientSkewProjection D i (toQuotient D 𝕧 (θ 𝕂 i ^ n * a)) =
      if n = 0 then toQuotient D 𝕧 a else 0 := by
  have hk := quotientLDeriv_eq_zero_of_mem D i (show toQuotient D 𝕧 a ∈
    quotientSkewGenerated D i from ⟨a, ha, rfl⟩)
  have hf := qFactorial_ne_zero_of_not_root (D := D) RatFunc.X_ne_zero
    (pow_ne_one_of_transcendental' transcendental_ratFunc_X) i n
  have hp : toQuotient D 𝕧 (θ 𝕂 i ^ n * a) =
      qFactorial (𝕧 ^ D.d i) n •
        (quotientIntegralGenerator D i n * toQuotient D 𝕧 a) := by
    simp [quotientIntegralGenerator, qDivPow, smul_smul, hf]
  rw [hp, map_smul, quotientSkewProjection_divided_mul D i n hk]
  split_ifs with hn
  · subst n; simp [qFactorial]
  · simp

/-- Projection annihilates the whole actual left theta image, not merely pure strings. -/
theorem projection_theta_mul (i : I) (x : Quotient D 𝕧) :
    quotientSkewProjection D i (toQuotient D 𝕧 (θ 𝕂 i) * x) = 0 := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  have hx : x ∈ skewStringSpan D 𝕧 i := by rw [skewStringSpan_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [← map_mul, ← mul_assoc, ← pow_succ', projection_string D i (n + 1) ha]
    simp
  | zero => simp
  | add x y _ _ hx hy => simp [mul_add, hx, hy]
  | smul c x _ hx => simp [hx]

/-- Every element differs from its actual zero-string coefficient by theta_i f. -/
theorem sub_projection_mem (i : I) (x : Quotient D 𝕧) :
    x - quotientSkewProjection D i x ∈ thetaImage D i := by
  obtain ⟨x, rfl⟩ := toQuotient_surjective D 𝕧 x
  have hx : x ∈ skewStringSpan D 𝕧 i := by rw [skewStringSpan_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [projection_string D i n ha]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, sub_zero]
      refine ⟨toQuotient D 𝕧 (θ 𝕂 i ^ n * a), ?_⟩
      simp [LinearMap.mulLeft_apply, ← map_mul, pow_succ', mul_assoc]
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [map_add, add_sub_add_comm] using (thetaImage D i).add_mem hx hy
  | smul c x _ hx =>
    simpa only [map_smul, smul_sub] using (thetaImage D i).smul_mem c hx

/-- Exact kernel identification for the existing projector. -/
theorem ker_projection (i : I) :
    LinearMap.ker (quotientSkewProjection D i) = thetaImage D i := by
  ext x
  constructor
  · intro hx
    have := sub_projection_mem D i x
    simpa only [LinearMap.mem_ker.mp hx, sub_zero] using this
  · rintro ⟨y, rfl⟩
    exact projection_theta_mul D i y

/-- The coordinate in the actual skew-derivation kernel. -/
def kernelProjection (i : I) : Quotient D 𝕧 →ₗ[𝕂] LinearMap.ker (quotientLDeriv D i) :=
  (quotientSkewProjection D i).codRestrict _ fun x ↦
    quotientLDeriv_eq_zero_of_mem D i (quotientSkewProjection_mem D i x)

variable {D}
/-- The original twisted-Verma E_i image as a base-field subspace. -/
abbrev vermaEImage (i : I) : Submodule 𝕂 (VermaModule R 𝕧 Λ) :=
  LinearMap.range (lowestE R Λ i)

/-- The actual zero-string coordinate of an arbitrary Verma vector. -/
def vermaCoordinate (i : I) :
    VermaModule R 𝕧 Λ →ₗ[𝕂] LinearMap.ker (quotientLDeriv D i) :=
  kernelProjection D i ∘ₗ (vermaEquiv R Λ).symm.toLinearMap

@[simp] theorem vermaCoordinate_eval (i : I) (x : Quotient D 𝕧) :
    (vermaCoordinate R Λ i (vermaEquiv R Λ x) : Quotient D 𝕧) =
      quotientSkewProjection D i x := by
  change quotientSkewProjection D i ((vermaEquiv R Λ).symm (vermaEquiv R Λ x)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The kernel is exactly E_i M, with E acting through the frozen Chevalley twist. -/
theorem ker_vermaCoordinate (i : I) :
    LinearMap.ker (vermaCoordinate R Λ i) = vermaEImage R Λ i := by
  ext m
  obtain ⟨x, rfl⟩ := (vermaEquiv R Λ).surjective m
  constructor
  · intro h
    have hx : quotientSkewProjection D i x = 0 := by
      simpa using congrArg Subtype.val (LinearMap.mem_ker.mp h)
    have hx' : x ∈ thetaImage D i := by rw [← ker_projection]; exact hx
    obtain ⟨y, hy⟩ := hx'
    exact ⟨vermaEquiv R Λ y, by rw [lowestE_vermaEquiv]; exact congrArg (vermaEquiv R Λ) hy⟩
  · rintro ⟨m, hm⟩
    obtain ⟨y, rfl⟩ := (vermaEquiv R Λ).surjective m
    rw [lowestE_vermaEquiv] at hm
    have hx := (vermaEquiv R Λ).injective hm
    apply Subtype.ext
    change quotientSkewProjection D i ((vermaEquiv R Λ).symm (vermaEquiv R Λ x)) = 0
    rw [LinearEquiv.symm_apply_apply, ← hx, projection_theta_mul]

/-- Well-defined vector-space quotient coordinate, with the actual E_i M denominator. -/
def quotientCoordinate (i : I) :
    (VermaModule R 𝕧 Λ ⧸ vermaEImage R Λ i) →ₗ[𝕂]
      LinearMap.ker (quotientLDeriv D i) :=
  (vermaEImage R Λ i).liftQ (vermaCoordinate R Λ i) (ker_vermaCoordinate R Λ i).ge

/-- The concrete Verma quotient is the existing zero-string kernel. -/
def vermaQuotientEquiv (i : I) :
    (VermaModule R 𝕧 Λ ⧸ vermaEImage R Λ i) ≃ₗ[𝕂]
      LinearMap.ker (quotientLDeriv D i) :=
  LinearEquiv.ofBijective (quotientCoordinate R Λ i) ⟨by
    rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    rw [← ker_vermaCoordinate]
    exact hm,
    fun x ↦ ⟨Submodule.Quotient.mk (vermaEquiv R Λ x), by
      apply Subtype.ext
      change (vermaCoordinate R Λ i (vermaEquiv R Λ x) : Quotient D 𝕧) = x
      rw [vermaCoordinate_eval, quotientSkewProjection_of_ker D i x.property]⟩⟩

/-- The forward formula is valid for every element, not just homogeneous vectors. -/
@[simp] theorem vermaQuotientEquiv_mk (i : I) (x : Quotient D 𝕧) :
    (vermaQuotientEquiv R Λ i (Submodule.Quotient.mk (vermaEquiv R Λ x)) : Quotient D 𝕧) =
      quotientSkewProjection D i x := vermaCoordinate_eval R Λ i x

/-- Its inverse is the class of actual evaluation on the lowest generator. -/
theorem vermaQuotientEquiv_symm (i : I) (x : LinearMap.ker (quotientLDeriv D i)) :
    (vermaQuotientEquiv R Λ i).symm x = Submodule.Quotient.mk (vermaEquiv R Λ x) := by
  apply (vermaQuotientEquiv R Λ i).injective
  apply Subtype.ext
  simp [quotientSkewProjection_of_ker D i x.property]

/-- Decoding the first vector and the second quotient is a genuine tensor equivalence. -/
def tensorCoordinateEquiv (Λ₂ : Y →+ ℤ) (i : I) :
    (VermaModule R 𝕧 Λ ⊗[𝕂] (VermaModule R 𝕧 Λ₂ ⧸ vermaEImage R Λ₂ i)) ≃ₗ[𝕂]
      (Quotient D 𝕧 ⊗[𝕂] LinearMap.ker (quotientLDeriv D i)) :=
  TensorProduct.congr (vermaEquiv R Λ).symm (vermaQuotientEquiv R Λ₂ i)

end VermaProjection
