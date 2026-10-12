/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidCoproduct.VermaProjection.Extraction

/-!
# Ordered negative-string extraction

Both Cartan factors and the inverse-braid scalar are retained until extraction.

## References

Lusztig, *Introduction to Quantum Groups*, second printing (1994),
37.3.1–37.3.2 and the proof of 38.1.8 (printed pp. 293, 297–299).
The finite-cutoff argument uses the actual quantum group and original Verma modules.
No restricted braid isometry or PBW norm conclusion is asserted here.
-/

noncomputable section
open LieLean LusztigF TensorProduct
open LieLean.QuantumGroup FiniteIntertwining
namespace VermaProjection
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (Λ₁ Λ₂ : Y →+ ℤ)

/-- Faithful realization uses the original first Verma and second E-image quotient. -/
def realizeKernelTensor (i : I) :
    (Quotient D 𝕧 ⊗[𝕂] LinearMap.ker (quotientLDeriv D i)) →ₗ[𝕂]
      (VermaModule R 𝕧 Λ₁ ⊗[𝕂] (VermaModule R 𝕧 Λ₂ ⧸ vermaEImage R Λ₂ i)) :=
  TensorProduct.map (vermaEquiv R Λ₁).toLinearMap
    ((vermaEImage R Λ₂ i).mkQ ∘ₗ (vermaEquiv R Λ₂).toLinearMap ∘ₗ
      (LinearMap.ker (quotientLDeriv D i)).subtype)

/-- The actual evaluation/quotient map, on arbitrary tensors, is the constructed inverse. -/
theorem realizeKernelTensor_eq (i : I) :
    realizeKernelTensor R Λ₁ Λ₂ i = (tensorCoordinateEquiv R Λ₁ Λ₂ i).symm.toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change vermaEquiv R Λ₁ a ⊗ₜ[𝕂] Submodule.Quotient.mk (vermaEquiv R Λ₂ b) =
    vermaEquiv R Λ₁ a ⊗ₜ[𝕂] (vermaQuotientEquiv R Λ₂ i).symm b
  rw [vermaQuotientEquiv_symm]

/-- Equality of evaluated arbitrary tensors is equivalent to equality of actual coefficients.
There is no assumed family-faithfulness or weight-separation premise. -/
theorem tensor_coefficient_faithful (i : I)
    (z w : Quotient D 𝕧 ⊗[𝕂] LinearMap.ker (quotientLDeriv D i)) :
    realizeKernelTensor R Λ₁ Λ₂ i z = realizeKernelTensor R Λ₁ Λ₂ i w ↔ z = w := by
  rw [realizeKernelTensor_eq]
  exact (tensorCoordinateEquiv R Λ₁ Λ₂ i).symm.injective.eq_iff

/-- Exact ordered negative-string evaluation. Both Cartan factors and the general weight
are retained; positive strings vanish because F acts as old E on the lowest generator. -/
theorem extract_negative_string (i : I) (a b : Quotient D 𝕧) (μ ν : Y) (n : ℕ) :
    extract R Λ₁ Λ₂ i
      ((quotientPlus R a * K R 𝕧 μ * qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) * K R 𝕧 ν) ⊗ₜ[𝕂]
        quotientPlus R b) =
      if n = 0 then 𝕧 ^ (-Λ₁ (μ + ν)) • (a ⊗ₜ[𝕂] quotientSkewProjection D i b) else 0 := by
  cases n with
  | zero =>
    simp [qDivPow, qFactorial, mul_assoc, K_add]
  | succ n =>
    simp only [extract, LinearMap.coe_mk, AddHom.coe_mk]
    rw [vacuum, lowestPair_tmul]
    simp [qDivPow, map_mul, map_smul, map_pow, chevalley_K,
      mul_smul, VermaModule.K_smul_hwv, smul_comm, pow_succ]

/-- The literal signed/weighted summand displayed in the source's inverse-braid expansion. -/
def negativeSourceTerm (i : I) (n : ℕ) (ν : I →₀ ℕ) (a b : Quotient D 𝕧) :
    QuantumGroup R 𝕧 ⊗[𝕂] QuantumGroup R 𝕧 :=
  ((-1 : 𝕂) ^ n * (𝕧 ^ D.d i) ^ (-((n * (n - 1) : ℕ) : ℤ))) •
    ((quotientPlus R a * K R 𝕧 (-(n • ktilde R i)) *
      qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i) * K R 𝕧 (positiveToralWeight R ν)) ⊗ₜ[𝕂]
        quotientPlus R b)

/-- At the source weight, the complete signed negative summand extracts its n=0 coefficient. -/
theorem extract_negativeSourceTerm (i : I) (n : ℕ) (ν : I →₀ ℕ) (a b : Quotient D 𝕧) :
    extract R 0 Λ₂ i (negativeSourceTerm R i n ν a b) =
      if n = 0 then a ⊗ₜ[𝕂] quotientSkewProjection D i b else 0 := by
  rw [negativeSourceTerm, map_smul, extract_negative_string]
  split_ifs with hn
  · subst n; simp
  · simp

/-- Arbitrary finite signed negative expansions retain precisely the zero-string terms. -/
theorem extract_finite_negative {A : Type*} (s : Finset A) (i : I)
    (d : A → 𝕂) (n : A → ℕ) (ν : A → I →₀ ℕ) (a b : A → Quotient D 𝕧) :
    extract R 0 Λ₂ i (∑ j ∈ s, d j • negativeSourceTerm R i (n j) (ν j) (a j) (b j)) =
      ∑ j ∈ s, if n j = 0 then d j • (a j ⊗ₜ[𝕂] quotientSkewProjection D i (b j)) else 0 := by
  simp only [map_sum, map_smul, extract_negativeSourceTerm]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

/-- The concrete coefficient-extraction identity for the actual braid-conjugated coproduct.
The premise is an actual finite expansion, not an assumed compatibility or faithful action. -/
theorem finite_braid_coefficient_identity {A : Type*} (s : Finset A) (i : I)
    (x : Quotient D 𝕧) (d : A → 𝕂) (n : A → ℕ) (ν : A → I →₀ ℕ)
    (a b : A → Quotient D 𝕧)
    (h : braidDelta R 𝕧 ratFunc_X_not_root i (quotientPlus R x) =
      ∑ j ∈ s, d j • negativeSourceTerm R i (n j) (ν j) (a j) (b j)) :
    (∑ j ∈ s, if n j = 0 then d j • (a j ⊗ₜ[𝕂] quotientSkewProjection D i (b j)) else 0) =
      TensorProduct.map LinearMap.id (quotientSkewProjection D i) (quotientComul D x) := by
  rw [← extract_finite_negative R (0 : Y →+ ℤ), ← h]
  exact extract_braid_positive R 0 i x

/-- With both actual finite expansions supplied, the source's d_0=c_0 tensor comparison
follows with all positive and negative string indices present before extraction. -/
theorem finite_two_expansions {A B : Type*} (s : Finset A) (t : Finset B) (i : I)
    (x : Quotient D 𝕧) (d : A → 𝕂) (n : A → ℕ) (ν : A → I →₀ ℕ)
    (a b : A → Quotient D 𝕧) (c : B → 𝕂) (m : B → ℕ)
    (a' b' : B → Quotient D 𝕧)
    (hb : ∀ j ∈ t, quotientLDeriv D i (b' j) = 0)
    (hd : braidDelta R 𝕧 ratFunc_X_not_root i (quotientPlus R x) =
      ∑ j ∈ s, d j • negativeSourceTerm R i (n j) (ν j) (a j) (b j))
    (hc : quotientComul D x =
      ∑ j ∈ t, c j • (a' j ⊗ₜ[𝕂] (quotientIntegralGenerator D i (m j) * b' j))) :
    (∑ j ∈ s, if n j = 0 then d j • (a j ⊗ₜ[𝕂] quotientSkewProjection D i (b j)) else 0) =
      ∑ j ∈ t, if m j = 0 then c j • (a' j ⊗ₜ[𝕂] b' j) else 0 := by
  rw [finite_braid_coefficient_identity R s i x d n ν a b hd, hc, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, map_tmul, LinearMap.id_apply, quotientSkewProjection_divided_mul D i _ (hb j hj)]
  split_ifs <;> simp

/-- Reversal changes left strings into right strings. It does not identify P with S P S. -/
theorem reversed_projection_eq_zero_iff (i : I) (x : Quotient D 𝕧) :
    quotientRev D (quotientSkewProjection D i (quotientRev D x)) = 0 ↔
      ∃ y : Quotient D 𝕧, x = y * toQuotient D 𝕧 (θ 𝕂 i) := by
  constructor
  · intro hx
    have hp : quotientSkewProjection D i (quotientRev D x) = 0 := by
      have h := congrArg (quotientRev D) hx
      simpa only [quotientRev_rev, map_zero] using h
    have hm : quotientRev D x ∈ thetaImage D i := by rw [← ker_projection]; exact hp
    obtain ⟨y, hy⟩ := hm
    refine ⟨quotientRev D y, ?_⟩
    have h := congrArg (quotientRev D) hy
    simpa [LinearMap.mulLeft_apply, quotientRev_mul] using h.symm
  · rintro ⟨y, rfl⟩
    simp [quotientRev_mul, projection_theta_mul]

end VermaProjection
