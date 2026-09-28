/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.LusztigF.RatFunc

/-!
# Bar and divided powers: a prerequisite for global bases

This scratch development constructs bar on the generic coefficient field and on the actual
free algebra `'f`. It does not assert existence of a canonical/global basis or descend bar to `f`.

## Main definitions

* `RatFunc.bar`: the coefficient involution, fixing constants and sending `X` to `X⁻¹`.
* `LusztigF.bar`: the semilinear ring involution of `'f`, fixing its generators.

## Main results

* `QuantumGroup.bar_qBinomial`, `QuantumGroup.bar_qFactorial`: invariance at every `X^d`.
* `QuantumGroup.qFactorial_X_pow_ne_zero`: denominators do not vanish when `d > 0`.
* `LusztigF.bar_qDivPow`, `LusztigF.bar_serreElement`: divided powers and relations are fixed.

## References

* Kashiwara, *Global crystal bases of quantum groups*, Duke Math. J. 69 (1993),
  §1.2, equation (1.2.1): bar fixes root generators and inverts the parameter.
* Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §12.3 (bar and divided-power forms),
  Theorems 12.1–12.2 (global bases, NOT proved here).
* Kashiwara, *Crystal bases and categorifications*, arXiv:1809.00114v2, §2, p. 2.

The implementation and all proofs below are reconstructed arguments. Coefficient statements
hold over an arbitrary constant field, but always at the indeterminate, not a scalar specialization.
-/

noncomputable section

namespace RatFunc

variable {K : Type*} [Field K]

private theorem transcendental_X_inv : Transcendental K ((X : RatFunc K)⁻¹) := by
  intro h
  exact transcendental_X (by simpa using h.inv)

/-- Substitution `X ↦ X⁻¹` as an algebra homomorphism over the constant field. -/
def barHom : RatFunc K →ₐ[K] RatFunc K :=
  (IntermediateField.val _).comp
    (algEquivOfTranscendental (X⁻¹ : RatFunc K) transcendental_X_inv).toAlgHom

@[simp] theorem barHom_X : barHom (X : RatFunc K) = X⁻¹ := by
  exact algEquivOfTranscendental_X _ _

/-- The substitution is involutive. Reconstructed from the fraction-field universal property. -/
theorem barHom_involutive : Function.Involutive (barHom (K := K)) := by
  have h : (barHom (K := K)).comp barHom = AlgHom.id K (RatFunc K) := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    change barHom (barHom (X : RatFunc K)) = X
    simp
  intro x
  exact DFunLike.congr_fun h x

/-- The coefficient-field bar involution, linear over `K`, not over `K(X)`.
This constructs the coefficient operation required in Kashiwara, §2, p. 2. -/
def bar : RatFunc K ≃ₐ[K] RatFunc K :=
  AlgEquiv.ofAlgHom barHom barHom
    (by ext x; exact barHom_involutive x) (by ext x; exact barHom_involutive x)

@[simp] theorem bar_X : bar (X : RatFunc K) = X⁻¹ := barHom_X

@[simp] theorem bar_bar (x : RatFunc K) : bar (bar x) = x := barHom_involutive x

end RatFunc

namespace QuantumGroup

variable {K : Type*} [Field K]

/-- The symmetric q-binomial coefficients at `X^d` are fixed by the coefficient bar.
Reconstructed from the Pascal recurrence and the existing `qBinomial_inv`. -/
theorem bar_qBinomial (d n j : ℕ) :
    RatFunc.bar (qBinomial ((RatFunc.X : RatFunc K) ^ d) n j) =
      qBinomial (RatFunc.X ^ d) n j := by
  have h (n j : ℕ) :
      RatFunc.bar (qBinomial ((RatFunc.X : RatFunc K) ^ d) n j) =
        qBinomial ((RatFunc.X : RatFunc K) ^ d)⁻¹ n j := by
    induction n generalizing j with
    | zero => cases j <;> simp
    | succ n ih =>
      cases j with
      | zero => simp
      | succ j => simp only [qBinomial_succ_succ, map_add, map_mul, map_pow,
          map_inv₀, RatFunc.bar_X, ih, inv_pow]
  rw [h, qBinomial_inv]

/-- The quantum factorials used in divided powers are bar-fixed. -/
theorem bar_qFactorial (d n : ℕ) :
    RatFunc.bar (qFactorial ((RatFunc.X : RatFunc K) ^ d) n) =
      qFactorial (RatFunc.X ^ d) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ, map_mul, ← qBinomial_one_right, bar_qBinomial,
      qBinomial_one_right, ih]

/-- In particular the inverse factorial coefficient of a divided power is bar-fixed. -/
theorem bar_inv_qFactorial (d n : ℕ) :
    RatFunc.bar ((qFactorial ((RatFunc.X : RatFunc K) ^ d) n)⁻¹) =
      (qFactorial (RatFunc.X ^ d) n)⁻¹ := by
  rw [map_inv₀, bar_qFactorial]

/-- The divided-power denominators are nonzero for each positive symmetrizer exponent.
This is the generic parameter case, not a claim at arbitrary scalar specializations. -/
theorem qFactorial_X_pow_ne_zero (d n : ℕ) (hd : 0 < d) :
    qFactorial ((RatFunc.X : RatFunc K) ^ d) n ≠ 0 := by
  apply qFactorial_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero)
  intro m hm _
  rw [← pow_mul]
  exact LusztigF.ratFunc_X_pow_ne_one (Nat.mul_pos hd (by omega))

end QuantumGroup

namespace LusztigF

variable {K I : Type*} [Field K]

/-- The semilinear bar on the actual free algebra `'f`: fix generators and bar coefficients.
Reconstructed using Mathlib's monoid-algebra model. This has not yet descended to `f`. -/
def bar : LusztigF (RatFunc K) I ≃+* LusztigF (RatFunc K) I :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.toRingEquiv.trans
    ((MonoidAlgebra.mapRingEquiv (FreeMonoid I) RatFunc.bar.toRingEquiv).trans
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toRingEquiv.symm)

@[simp] theorem bar_bar (x : LusztigF (RatFunc K) I) : bar (bar x) = x := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  ext w
  simp [bar]

@[simp] theorem bar_θ (i : I) : bar (θ (RatFunc K) i) = θ (RatFunc K) i := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  simp [bar, θ, FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply]

@[simp] theorem bar_algebraMap (c : RatFunc K) :
    bar (algebraMap (RatFunc K) (LusztigF (RatFunc K) I) c) =
      algebraMap (RatFunc K) _ (RatFunc.bar c) := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  simp [bar]

/-- Semilinearity is with respect to coefficient inversion, not the identity of `K(X)`. -/
theorem bar_smul (c : RatFunc K) (x : LusztigF (RatFunc K) I) :
    bar (c • x) = RatFunc.bar c • bar x := by
  simp only [Algebra.smul_def, map_mul, bar_algebraMap]

/-- All generator divided powers are bar-fixed, including non-simply-laced parameters `X^d`.
This verifies the coefficient/generator bridge; it does not assert that they form a basis. -/
theorem bar_qDivPow (d n : ℕ) (i : I) :
    bar (QuantumGroup.qDivPow ((RatFunc.X : RatFunc K) ^ d) n (θ (RatFunc K) i)) =
      QuantumGroup.qDivPow ((RatFunc.X : RatFunc K) ^ d) n (θ (RatFunc K) i) := by
  simp [QuantumGroup.qDivPow, bar_smul, QuantumGroup.bar_qFactorial]

/-- The defining divided-power Serre elements are bar-fixed for every Cartan datum.
This is the explicit relation-level bridge needed before descending bar to the quotient;
it uses no braid automorphism or global-basis existence hypothesis. -/
theorem bar_serreElement (D : LusztigCartanDatum I) (i j : I) :
    bar (serreElement D (RatFunc.X : RatFunc K) i j) =
      serreElement D (RatFunc.X : RatFunc K) i j := by
  simp [serreElement, QuantumGroup.qSerreDiv, bar_smul, bar_qDivPow]

end LusztigF
