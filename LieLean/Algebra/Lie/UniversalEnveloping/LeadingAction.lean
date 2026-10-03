/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.Filtration

/-!
# Leading polynomial action of left multiplication under PBW

## Main results

Left multiplication by a Lie algebra basis generator agrees under the actual ordered PBW
isomorphism with polynomial multiplication by the matching variable, modulo lower degree.
This is the coefficient-level input for identifying the associated-graded regular CE
complex with a polynomial Koszul complex, not that entire chain-level identification.

## References

Reconstructed from the proved PBW properties `PBW.rho_sub_mem` and `PBW.phi_lift`.
-/

open Module MvPolynomial Finsupp

noncomputable section
namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L σ : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LinearOrder σ] (b : Basis σ R L)

/-- Under PBW, left multiplication is the constructed polynomial representation, not the
adjoint action. Reconstructed directly from the definition of the PBW equivalence. -/
theorem pbwEquiv_ι_mul (x : L) (u : UniversalEnvelopingAlgebra R L) :
    pbwEquiv b (ι R x * u) = PBW.rho b x (pbwEquiv b u) := by
  change (lift R (PBW.rhoHom b) (ι R x * u)) 1 =
    PBW.rho b x ((lift R (PBW.rhoHom b) u) 1)
  rw [map_mul, Module.End.mul_apply, lift_ι_apply, PBW.rhoHom_apply]

/-- For any polynomial of degree at most `n`, the difference between the PBW action of a
basis generator and multiplication by its variable has degree at most `n`.
Reconstructed by linear extension of the monomial PBW property. -/
theorem rho_sub_X_mul_mem (i : σ) (n : ℕ) {p : MvPolynomial σ R}
    (hp : p ∈ restrictTotalDegree σ R n) :
    PBW.rho b (b i) p - X i * p ∈ restrictTotalDegree σ R n := by
  rw [restrictTotalDegree, restrictSupport_eq_span] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨s, hs, rfl⟩ := hp
    simpa [PBW.z, X, monomial_mul_monomial, add_comm] using
      PBW.restrictTotalDegree_mono hs (PBW.rho_sub_mem b i s)
  | zero => simp
  | add p q _ _ hp hq =>
    rw [map_add, mul_add, add_sub_add_comm]
    exact add_mem hp hq
  | smul r p _ hp =>
    rw [map_smul, mul_smul_comm, ← smul_sub]
    exact Submodule.smul_mem _ _ hp

/-- The leading PBW symbol of actual left multiplication is polynomial multiplication.
The error has one less total degree than the natural `n+1` bound for the product.
No finite-dimensionality or characteristic-zero hypothesis is used. -/
theorem pbwEquiv_ι_basis_mul_sub_mem (i : σ) (n : ℕ)
    {u : UniversalEnvelopingAlgebra R L} (hu : u ∈ filtration R L n) :
    pbwEquiv b (ι R (b i) * u) - X i * pbwEquiv b u ∈ restrictTotalDegree σ R n := by
  rw [pbwEquiv_ι_mul]
  exact rho_sub_X_mul_mem b i n ((mem_filtration_iff_pbwEquiv b).mp hu)

/-- For an arbitrary Lie algebra element, PBW intertwines left multiplication with
multiplication by its degree-one polynomial modulo lower degree. Reconstructed by basis
linearity from `pbwEquiv_ι_basis_mul_sub_mem`. -/
theorem pbwEquiv_ι_mul_sub_mem (x : L) (n : ℕ)
    {u : UniversalEnvelopingAlgebra R L} (hu : u ∈ filtration R L n) :
    pbwEquiv b (ι R x * u) - pbwEquiv b (ι R x) * pbwEquiv b u ∈
      restrictTotalDegree σ R n := by
  let e := (pbwEquiv b).toLinearMap
  let j := (ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L).toLinearMap
  let D : L →ₗ[R] MvPolynomial σ R :=
    e ∘ₗ (LinearMap.mulRight R u) ∘ₗ j -
      (LinearMap.mulRight R (pbwEquiv b u)) ∘ₗ e ∘ₗ j
  change D x ∈ restrictTotalDegree σ R n
  induction b.mem_span x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    change pbwEquiv b (ι R (b i) * u) - pbwEquiv b (ι R (b i)) * pbwEquiv b u ∈ _
    rw [pbwEquiv_ι_basis]
    exact pbwEquiv_ι_basis_mul_sub_mem b i n hu
  | zero => simpa only [map_zero] using (restrictTotalDegree σ R n).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul r x _ hx =>
    rw [map_smul]
    exact (restrictTotalDegree σ R n).smul_mem r hx

end UniversalEnvelopingAlgebra
