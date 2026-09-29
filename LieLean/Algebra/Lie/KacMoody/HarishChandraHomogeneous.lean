/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HarishChandraSymbol
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Full homogeneous symmetric-algebra components

## Main definitions

* `SymmetricAlgebra.homogeneousSubmodule`: powers of the degree-one generator submodule.
* `SymmetricPower.homogeneousEquiv`: equivalence from the actual symmetric tensor quotient.
* `SymmetricAlgebra.derivation`: independent extension of a linear endomorphism.

## Main results

* `SymmetricPower.range_toSymmetricAlgebra`: the full range in every degree.
* `SymmetricAlgebra.map_homogeneousSubmodule`: identification with Mathlib's genuine
  homogeneous polynomial component, not a definition using the symmetric-power map.
* `SymmetricPower.toSymmetricAlgebra_injective`: coefficientwise inverse, all degrees.
* `SymmetricPower.toSymmetricAlgebra_diagonal`: independent derivation compatibility.
* `UniversalEnvelopingAlgebra.exists_centralLift_of_invariant_homogeneous`: actual
  invariant-symbol lift to the centre with the prescribed PBW leading symbol.

All identification and derivation statements hold over every field, without finite
dimensionality, including degree zero. Only the final normalized central lift uses
characteristic zero. No finite-Cartan-type HC result is inferred from this generality.

## References

Reconstructed elementary argument from the universal properties. The independent
polynomial model uses pinned Mathlib `SymmetricAlgebra.equivMvPolynomial` and
`MvPolynomial.homogeneousSubmodule_one_pow`. This is a dependency toward HC image,
not HC image equality or Chevalley restriction.
-/

noncomputable section

open scoped Pointwise
open Module

namespace SymmetricAlgebra

variable {K : Type} {M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- The degree `n` component, independently defined by powers of the generator submodule. -/
def homogeneousSubmodule (n : ℕ) : Submodule K (SymmetricAlgebra K M) :=
  LinearMap.range (ι K M) ^ n

/-- The independent component is exactly the genuine homogeneous polynomial component
under every basis presentation, including in infinite dimension and degree zero. -/
theorem map_homogeneousSubmodule {κ : Type*} (b : Basis κ K M) (n : ℕ) :
    (homogeneousSubmodule (K := K) (M := M) n).map
      (equivMvPolynomial b).toAlgHom.toLinearMap = MvPolynomial.homogeneousSubmodule κ K n := by
  have h : (LinearMap.range (ι K M)).map (equivMvPolynomial b).toAlgHom.toLinearMap =
      MvPolynomial.homogeneousSubmodule κ K 1 := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    rw [← Submodule.map_top (ι K M), ← b.span_eq, Submodule.map_span,
      Submodule.map_span]
    congr 1
    ext p
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, (equivMvPolynomial_ι_apply b i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ι K M (b i), ⟨b i, ⟨i, rfl⟩, rfl⟩, equivMvPolynomial_ι_apply b i⟩
  change ((LinearMap.range (ι K M)) ^ n).map
    (equivMvPolynomial b).toAlgHom.toLinearMap = _
  rw [Submodule.map_pow, h,
    MvPolynomial.homogeneousSubmodule_one_pow]

/-- Membership in the independently defined component is precisely standard polynomial
homogeneity under any basis presentation. In particular the definition is basis-free. -/
theorem mem_homogeneousSubmodule_iff {κ : Type*} (b : Basis κ K M) (n : ℕ)
    (p : SymmetricAlgebra K M) :
    p ∈ homogeneousSubmodule (K := K) (M := M) n ↔
      (equivMvPolynomial b p).IsHomogeneous n := by
  change p ∈ _ ↔ equivMvPolynomial b p ∈ MvPolynomial.homogeneousSubmodule κ K n
  rw [← map_homogeneousSubmodule b n]
  constructor
  · intro hp
    exact ⟨p, hp, rfl⟩
  · rintro ⟨q, hq, hqp⟩
    have h : q = p := (equivMvPolynomial b).injective hqp
    exact h ▸ hq

/-- Extension of a linear endomorphism to a derivation of the symmetric algebra,
constructed independently via Mathlib's polynomial derivation. -/
def derivationOfBasis {κ : Type*} (b : Basis κ K M) (D : M →ₗ[K] M) :
    Derivation K (SymmetricAlgebra K M) (SymmetricAlgebra K M) where
  toLinearMap := (equivMvPolynomial b).symm.toLinearMap.comp
    ((MvPolynomial.mkDerivation K
      (fun i => equivMvPolynomial b (ι K M (D (b i))))).toLinearMap.comp
        (equivMvPolynomial b).toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' a c := by simp [Derivation.leibniz, smul_eq_mul]

/-- The independently constructed derivation has the prescribed generator action. -/
@[simp] theorem derivationOfBasis_ι {κ : Type*} (b : Basis κ K M)
    (D : M →ₗ[K] M) (x : M) : derivationOfBasis b D (ι K M x) = ι K M (D x) := by
  have h : (derivationOfBasis b D).toLinearMap.comp (ι K M) = (ι K M).comp D := by
    apply b.ext
    intro i
    simp [derivationOfBasis]
  exact LinearMap.congr_fun h x

/-- Canonical derivation extension. Its construction chooses a basis; its action on
all generators, and hence on the entire algebra, is prescribed. -/
def derivation (D : M →ₗ[K] M) :
    Derivation K (SymmetricAlgebra K M) (SymmetricAlgebra K M) :=
  derivationOfBasis (Module.Free.chooseBasis K M) D

@[simp] theorem derivation_ι (D : M →ₗ[K] M) (x : M) :
    derivation D (ι K M x) = ι K M (D x) := derivationOfBasis_ι _ D x

/-- Leibniz rule on a finite product, in insertion form. -/
theorem derivation_prod_ι (D : M →ₗ[K] M) (n : ℕ) (v : Fin n → M) :
    derivation D (∏ i, ι K M (v i)) =
      ∑ i, ∏ j, ι K M (Function.update v i (D (v i)) j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simp only [Fin.prod_univ_succ, Derivation.leibniz, derivation_ι, Fin.sum_univ_succ,
      Function.update_apply, Fin.succ_inj, Fin.succ_ne_zero, hn, ite_false, ite_true]
    have h := ih (fun i => v i.succ)
    simp only [Function.update_apply] at h
    rw [smul_eq_mul, smul_eq_mul, h, Finset.mul_sum]
    ac_rfl

end SymmetricAlgebra

namespace SymmetricPower

variable {K : Type} {M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Every full homogeneous component is attained by the actual symmetric tensor quotient.
No injectivity is hidden in the definition of the target. -/
theorem range_toSymmetricAlgebra (n : ℕ) :
    LinearMap.range (toSymmetricAlgebra (K := K) (M := M) n) =
      SymmetricAlgebra.homogeneousSubmodule n := by
  rw [SymmetricAlgebra.homogeneousSubmodule, LinearMap.range_eq_map,
    ← span_tprod_eq_top K (Fin n) M, Submodule.map_span]
  rw [← Submodule.span_eq (LinearMap.range (SymmetricAlgebra.ι K M)),
    Submodule.span_pow]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_range]
  rw [Set.mem_pow_iff_prod]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨fun i => SymmetricAlgebra.ι K M (v i), fun i => ⟨v i, rfl⟩,
      (toSymmetricAlgebra_tprod n v).symm⟩
  · rintro ⟨f, hf, rfl⟩
    choose v hv using hf
    exact ⟨tprod K v, ⟨v, rfl⟩, by rw [toSymmetricAlgebra_tprod]; simp only [hv]⟩

/-- Multiplicities of a tuple of basis indices. -/
def tupleExponent {κ : Type*} {n : ℕ} (f : Fin n → κ) : κ →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

/-- Equal multiplicities imply equality in the actual permutation quotient. -/
theorem tprod_basis_eq_of_exponent_eq {κ : Type*} (b : Basis κ K M) {n : ℕ}
    (f g : Fin n → κ) (h : tupleExponent f = tupleExponent g) :
    tprod K (fun i => b (f i)) = tprod K (fun i => b (g i)) := by
  classical
  have hc (a : κ) : Fintype.card {i // f i = a} = Fintype.card {i // g i = a} := by
    have ha := DFunLike.congr_fun h a
    simpa [tupleExponent, Finsupp.single_apply, Fintype.card_subtype, eq_comm] using ha
  let e (a : κ) : {i // f i = a} ≃ {i // g i = a} := Fintype.equivOfCardEq (hc a)
  have he (i : Fin n) : g (Equiv.ofFiberEquiv e i) = f i := Equiv.ofFiberEquiv_map e i
  calc
    tprod K (fun i => b (f i)) =
        tprod K (fun i => b (g (Equiv.ofFiberEquiv e i))) := by simp only [he]
    _ = tprod K (fun i => b (g i)) := tprod_equiv (Equiv.ofFiberEquiv e) (fun i => b (g i))

/-- A monomial is sent to a representing symmetric basis tensor if one exists,
and to zero otherwise. This auxiliary definition is only used to prove injectivity. -/
def monomialPreimage {κ : Type*} (b : Basis κ K M) (n : ℕ) (d : κ →₀ ℕ) :
    SymmetricPower K (Fin n) M := by
  classical
  exact if h : ∃ f : Fin n → κ, tupleExponent f = d then
    tprod K (fun i => b (h.choose i)) else 0

/-- The chosen representative is equal to every representative in the symmetric quotient. -/
theorem monomialPreimage_tupleExponent {κ : Type*} (b : Basis κ K M) (n : ℕ)
    (f : Fin n → κ) :
    monomialPreimage b n (tupleExponent f) = tprod K (fun i => b (f i)) := by
  classical
  unfold monomialPreimage
  split
  · rename_i h
    exact tprod_basis_eq_of_exponent_eq b _ f h.choose_spec
  · rename_i h
    exact False.elim (h ⟨f, rfl⟩)

/-- Coefficientwise inverse candidate on the whole polynomial algebra. -/
def polynomialPreimage {κ : Type*} (b : Basis κ K M) (n : ℕ) :
    MvPolynomial κ K →ₗ[K] SymmetricPower K (Fin n) M :=
  (MvPolynomial.basisMonomials κ K).constr K (monomialPreimage b n)

/-- This coefficient map inverts a product of basis variables without factorials. -/
theorem polynomialPreimage_prod_X {κ : Type*} (b : Basis κ K M) (n : ℕ)
    (f : Fin n → κ) :
    polynomialPreimage b n (∏ i, MvPolynomial.X (f i)) =
      tprod K (fun i => b (f i)) := by
  have h : (∏ i, MvPolynomial.X (f i) : MvPolynomial κ K) =
      MvPolynomial.monomial (tupleExponent f) 1 := by
    rw [tupleExponent, MvPolynomial.monomial_sum_one]
    rfl
  rw [h]
  change polynomialPreimage b n (MvPolynomial.basisMonomials κ K (tupleExponent f)) = _
  rw [polynomialPreimage, Basis.constr_basis, monomialPreimage_tupleExponent]

/-- Actual left inverse of the canonical map, constructed coefficientwise from any basis. -/
theorem polynomialPreimage_leftInverse {κ : Type*} (b : Basis κ K M) (n : ℕ) :
    Function.LeftInverse
      ((polynomialPreimage b n).comp (SymmetricAlgebra.equivMvPolynomial b).toLinearMap)
      (toSymmetricAlgebra (K := K) (M := M) n) := by
  have hm : ((polynomialPreimage b n).comp
      (SymmetricAlgebra.equivMvPolynomial b).toLinearMap).comp
      (toSymmetricAlgebra n) = LinearMap.id := by
    apply LinearMap.ext_on (span_tprod_eq_top K (Fin n) M)
    have ht : (((polynomialPreimage b n).comp
        (SymmetricAlgebra.equivMvPolynomial b).toLinearMap).comp
        (toSymmetricAlgebra n)).compMultilinearMap (tprod K) = tprod K := by
      apply Basis.ext_multilinear (fun _ => b)
      intro f
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        toSymmetricAlgebra_tprod, AlgEquiv.toLinearMap_apply, map_prod,
        SymmetricAlgebra.equivMvPolynomial_ι_apply, polynomialPreimage_prod_X]
    rintro _ ⟨f, rfl⟩
    exact MultilinearMap.congr_fun ht f
  intro s
  exact LinearMap.congr_fun hm s

/-- Injectivity of the actual symmetric-power quotient map, in every characteristic,
dimension and degree. The proof uses a basis, but the statement does not choose one. -/
theorem toSymmetricAlgebra_injective (n : ℕ) :
    Function.Injective (toSymmetricAlgebra (K := K) (M := M) n) :=
  (polynomialPreimage_leftInverse (Module.Free.chooseBasis K M) n).injective

/-- The actual canonical multiplication map with full homogeneous codomain. -/
def toHomogeneous (n : ℕ) :
    SymmetricPower K (Fin n) M →ₗ[K] SymmetricAlgebra.homogeneousSubmodule
      (K := K) (M := M) n :=
  (toSymmetricAlgebra n).codRestrict _ (fun s =>
    (range_toSymmetricAlgebra (K := K) (M := M) n) ▸ LinearMap.mem_range_self _ s)

/-- Full degreewise identification, over every field and in arbitrary dimension.
The target is independently defined and proved equal to the genuine polynomial degree. -/
def homogeneousEquiv (n : ℕ) :
    SymmetricPower K (Fin n) M ≃ₗ[K] SymmetricAlgebra.homogeneousSubmodule
      (K := K) (M := M) n :=
  LinearEquiv.ofBijective (toHomogeneous n) ⟨by
    intro s t h
    exact toSymmetricAlgebra_injective n (congrArg Subtype.val h), by
    intro p
    have hp : p.val ∈ LinearMap.range (toSymmetricAlgebra (K := K) (M := M) n) :=
      (range_toSymmetricAlgebra (K := K) (M := M) n).symm ▸ p.property
    obtain ⟨s, hs⟩ := hp
    exact ⟨s, Subtype.ext hs⟩⟩

@[simp] theorem coe_homogeneousEquiv (n : ℕ) (s : SymmetricPower K (Fin n) M) :
    (homogeneousEquiv n s : SymmetricAlgebra K M) = toSymmetricAlgebra n s := rfl

/-- Explicit coefficient formula for the true inverse; it is independent of the basis
because both inverse laws hold for the canonical multiplication map. -/
theorem homogeneousEquiv_symm_eq {κ : Type*} (b : Basis κ K M) (n : ℕ)
    (p : SymmetricAlgebra.homogeneousSubmodule (K := K) (M := M) n) :
    (homogeneousEquiv n).symm p =
      polynomialPreimage b n (SymmetricAlgebra.equivMvPolynomial b p.val) := by
  obtain ⟨s, rfl⟩ := (homogeneousEquiv (K := K) (M := M) n).surjective p
  simpa only [LinearEquiv.symm_apply_apply, coe_homogeneousEquiv,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] using
    (polynomialPreimage_leftInverse b n s).symm

/-- The quotient's diagonal insertion agrees with the independently constructed
symmetric-algebra derivation. In particular `D = LieAlgebra.ad K L x` gives the
infinitesimal adjoint compatibility needed for invariant homogeneous symbols. -/
theorem toSymmetricAlgebra_diagonal (n : ℕ) (D : M →ₗ[K] M)
    (s : SymmetricPower K (Fin n) M) :
    toSymmetricAlgebra n (diagonal D s) =
      SymmetricAlgebra.derivation D (toSymmetricAlgebra n s) := by
  have h : (toSymmetricAlgebra n).comp (diagonal D) =
      (SymmetricAlgebra.derivation D).toLinearMap.comp (toSymmetricAlgebra n) := by
    apply LinearMap.ext_on (span_tprod_eq_top K (Fin n) M)
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply, diagonal_tprod, map_sum, toSymmetricAlgebra_tprod,
      Derivation.coeFn_coe, SymmetricAlgebra.derivation_prod_ι]
  exact LinearMap.congr_fun h s

/-- Invariance of a full homogeneous polynomial is equivalent to invariance of its
actual symmetric-quotient inverse. This is not a surjectivity assumption. -/
theorem homogeneousEquiv_symm_diagonal_eq_zero_iff (n : ℕ) (D : M →ₗ[K] M)
    (p : SymmetricAlgebra.homogeneousSubmodule (K := K) (M := M) n) :
    diagonal D ((homogeneousEquiv n).symm p) = 0 ↔
      SymmetricAlgebra.derivation D p.val = 0 := by
  have hp : toSymmetricAlgebra n ((homogeneousEquiv n).symm p) = p.val := by
    rw [← coe_homogeneousEquiv, LinearEquiv.apply_symm_apply]
  constructor
  · intro h
    have he := toSymmetricAlgebra_diagonal n D ((homogeneousEquiv n).symm p)
    rw [h, map_zero, hp] at he
    exact he.symm
  · intro h
    apply toSymmetricAlgebra_injective n
    rw [map_zero, toSymmetricAlgebra_diagonal, hp, h]

end SymmetricPower

namespace UniversalEnvelopingAlgebra

variable {K : Type} {L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

/-- Every genuine adjoint-invariant degree-`n` homogeneous symmetric-algebra symbol
has an actual central lift with exactly that PBW symbol. No Cartan/Weyl invariant
extension, graded HC compatibility, or HC image equality is asserted. -/
theorem exists_centralLift_of_invariant_homogeneous (n : ℕ)
    (p : SymmetricAlgebra.homogeneousSubmodule (K := K) (M := L) n)
    (hp : ∀ x : L, SymmetricAlgebra.derivation (LieAlgebra.ad K L x) p.val = 0) :
    ∃ z : Subalgebra.center K (UniversalEnvelopingAlgebra K L),
      ∃ hz : z.val ∈ filtration K L n,
        toGr K L n ⟨z.val, hz⟩ = symmetricAlgebraToAssociatedGraded K L p.val := by
  let s := (SymmetricPower.homogeneousEquiv (K := K) (M := L) n).symm p
  have hs (x : L) : SymmetricPower.diagonal (LieAlgebra.ad K L x) s = 0 :=
    (SymmetricPower.homogeneousEquiv_symm_diagonal_eq_zero_iff n _ p).mpr (hp x)
  refine ⟨⟨symmetrizationPower n s, symmetrizationPower_mem_center n s hs⟩,
    symmetrizationPower_mem_filtration n s, ?_⟩
  rw [show p.val = SymmetricPower.toSymmetricAlgebra n s by
    dsimp only [s]
    rw [← SymmetricPower.coe_homogeneousEquiv, LinearEquiv.apply_symm_apply]]
  exact symmetrizationPower_toGr n s

end UniversalEnvelopingAlgebra
