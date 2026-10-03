/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Sl2.CrystalLattice
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Residue basis and rational balanced triple in rank one

## Main definitions
* `residue`: evaluation at zero on the genuine localization `ℚ[X]_(X)`.
* `ResidueSpace`, `residueBasis`: the actual quotient `L / X L` and its divided-power basis.
* `laurentForm`, `tripleLattice`: the genuine Laurent form and its intersection with
  the local lattice and its bar image.
* `balancedEquiv`, `globalBasis`: the proved quotient isomorphism and its unique basis lifts.

## Main results
* `residue_eq_zero_iff`, `latticeResidue_ker`: the scalar and lattice kernels are exactly
  multiplication by `X`, not a kernel substituted by definition for the intended submodule.
* `scalar_laurent_intersection`: Laurent functions regular at zero and infinity are constants.
* `tripleProjection_bijective`: balancedness of the actual triple intersection.
* `globalLift_coe`, `globalLift_unique`: unique lifts are the represented `F^(j)` vectors.
* `residueLower_basis`, `residueRaise_basis`: the descended actual operators have the
  rank-one crystal-string action on the quotient basis, including both boundaries.

## References and scope
Reconstructed elementary localization, valuation and basis arguments, guided by the
rank-one target of Kashiwara, *On crystal bases*, §§12.2–12.3; the arguments are
our own. No residue basis or balancedness is assumed.

This is only the positive type-1 `simpleRep X n 1` over `ℚ(X)`, for every natural `n`.
The Laurent form is rational `ℚ[X,X⁻¹]`, not the integer integral form. No general-rank
canonical basis, integer integral basis, or full quantum-algebra bar is asserted.
The local lattice is not bar-stable; only the displayed global vectors are bar-fixed.
-/
noncomputable section
namespace QuantumGroup.Sl2.RankOne

/-- Evaluation at zero sends every allowed denominator to a unit. -/
theorem evalZero_denominator (s : (Polynomial.idealX ℚ).asIdeal.primeCompl) :
    IsUnit (Polynomial.evalRingHom (0 : ℚ) s) := by
  apply isUnit_iff_ne_zero.mpr
  have hs := s.property
  simpa only [Ideal.mem_primeCompl_iff, Polynomial.idealX_span,
    Ideal.mem_span_singleton, Polynomial.X_dvd_iff,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.coe_evalRingHom] using hs

/-- The genuine residue map on `ℚ[X]_(X)`, constructed by localization. -/
def residue : LocalRing →+* ℚ := IsLocalization.lift evalZero_denominator

@[simp] theorem residue_polynomial (p : Polynomial ℚ) :
    residue (algebraMap (Polynomial ℚ) LocalRing p) = p.eval 0 :=
  IsLocalization.lift_eq evalZero_denominator p

/-- The local parameter is the actual polynomial indeterminate. -/
def localX : LocalRing := algebraMap (Polynomial ℚ) LocalRing Polynomial.X

@[simp] theorem residue_localX : residue localX = 0 := by simp [localX]

/-- The residue map has exactly the principal ideal `(X)` as its kernel. -/
theorem residue_eq_zero_iff (x : LocalRing) :
    residue x = 0 ↔ ∃ y : LocalRing, x = localX * y := by
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (Polynomial.idealX ℚ).asIdeal.primeCompl x
  constructor
  · intro h
    have hp : p.eval 0 = 0 := by
      have he := (IsLocalization.lift_mk'_spec evalZero_denominator p 0 s).mp h
      simpa using he
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr
      (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hp)
    refine ⟨IsLocalization.mk' LocalRing q s, ?_⟩
    exact (IsLocalization.mul_mk'_eq_mk'_of_mul (S := LocalRing) Polynomial.X q s).symm
  · rintro ⟨y, h⟩
    rw [h, map_mul, residue_localX, zero_mul]

/-- The local ring carries its natural rational-constant algebra structure. -/
instance localRationalAlgebra : Algebra ℚ LocalRing :=
  ((algebraMap (Polynomial ℚ) LocalRing).comp Polynomial.C).toAlgebra

instance localRationalTower : IsScalarTower ℚ (Polynomial ℚ) LocalRing :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance latticeRationalModule (n : ℕ) : Module ℚ (lattice n) :=
  Module.compHom _ (algebraMap ℚ LocalRing)

instance latticeRationalTower (n : ℕ) : IsScalarTower ℚ LocalRing (lattice n) :=
  IsScalarTower.of_compHom ℚ LocalRing (lattice n)

/-- Constants in the residue map retain their original values. -/
@[simp] theorem residue_rat (c : ℚ) : residue (algebraMap ℚ LocalRing c) = c := by
  change residue (algebraMap (Polynomial ℚ) LocalRing (Polynomial.C c)) = c
  simp

/-- Coordinatewise specialization in the genuine free lattice. -/
def latticeResidue (n : ℕ) : lattice n →ₗ[ℚ] (Fin (n + 1) → ℚ) where
  toFun x j := residue ((latticeBasis n).repr x j)
  map_add' x y := by ext j; simp
  map_smul' c x := by
    ext j
    change residue ((latticeBasis n).repr ((algebraMap ℚ LocalRing c) • x) j) = _
    rw [map_smul]
    change residue ((algebraMap ℚ LocalRing c) * (latticeBasis n).repr x j) = _
    rw [map_mul, residue_rat]
    rfl

/-- Constant-coordinate lift of residue vectors. -/
def constantLift (n : ℕ) (c : Fin (n + 1) → ℚ) : lattice n :=
  ∑ j, (algebraMap ℚ LocalRing (c j)) • latticeBasis n j

@[simp] theorem latticeResidue_constantLift (n : ℕ) (c : Fin (n + 1) → ℚ) :
    latticeResidue n (constantLift n c) = c := by
  ext j
  simp [latticeResidue, constantLift, Finsupp.single_apply]

/-- Specialization is onto, by actual constant divided-power combinations. -/
theorem latticeResidue_surjective (n : ℕ) : Function.Surjective (latticeResidue n) :=
  fun c ↦ ⟨constantLift n c, latticeResidue_constantLift n c⟩

/-- Exact kernel formula: reduction kills precisely `X` times the actual lattice. -/
theorem latticeResidue_eq_zero_iff (n : ℕ) (x : lattice n) :
    latticeResidue n x = 0 ↔ ∃ y : lattice n, x = localX • y := by
  constructor
  · intro hx
    have h : ∀ j, ∃ y : LocalRing, (latticeBasis n).repr x j = localX * y := by
      intro j
      apply (residue_eq_zero_iff _).mp
      exact congrFun hx j
    choose c hc using h
    refine ⟨∑ j, c j • latticeBasis n j, ?_⟩
    apply (latticeBasis n).repr.injective
    apply DFunLike.ext
    intro j
    simpa [Finsupp.single_apply] using hc j
  · rintro ⟨y, rfl⟩
    ext j
    simp [latticeResidue]

/-- Multiplication by the actual local parameter, as a rational-linear map. -/
def latticeParameter (n : ℕ) : lattice n →ₗ[ℚ] lattice n where
  toFun x := localX • x
  map_add' x y := smul_add _ _ _
  map_smul' c x := by
    change localX • ((algebraMap ℚ LocalRing c) • x) =
      (algebraMap ℚ LocalRing c) • (localX • x)
    exact smul_comm _ _ _

/-- The submodule `X L`, defined by multiplication rather than by the residue kernel. -/
def xLattice (n : ℕ) : Submodule ℚ (lattice n) := (latticeParameter n).range

/-- The kernel computation identifies the actual quotient `L / X L`. -/
theorem latticeResidue_ker (n : ℕ) : (latticeResidue n).ker = xLattice n := by
  ext x
  change latticeResidue n x = 0 ↔ ∃ y, localX • y = x
  rw [latticeResidue_eq_zero_iff]
  simp only [eq_comm]

/-- The actual residue quotient of the local lattice. -/
abbrev ResidueSpace (n : ℕ) := lattice n ⧸ xLattice n

/-- Specialization induces an isomorphism of the quotient with rational coordinates. -/
def residueEquiv (n : ℕ) : ResidueSpace n ≃ₗ[ℚ] (Fin (n + 1) → ℚ) :=
  (Submodule.quotEquivOfEq _ _ (latticeResidue_ker n).symm).trans
    ((latticeResidue n).quotKerEquivOfSurjective (latticeResidue_surjective n))

@[simp] theorem residueEquiv_mk (n : ℕ) (x : lattice n) :
    residueEquiv n (Submodule.Quotient.mk x) = latticeResidue n x := rfl

/-- The actual residue classes of the divided-power basis form a rational basis. -/
def residueBasis (n : ℕ) : Module.Basis (Fin (n + 1)) ℚ (ResidueSpace n) :=
  (Pi.basisFun ℚ (Fin (n + 1))).map (residueEquiv n).symm

@[simp] theorem residueBasis_eq (n : ℕ) (j : Fin (n + 1)) :
    residueBasis n j = Submodule.Quotient.mk (latticeBasis n j) := by
  apply (residueEquiv n).injective
  ext k
  simp [residueBasis, latticeResidue, Pi.single_apply, Finsupp.single_apply, eq_comm]

end QuantumGroup.Sl2.RankOne
noncomputable section
-- Prefer the generic constant-field algebra to the competing rational-cast algebra.
attribute [local instance 1100] RatFunc.instAlgebraOfPolynomial
namespace QuantumGroup.Sl2.RankOne
open IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

abbrev zeroValuation := (Polynomial.idealX ℚ).valuation Coeff

lemma local_mem_valuation {x : Coeff} (hx : x ∈ LocalRing) : zeroValuation x ≤ 1 := by
  exact valuationSubringAtPrime_le_valuation (Polynomial.idealX ℚ) hx

lemma zeroValuation_X_lt_one : zeroValuation (RatFunc.X : Coeff) < 1 := by
  rw [Polynomial.valuation_X_eq_neg_one]
  norm_num

instance zeroValuation_trivial : zeroValuation.IsTrivialOn ℚ where
  eq_one c hc := by
    rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C, valuation_of_algebraMap]
    apply intValuation_eq_one_iff.mpr
    simpa [Polynomial.idealX, Ideal.mem_span_singleton, Polynomial.X_dvd_iff] using hc

lemma bar_polynomial_eq (p : Polynomial ℚ) :
    RatFunc.bar (algebraMap (Polynomial ℚ) Coeff p) =
      Polynomial.aeval (RatFunc.X⁻¹ : Coeff) p := by
  have h : RatFunc.bar.toAlgHom.comp (IsScalarTower.toAlgHom ℚ (Polynomial ℚ) Coeff) =
      Polynomial.aeval (RatFunc.X⁻¹ : Coeff) := by
    apply Polynomial.algHom_ext
    simp
  exact DFunLike.congr_fun h p

lemma polynomial_bar_regular_constant (p : Polynomial ℚ)
    (hp : RatFunc.bar (algebraMap (Polynomial ℚ) Coeff p) ∈ LocalRing) :
    ∃ c : ℚ, algebraMap (Polynomial ℚ) Coeff p = algebraMap ℚ Coeff c := by
  by_cases hz : p = 0
  · exact ⟨0, by simp [hz]⟩
  have hpos : 1 < zeroValuation (RatFunc.X⁻¹ : Coeff) :=
    (Valuation.val_lt_one_iff zeroValuation RatFunc.X_ne_zero).mp zeroValuation_X_lt_one
  have hv := local_mem_valuation hp
  rw [bar_polynomial_eq,
    Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
      _ hpos hz] at hv
  have hdeg : p.natDegree = 0 := by
    by_contra hn
    exact (not_lt_of_ge hv) (one_lt_pow₀ hpos hn)
  refine ⟨p.coeff 0, ?_⟩
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
  simp

/-- Removing possible poles at zero from a Laurent presentation. -/
lemma polynomial_of_regular_laurent_presentation (x : Coeff) (hx : x ∈ LocalRing)
    (n : ℕ) (p : Polynomial ℚ)
    (heq : x * RatFunc.X ^ n = algebraMap (Polynomial ℚ) Coeff p) :
    ∃ q : Polynomial ℚ, x = algebraMap (Polynomial ℚ) Coeff q := by
  induction n generalizing p with
  | zero => exact ⟨p, by simpa using heq⟩
  | succ n ih =>
    have hvp : zeroValuation (algebraMap (Polynomial ℚ) Coeff p) < 1 := by
      rw [← heq, map_mul, map_pow]
      apply lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (local_mem_valuation hx) zero_le)
      rw [one_mul]
      exact pow_lt_one₀ zero_le zeroValuation_X_lt_one (by omega)
    have hdiv : Polynomial.X ∣ p := by
      have hm := (valuation_lt_one_iff_mem (Polynomial.idealX ℚ) p).mp hvp
      simpa [Polynomial.idealX, Ideal.mem_span_singleton] using hm
    obtain ⟨q, rfl⟩ := hdiv
    apply ih q
    apply mul_right_cancel₀ (RatFunc.X_ne_zero (K := ℚ))
    calc
      x * RatFunc.X ^ n * RatFunc.X = x * RatFunc.X ^ (n + 1) := by ring
      _ = algebraMap (Polynomial ℚ) Coeff (Polynomial.X * q) := heq
      _ = algebraMap (Polynomial ℚ) Coeff q * RatFunc.X := by
        simp [mul_comm]

/-- Evaluation of genuine Laurent polynomials in the rational-function indeterminate. -/
def laurentToCoeff : LaurentPolynomial ℚ →+* Coeff :=
  LaurentPolynomial.eval₂ (algebraMap ℚ Coeff) (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

lemma laurentToCoeff_toLaurent (p : Polynomial ℚ) :
    laurentToCoeff p.toLaurent = algebraMap (Polynomial ℚ) Coeff p := by
  rw [laurentToCoeff, LaurentPolynomial.eval₂_toLaurent]
  change Polynomial.aeval (RatFunc.X : Coeff) p = _
  rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_X_left_apply]

lemma laurentToCoeff_T (n : ℕ) :
    laurentToCoeff (LaurentPolynomial.T n) = (RatFunc.X : Coeff) ^ n := by
  simp [laurentToCoeff]

/-- The evaluation uses the transcendental parameter and loses no Laurent coefficients. -/
lemma laurentToCoeff_injective : Function.Injective laurentToCoeff := by
  suffices hzero : ∀ l, laurentToCoeff l = 0 → l = 0 by
    intro l m h
    apply sub_eq_zero.mp
    apply hzero
    simp [h]
  intro l hl
  obtain ⟨n, p, hp⟩ := l.exists_T_pow
  have he : algebraMap (Polynomial ℚ) Coeff p = 0 := by
    have h := congrArg laurentToCoeff hp
    simpa only [map_mul, laurentToCoeff_toLaurent, hl, zero_mul] using h
  have hpzero : p = 0 := (RatFunc.algebraMap_injective ℚ) (by simpa using he)
  have hmul : l * LaurentPolynomial.T (n : ℤ) = 0 := by
    rw [← hp, hpzero, map_zero]
  exact (LaurentPolynomial.isUnit_T (n : ℤ)).mul_right_cancel (by simpa using hmul)

/-- A Laurent polynomial regular at zero is an ordinary polynomial. -/
lemma laurent_regular_polynomial (l : LaurentPolynomial ℚ)
    (hl : laurentToCoeff l ∈ LocalRing) :
    ∃ p : Polynomial ℚ, laurentToCoeff l = algebraMap (Polynomial ℚ) Coeff p := by
  obtain ⟨n, p, hp⟩ := l.exists_T_pow
  apply polynomial_of_regular_laurent_presentation _ hl n p
  have h := congrArg laurentToCoeff hp
  simpa only [map_mul, laurentToCoeff_toLaurent, laurentToCoeff_T] using h.symm

/-- Scalar Laurent triple-intersection theorem. Our own argument, not
Kashiwara's. Neither balancedness nor any basis theorem is assumed. -/
theorem laurent_regular_bar_regular_constant (l : LaurentPolynomial ℚ)
    (hzero : laurentToCoeff l ∈ LocalRing)
    (hinfty : RatFunc.bar (laurentToCoeff l) ∈ LocalRing) :
    ∃ c : ℚ, laurentToCoeff l = algebraMap ℚ Coeff c := by
  obtain ⟨p, hp⟩ := laurent_regular_polynomial l hzero
  rw [hp] at hinfty ⊢
  exact polynomial_bar_regular_constant p hinfty

/-- Inside `ℚ(X)`, the Laurent condition together with regularity at zero and at
infinity forces a rational constant. Reconstructed; no primary source was consulted. -/
theorem scalar_laurent_intersection (x : Coeff)
    (hlaurent : x ∈ Set.range laurentToCoeff)
    (hzero : x ∈ LocalRing) (hinfty : RatFunc.bar x ∈ LocalRing) :
    ∃ c : ℚ, x = algebraMap ℚ Coeff c := by
  obtain ⟨l, rfl⟩ := hlaurent
  exact laurent_regular_bar_regular_constant l hzero hinfty

/-- Bar acts on divided-power coordinates by coefficient bar. -/
theorem dividedBasis_repr_bar (n : ℕ) (x : Space n) (j : Fin (n + 1)) :
    (dividedBasis n).repr (moduleBar n x) j = RatFunc.bar ((dividedBasis n).repr x j) := by
  have h : moduleBar n x =
      ∑ k, RatFunc.bar ((dividedBasis n).repr x k) • dividedBasis n k := by
    conv_lhs => rw [← (dividedBasis n).sum_repr x]
    change (moduleBarEquiv n) (∑ k, (dividedBasis n).repr x k • dividedBasis n k) = _
    rw [map_sum]
    simp only [moduleBarEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
      moduleBar_smul, moduleBar_dividedBasis]
  rw [h]
  simp [Finsupp.single_apply]

/-- Coordinate compatibility of the free local lattice with its ambient field basis. -/
theorem lattice_repr_coe (n : ℕ) (x : lattice n) (j : Fin (n + 1)) :
    ((latticeBasis n).repr x j : Coeff) = (dividedBasis n).repr (x : Space n) j :=
  (dividedBasis n).restrictScalars_repr_apply LocalRing x j

/-- The embedded rational constants agree with the ambient constant-field inclusion. -/
@[simp] theorem local_rat_coe (c : ℚ) :
    ((algebraMap ℚ LocalRing c) : Coeff) = algebraMap ℚ Coeff c := by
  change algebraMap (Polynomial ℚ) Coeff (Polynomial.C c) = _
  simp

/-- Constant-coordinate section, rational-linear on the actual local lattice. -/
def constantSection (n : ℕ) : (Fin (n + 1) → ℚ) →ₗ[ℚ] lattice n :=
  ∑ j, (LinearMap.proj j).smulRight (latticeBasis n j)

@[simp] theorem constantSection_eq (n : ℕ) (c : Fin (n + 1) → ℚ) :
    constantSection n c = constantLift n c := by
  simp [constantSection, constantLift]

/-- Exact local coordinates of the constant section. -/
@[simp] theorem constantLift_repr (n : ℕ) (c : Fin (n + 1) → ℚ) (j : Fin (n + 1)) :
    (latticeBasis n).repr (constantLift n c) j = algebraMap ℚ LocalRing (c j) := by
  simp only [constantLift, map_sum, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, Algebra.smul_def]

/-- The genuine rational Laurent form, generated by the divided powers. -/
def laurentForm (n : ℕ) : Submodule laurentToCoeff.range (Space n) :=
  Submodule.span laurentToCoeff.range (Set.range (dividedBasis n))

/-- Laurent-form membership is exactly the Laurent condition on every coefficient. -/
theorem mem_laurentForm_iff (n : ℕ) (x : Space n) :
    x ∈ laurentForm n ↔ ∀ j, (dividedBasis n).repr x j ∈ Set.range laurentToCoeff := by
  rw [laurentForm, Module.Basis.mem_span_iff_repr_mem]
  constructor
  · intro h j
    obtain ⟨a, ha⟩ := h j
    exact ha ▸ a.property
  · intro h j
    exact ⟨⟨_, h j⟩, rfl⟩

/-- The actual triple condition, with the local condition supplied by `x : lattice n`. -/
def InTriple (n : ℕ) (x : lattice n) : Prop :=
  (x : Space n) ∈ laurentForm n ∧ moduleBar n (x : Space n) ∈ lattice n

/-- The triple intersection is exactly the constant-coordinate section.
Reconstructed rank-one argument, using the proved scalar Laurent intersection. -/
theorem inTriple_iff_constant (n : ℕ) (x : lattice n) :
    InTriple n x ↔ ∃ c : Fin (n + 1) → ℚ, constantSection n c = x := by
  constructor
  · rintro ⟨hl, hb⟩
    have hc : ∀ j, ∃ c : ℚ,
        ((latticeBasis n).repr x j : Coeff) = algebraMap ℚ Coeff c := by
      intro j
      rw [lattice_repr_coe]
      apply scalar_laurent_intersection
      · exact (mem_laurentForm_iff n x).mp hl j
      · exact (mem_lattice_iff n x).mp x.property j
      · simpa only [dividedBasis_repr_bar] using (mem_lattice_iff n _).mp hb j
    choose c hc using hc
    refine ⟨c, ?_⟩
    apply (latticeBasis n).repr.injective
    apply DFunLike.ext
    intro j
    apply Subtype.val_injective
    simpa only [constantSection_eq, constantLift_repr, local_rat_coe] using (hc j).symm
  · rintro ⟨c, rfl⟩
    have hc (j : Fin (n + 1)) :
        (dividedBasis n).repr (constantSection n c : Space n) j =
          algebraMap ℚ Coeff (c j) := by
      rw [← lattice_repr_coe]
      simp only [constantSection_eq, constantLift_repr, local_rat_coe]
    constructor
    · rw [mem_laurentForm_iff]
      intro j
      rw [hc]
      exact ⟨LaurentPolynomial.C (c j), by simp [laurentToCoeff]⟩
    · rw [mem_lattice_iff]
      intro j
      rw [dividedBasis_repr_bar, hc]
      simpa using (algebraMap ℚ LocalRing (c j)).property

/-- The actual intersection `L ∩ bar(L) ∩ V_{ℚ[X,X⁻¹]}`, inside `L`.
The carrier is the three genuine membership conditions, not a chosen constant span. -/
def tripleLattice (n : ℕ) : Submodule ℚ (lattice n) where
  carrier := {x | InTriple n x}
  zero_mem' := (inTriple_iff_constant n 0).mpr ⟨0, map_zero _⟩
  add_mem' hx hy := by
    obtain ⟨c, rfl⟩ := (inTriple_iff_constant n _).mp hx
    obtain ⟨d, rfl⟩ := (inTriple_iff_constant n _).mp hy
    exact (inTriple_iff_constant n _).mpr ⟨c + d, map_add _ _ _⟩
  smul_mem' a x hx := by
    obtain ⟨c, rfl⟩ := (inTriple_iff_constant n x).mp hx
    exact (inTriple_iff_constant n _).mpr ⟨a • c, (constantSection n).map_smul a c⟩

/-- A triple-intersection vector is recovered from its genuine residue. -/
theorem triple_eq_constantResidue (n : ℕ) (x : tripleLattice n) :
    (x : lattice n) = constantSection n (latticeResidue n x) := by
  obtain ⟨c, hc⟩ := (inTriple_iff_constant n x).mp x.property
  rw [← hc]
  simp

/-- The balanced-triple projection is the actual quotient map, restricted to the intersection. -/
def tripleProjection (n : ℕ) : tripleLattice n →ₗ[ℚ] ResidueSpace n :=
  (xLattice n).mkQ.comp (tripleLattice n).subtype

/-- Rank-one balancedness: the actual triple intersection maps bijectively to `L / X L`.
Reconstructed from the scalar Laurent intersection, not assumed as an interface hypothesis. -/
theorem tripleProjection_bijective (n : ℕ) : Function.Bijective (tripleProjection n) := by
  constructor
  · intro x y h
    have hr : latticeResidue n x = latticeResidue n y :=
      congrArg (residueEquiv n) h
    apply Subtype.val_injective
    rw [triple_eq_constantResidue n x, triple_eq_constantResidue n y, hr]
  · intro q
    refine ⟨⟨constantSection n (residueEquiv n q),
      (inTriple_iff_constant n _).mpr ⟨_, rfl⟩⟩, ?_⟩
    apply (residueEquiv n).injective
    change latticeResidue n (constantSection n (residueEquiv n q)) = _
    simp

/-- The proved rational balanced-triple isomorphism for the actual rank-one module. -/
def balancedEquiv (n : ℕ) : tripleLattice n ≃ₗ[ℚ] ResidueSpace n :=
  LinearEquiv.ofBijective (tripleProjection n) (tripleProjection_bijective n)

/-- The actual divided-power vectors lie in all three forms. -/
theorem latticeBasis_mem_triple (n : ℕ) (j : Fin (n + 1)) :
    latticeBasis n j ∈ tripleLattice n := by
  change InTriple n (latticeBasis n j)
  constructor
  · rw [latticeBasis_coe]
    exact Submodule.subset_span (Set.mem_range_self j)
  · simpa using dividedBasis_mem_lattice n j

/-- The rational global lift of a crystal residue element, in the actual triple intersection. -/
def globalLift (n : ℕ) (j : Fin (n + 1)) : tripleLattice n :=
  ⟨latticeBasis n j, latticeBasis_mem_triple n j⟩

/-- The balanced inverse lifts the crystal residue basis to the actual divided powers. -/
@[simp] theorem balancedEquiv_symm_residueBasis (n : ℕ) (j : Fin (n + 1)) :
    (balancedEquiv n).symm (residueBasis n j) = globalLift n j := by
  apply (balancedEquiv n).injective
  simpa only [LinearEquiv.apply_symm_apply, balancedEquiv, LinearEquiv.ofBijective_apply,
    tripleProjection, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.mkQ_apply, globalLift] using residueBasis_eq n j

/-- These are the real represented `F^(j)` vectors, not an abstract replacement basis. -/
theorem globalLift_coe (n : ℕ) (j : Fin (n + 1)) :
    ((globalLift n j : lattice n) : Space n) =
      rep n (qDivPow (RatFunc.X : Coeff) j (F sl2RootDatum RatFunc.X ())) (highest n) := by
  simpa only [globalLift, latticeBasis_coe] using dividedBasis_eq n j

/-- Uniqueness of the global lift is proved in the Laurent triple, not in `L ∩ bar(L)` alone. -/
theorem globalLift_unique (n : ℕ) (j : Fin (n + 1)) (x : tripleLattice n)
    (hx : tripleProjection n x = residueBasis n j) : x = globalLift n j := by
  apply (tripleProjection_bijective n).injective
  rw [hx]
  exact residueBasis_eq n j

/-- The unique lifts form a rational basis of the actual triple intersection. -/
def globalBasis (n : ℕ) : Module.Basis (Fin (n + 1)) ℚ (tripleLattice n) :=
  (residueBasis n).map (balancedEquiv n).symm

@[simp] theorem globalBasis_apply (n : ℕ) (j : Fin (n + 1)) :
    globalBasis n j = globalLift n j := by
  exact balancedEquiv_symm_residueBasis n j

/-- The global lifts are fixed by the proved coefficient-semilinear module bar. -/
theorem moduleBar_globalLift (n : ℕ) (j : Fin (n + 1)) :
    moduleBar n ((globalLift n j : lattice n) : Space n) =
      ((globalLift n j : lattice n) : Space n) := by
  simp [globalLift]

/-- Restriction of an actual field-linear lattice-stable operator. -/
def latticeEnd (n : ℕ) (f : Module.End Coeff (Space n))
    (hf : ∀ x ∈ lattice n, f x ∈ lattice n) : Module.End LocalRing (lattice n) where
  toFun x := ⟨f x, hf x x.property⟩
  map_add' x y := by
    apply Subtype.val_injective
    exact map_add f (x : Space n) (y : Space n)
  map_smul' a x := by
    apply Subtype.val_injective
    exact (f.restrictScalars LocalRing).map_smul a (x : Space n)

/-- Every local-linear lattice operator descends through the actual submodule `X L`. -/
def residueEnd (n : ℕ) (f : Module.End LocalRing (lattice n)) :
    Module.End ℚ (ResidueSpace n) :=
  (xLattice n).mapQ (xLattice n) (f.restrictScalars ℚ) (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (map_smul f localX y).symm⟩)

/-- The actual lowering operator on the quotient, not an independently chosen shift. -/
def residueLower (n : ℕ) : Module.End ℚ (ResidueSpace n) :=
  residueEnd n (latticeEnd n (lower n) (fun _ hx ↦ lower_mem_lattice n hx))

/-- The actual raising operator on the quotient. -/
def residueRaise (n : ℕ) : Module.End ℚ (ResidueSpace n) :=
  residueEnd n (latticeEnd n (raise n) (fun _ hx ↦ raise_mem_lattice n hx))

/-- Lowering has the crystal string action on the proved quotient basis. -/
@[simp] theorem residueLower_basis (n : ℕ) (j : Fin (n + 1)) :
    residueLower n (residueBasis n j) =
      if h : (j : ℕ) + 1 < n + 1 then residueBasis n ⟨j + 1, h⟩ else 0 := by
  rw [residueBasis_eq]
  change Submodule.Quotient.mk
    (⟨lower n (latticeBasis n j), _⟩ : lattice n) = _
  split_ifs with h
  · rw [residueBasis_eq]
    congr 1
    apply Subtype.val_injective
    simp [h]
  · change (xLattice n).mkQ _ = 0
    have hz : (⟨lower n (latticeBasis n j),
        lower_mem_lattice n (latticeBasis n j).property⟩ : lattice n) = 0 := by
      apply Subtype.val_injective
      simp [h]
    rw [hz, map_zero]

/-- Raising has the crystal string action on the proved quotient basis. -/
@[simp] theorem residueRaise_basis (n : ℕ) (j : Fin (n + 1)) :
    residueRaise n (residueBasis n j) =
      if h : 0 < (j : ℕ) then residueBasis n ⟨j - 1, by omega⟩ else 0 := by
  rw [residueBasis_eq]
  change Submodule.Quotient.mk
    (⟨raise n (latticeBasis n j), _⟩ : lattice n) = _
  split_ifs with h
  · rw [residueBasis_eq]
    congr 1
    apply Subtype.val_injective
    simp [h]
  · change (xLattice n).mkQ _ = 0
    have hz : (⟨raise n (latticeBasis n j),
        raise_mem_lattice n (latticeBasis n j).property⟩ : lattice n) = 0 := by
      apply Subtype.val_injective
      simp [h]
    rw [hz, map_zero]

end QuantumGroup.Sl2.RankOne
