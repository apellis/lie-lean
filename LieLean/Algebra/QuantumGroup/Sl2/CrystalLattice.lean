/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Sl2.SimpleModule
import LieLean.Algebra.QuantumGroup.LusztigF.Bar
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Rank-one divided-power basis and module bar

## Main definitions
* `rep`: the actual type-1 representation `simpleRep X n 1`.
* `dividedBasis`: inverse quantum-factorial rescaling of the ordinary lowering basis.
* `moduleBar`: coefficient-semilinear involution on this representation.

## Main results
* `dividedBasis_eq`: the basis consists of the actual `F^(j)` applied to the highest vector.
* `moduleBar_E`, `moduleBar_F`, `moduleBar_K`: compatibility on all algebra generators.
* `latticeBasis`, `lattice_spans`: a free full local lattice over the actual localization
  `ℚ[X]_(X)`, stable under the explicitly constructed rank-one Kashiwara string shifts.

## References
Our own rank-one arguments, aimed at the rank-one case of Kashiwara, *On crystal bases*,
§§12.2–12.3.
No general global-basis theorem or balancedness is assumed or asserted here.
In particular, no residue basis, Laurent triple-intersection calculation or balanced-triple
isomorphism has yet been proved. Compatibility of module bar is stated generatorwise;
this file does not construct a bar ring equivalence on the full quantum algebra.
-/

noncomputable section

namespace QuantumGroup.Sl2.RankOne

abbrev Coeff := RatFunc ℚ
abbrev Space (n : ℕ) := Fin (n + 1) → Coeff

/-- The actual existing simple representation, with the positive type-1 sign. -/
def rep (n : ℕ) : Sl2 (RatFunc.X : Coeff) →ₐ[Coeff] Module.End Coeff (Space n) :=
  simpleRep RatFunc.X n 1 RatFunc.X_ne_zero
    (LusztigF.ratFunc_X_pow_ne_one (by omega)) (by simp)

/-- Highest vector in the existing ordinary lowering coordinates. -/
def highest (n : ℕ) : Space n := Pi.single 0 1

/-- The quantum factorial denominators are nonzero at the indeterminate. -/
theorem factorial_ne_zero (j : ℕ) : qFactorial (RatFunc.X : Coeff) j ≠ 0 := by
  simpa using qFactorial_X_pow_ne_zero (K := ℚ) 1 j one_pos

/-- Genuine divided-power basis, not the unnormalized ordinary lowering basis. -/
def dividedBasis (n : ℕ) : Module.Basis (Fin (n + 1)) Coeff (Space n) :=
  (Pi.basisFun Coeff (Fin (n + 1))).unitsSMul
    (fun j ↦ Units.mk0 ((qFactorial (RatFunc.X : Coeff) j)⁻¹) (inv_ne_zero (factorial_ne_zero j)))

/-- The normalization is precisely inverse quantum factorial. -/
theorem dividedBasis_apply (n : ℕ) (j : Fin (n + 1)) :
    dividedBasis n j = (qFactorial (RatFunc.X : Coeff) j)⁻¹ • Pi.single j 1 := by
  simp [dividedBasis, Module.Basis.unitsSMul_apply, Pi.basisFun_apply]

/-- Ordinary lowering powers recover the ordinary coordinate vector. -/
theorem F_pow_highest (n : ℕ) (j : Fin (n + 1)) :
    rep n ((F sl2RootDatum RatFunc.X ()) ^ (j : ℕ)) (highest n) = Pi.single j 1 := by
  simp only [rep, map_pow, simpleRep_F]
  apply ext_coord
  intro l
  have hj := j.2
  rw [coord_opF_pow, highest, coord_single, coord_single, Fin.val_zero]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The proved basis is the actual algebra divided powers applied to the highest vector. -/
theorem dividedBasis_eq (n : ℕ) (j : Fin (n + 1)) :
    dividedBasis n j =
      rep n (qDivPow (RatFunc.X : Coeff) j (F sl2RootDatum RatFunc.X ())) (highest n) := by
  rw [qDivPow, map_smul, LinearMap.smul_apply, F_pow_highest, dividedBasis_apply]

/-- The selected vector is genuinely highest weight. -/
theorem E_highest (n : ℕ) :
    rep n (E sl2RootDatum RatFunc.X ()) (highest n) = 0 := by
  simp only [rep, highest, simpleRep_E_single, Fin.val_zero, lt_self_iff_false,
    ↓reduceDIte]

/-- The ordinary lowering string has the correct finite boundary. -/
theorem F_pow_highest_zero (n : ℕ) :
    rep n (F sl2RootDatum RatFunc.X () ^ (n + 1)) (highest n) = 0 := by
  simp only [rep, map_pow, simpleRep_F]
  apply ext_coord
  intro l
  rw [coord_opF_pow, coord_zero]
  split_ifs with h
  · omega
  · rfl

/-- The representation is irreducible over `ℚ(X)`, with no closure-field assumption. -/
theorem irreducible (n : ℕ) (W : Submodule Coeff (Space n))
    (hW : ∀ u x, x ∈ W → rep n u x ∈ W) : W = ⊥ ∨ W = ⊤ :=
  simpleRep_irreducible RatFunc.X_ne_zero
    (fun _ hm ↦ LusztigF.ratFunc_X_pow_ne_one hm) (by simp) W hW

/-- Pointwise coefficient bar, not a `ℚ(X)`-linear map. -/
def moduleBar (n : ℕ) (x : Space n) : Space n := fun j ↦ RatFunc.bar (x j)

@[simp] theorem moduleBar_apply (n : ℕ) (x : Space n) (j : Fin (n + 1)) :
    moduleBar n x j = RatFunc.bar (x j) := rfl

/-- The module bar is involutive. -/
@[simp] theorem moduleBar_involutive (n : ℕ) (x : Space n) :
    moduleBar n (moduleBar n x) = x := by ext j; simp

/-- The module bar is additive. -/
theorem moduleBar_add (n : ℕ) (x y : Space n) :
    moduleBar n (x + y) = moduleBar n x + moduleBar n y := by ext j; simp

/-- The exact coefficient-semilinearity law. -/
theorem moduleBar_smul (n : ℕ) (c : Coeff) (x : Space n) :
    moduleBar n (c • x) = RatFunc.bar c • moduleBar n x := by ext j; simp

/-- The proved additive involution packaged as an equivalence; scalar behavior is
`moduleBar_smul`, not coefficient linearity. -/
def moduleBarEquiv (n : ℕ) : Space n ≃+ Space n where
  toFun := moduleBar n
  invFun := moduleBar n
  left_inv := moduleBar_involutive n
  right_inv := moduleBar_involutive n
  map_add' := moduleBar_add n

/-- Coordinate extension by zero commutes with bar. -/
theorem coord_moduleBar (n : ℕ) (x : Space n) (l : ℕ) :
    coord n (moduleBar n x) l = RatFunc.bar (coord n x l) := by
  unfold coord
  split_ifs <;> simp

/-- Quantum integers are bar-fixed. -/
theorem bar_qInt (j : ℕ) : RatFunc.bar (qInt (RatFunc.X : Coeff) j) =
    qInt RatFunc.X j := by
  simpa only [pow_one, qBinomial_one_right] using bar_qBinomial (K := ℚ) 1 j 1

/-- Bar fixes the highest vector. -/
@[simp] theorem moduleBar_highest (n : ℕ) : moduleBar n (highest n) = highest n := by
  ext j
  simp [moduleBar, highest, Pi.single_apply]

/-- Bar fixes the actual divided-power basis. -/
@[simp] theorem moduleBar_dividedBasis (n : ℕ) (j : Fin (n + 1)) :
    moduleBar n (dividedBasis n j) = dividedBasis n j := by
  have hq := bar_inv_qFactorial (K := ℚ) 1 j
  simp only [pow_one] at hq
  rw [dividedBasis_apply, moduleBar_smul, hq]
  congr 1
  ext l
  simp [moduleBar, Pi.single_apply]

/-- Compatibility with the actual positive generator: bar fixes `E`. -/
theorem moduleBar_E (n : ℕ) (x : Space n) :
    moduleBar n (rep n (E sl2RootDatum RatFunc.X ()) x) =
      rep n (E sl2RootDatum RatFunc.X ()) (moduleBar n x) := by
  ext j
  simp [rep, moduleBar, opE, eCoeff, bar_qInt, coord_moduleBar]

/-- Compatibility with the actual negative generator: bar fixes `F`. -/
theorem moduleBar_F (n : ℕ) (x : Space n) :
    moduleBar n (rep n (F sl2RootDatum RatFunc.X ()) x) =
      rep n (F sl2RootDatum RatFunc.X ()) (moduleBar n x) := by
  ext j
  simp only [rep, simpleRep_F, moduleBar_apply, opF, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> simp [coord_moduleBar]

/-- Toral compatibility at every integral exponent: bar sends `K_μ` to `K_{-μ}`. -/
theorem moduleBar_K (n : ℕ) (μ : ℤ) (x : Space n) :
    moduleBar n (rep n (K sl2RootDatum RatFunc.X μ) x) =
      rep n (K sl2RootDatum RatFunc.X (-μ)) (moduleBar n x) := by
  ext j
  simp [rep, moduleBar, opK, map_zpow₀, zpow_neg, neg_mul]

/-- Explicit type-1 weight formula on the divided-power basis. -/
theorem dividedBasis_weight (n : ℕ) (μ : ℤ) (j : Fin (n + 1)) :
    rep n (K sl2RootDatum RatFunc.X μ) (dividedBasis n j) =
      ((RatFunc.X : Coeff) ^ (μ * ((n : ℤ) - 2 * j))) • dividedBasis n j := by
  rw [dividedBasis_apply, map_smul]
  simp only [rep, simpleRep_K_single, one_zpow, one_mul]
  exact smul_comm _ _ _

/-- The actual local ring `ℚ[X]_(X)` embedded in `ℚ(X)`, not just polynomials. -/
abbrev LocalRing :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime Coeff (Polynomial.idealX ℚ)

/-- The ring used for the lattice really is localization at the prime `(X)`. -/
theorem localRing_isLocalization :
    IsLocalization (Polynomial.idealX ℚ).asIdeal.primeCompl LocalRing := inferInstance

/-- The genuine local lattice spanned by the actual divided-power vectors. -/
def lattice (n : ℕ) : Submodule LocalRing (Space n) :=
  Submodule.span LocalRing (Set.range (dividedBasis n))

/-- Freeness of the local lattice is proved by restriction from the constructed field basis. -/
def latticeBasis (n : ℕ) : Module.Basis (Fin (n + 1)) LocalRing (lattice n) :=
  (dividedBasis n).restrictScalars LocalRing

/-- The local basis consists of the same actual divided powers. -/
@[simp] theorem latticeBasis_coe (n : ℕ) (j : Fin (n + 1)) :
    (latticeBasis n j : Space n) = dividedBasis n j :=
  Module.Basis.restrictScalars_apply _ _ _

/-- Every divided-power vector belongs to the lattice. -/
theorem dividedBasis_mem_lattice (n : ℕ) (j : Fin (n + 1)) :
    dividedBasis n j ∈ lattice n := Submodule.subset_span (Set.mem_range_self j)

/-- The local lattice has full generic span. -/
theorem lattice_spans (n : ℕ) :
    Submodule.span Coeff (lattice n : Set (Space n)) = ⊤ := by
  apply top_unique
  rw [← (dividedBasis n).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact dividedBasis_mem_lattice n j

/-- Membership in the local lattice means regular-at-zero divided-basis coordinates. -/
theorem mem_lattice_iff (n : ℕ) (x : Space n) :
    x ∈ lattice n ↔ ∀ j, (dividedBasis n).repr x j ∈ LocalRing := by
  rw [lattice, Module.Basis.mem_span_iff_repr_mem]
  constructor
  · intro h j
    obtain ⟨a, ha⟩ := h j
    exact ha ▸ a.property
  · intro h j
    exact ⟨⟨_, h j⟩, rfl⟩

/-- Kashiwara lowering on the single actual highest-weight divided-power string. -/
def lower (n : ℕ) : Module.End Coeff (Space n) :=
  (dividedBasis n).constr Coeff fun j ↦
    if h : (j : ℕ) + 1 < n + 1 then dividedBasis n ⟨j + 1, h⟩ else 0

/-- Kashiwara raising on the single actual highest-weight divided-power string. -/
def raise (n : ℕ) : Module.End Coeff (Space n) :=
  (dividedBasis n).constr Coeff fun j ↦
    if h : 0 < (j : ℕ) then dividedBasis n ⟨j - 1, by omega⟩ else 0

/-- The lowering operator shifts actual divided powers, with the correct top boundary. -/
@[simp] theorem lower_dividedBasis (n : ℕ) (j : Fin (n + 1)) :
    lower n (dividedBasis n j) =
      if h : (j : ℕ) + 1 < n + 1 then dividedBasis n ⟨j + 1, h⟩ else 0 := by
  exact (dividedBasis n).constr_basis Coeff _ j

/-- The raising operator shifts actual divided powers, with the correct highest boundary. -/
@[simp] theorem raise_dividedBasis (n : ℕ) (j : Fin (n + 1)) :
    raise n (dividedBasis n j) =
      if h : 0 < (j : ℕ) then dividedBasis n ⟨j - 1, by omega⟩ else 0 := by
  exact (dividedBasis n).constr_basis Coeff _ j

/-- The actual local lattice is stable under Kashiwara lowering. -/
theorem lower_mem_lattice (n : ℕ) {x : Space n} (hx : x ∈ lattice n) :
    lower n x ∈ lattice n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [lower_dividedBasis]
    split_ifs
    · exact dividedBasis_mem_lattice n _
    · exact (lattice n).zero_mem
  | zero => simp
  | add x y _ _ hx hy => simpa using (lattice n).add_mem hx hy
  | smul a x _ hx =>
    simpa using (lattice n).smul_mem a hx

/-- The actual local lattice is stable under Kashiwara raising. -/
theorem raise_mem_lattice (n : ℕ) {x : Space n} (hx : x ∈ lattice n) :
    raise n x ∈ lattice n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [raise_dividedBasis]
    split_ifs
    · exact dividedBasis_mem_lattice n _
    · exact (lattice n).zero_mem
  | zero => simp
  | add x y _ _ hx hy => simpa using (lattice n).add_mem hx hy
  | smul a x _ hx =>
    simpa using (lattice n).smul_mem a hx

end QuantumGroup.Sl2.RankOne
