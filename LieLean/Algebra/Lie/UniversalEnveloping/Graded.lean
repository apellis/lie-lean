/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.UniversalEnveloping.Filtration
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The graded Poincaré–Birkhoff–Witt theorem

Let `L` be a Lie algebra over a commutative ring `R` and let `F₀ ⊆ F₁ ⊆ ⋯` be the PBW filtration
of `U(L)` (`UniversalEnvelopingAlgebra.filtration`). We construct the associated graded algebra
`gr U(L) = ⨁ₙ Fₙ / Fₙ₋₁`, show that it is commutative, and prove that the canonical algebra map
`Sym(L) → gr U(L)` induced by `L → F₁ / F₀` is surjective, and an isomorphism when `L` is free as
an `R`-module.

To obtain a ring without dependent-type bookkeeping, we realise `gr U(L)` as the quotient of the
Rees algebra `⨁ₙ Fₙ tⁿ ⊆ U(L)[t]` by the two-sided ideal `t · ⨁ₙ Fₙ tⁿ`. The degree-`n` piece is
the image of `toGr R L n : Fₙ →ₗ[R] gr U(L)`, `x ↦ [x tⁿ]`, whose kernel is `Fₙ₋₁`
(`ker_toGr_succ`, `ker_toGr_zero`); these pieces form an internal direct sum decomposition
(`isInternal_range_toGr`) compatible with multiplication (`toGr_mul`), so that
`gr U(L) ≅ ⨁ₙ Fₙ / Fₙ₋₁` as graded algebras.

## Main definitions

* `UniversalEnvelopingAlgebra.reesAlgebra R L`: the Rees algebra `⨁ₙ Fₙ tⁿ ⊆ U(L)[t]`.
* `UniversalEnvelopingAlgebra.AssociatedGraded R L`: the associated graded algebra `gr U(L)`.
* `UniversalEnvelopingAlgebra.toGr R L n`: the map `Fₙ → gr U(L)` onto the degree-`n` piece.
* `UniversalEnvelopingAlgebra.symmetricAlgebraToAssociatedGraded R L`: the canonical map
  `Sym(L) →ₐ[R] gr U(L)`.
* `UniversalEnvelopingAlgebra.symmetricAlgebraEquivAssociatedGraded R L`: for `L` free, the
  algebra isomorphism `Sym(L) ≃ₐ[R] gr U(L)`.

## Main results

* `UniversalEnvelopingAlgebra.quotEquivRangeToGr`, `isInternal_range_toGr`: `gr U(L)` is the
  internal direct sum of its graded pieces, and the piece of degree `n + 1` is `Fₙ₊₁ / Fₙ`.
* `UniversalEnvelopingAlgebra.AssociatedGraded.instCommRing`: `gr U(L)` is commutative.
* `UniversalEnvelopingAlgebra.symmetricAlgebraToAssociatedGraded_surjective`.
* `UniversalEnvelopingAlgebra.symmetricAlgebraToAssociatedGraded_bijective`: the graded PBW
  theorem.

## References

* J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §17.3–17.4
  (the PBW Theorem in §17.3 is the statement `Sym(L) ≅ gr U(L)`).
* N. Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.6–2.7.
-/

open Polynomial Module

noncomputable section

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The Rees algebra `⨁ₙ Fₙ tⁿ ⊆ U(L)[t]` of the PBW filtration of `U(L)`. -/
def reesAlgebra : Subalgebra R (UniversalEnvelopingAlgebra R L)[X] where
  carrier := {p | ∀ n, p.coeff n ∈ filtration R L n}
  mul_mem' {p q} hp hq n := by
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun x hx ↦ ?_
    rw [← Finset.mem_antidiagonal.mp hx]
    exact mul_mem_filtration (hp _) (hq _)
  add_mem' hp hq n := by rw [coeff_add]; exact add_mem (hp n) (hq n)
  algebraMap_mem' r n := by
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs
    · exact algebraMap_mem_filtration r n
    · exact zero_mem _

variable {R L} in
theorem mem_reesAlgebra {p : (UniversalEnvelopingAlgebra R L)[X]} :
    p ∈ reesAlgebra R L ↔ ∀ n, p.coeff n ∈ filtration R L n := Iff.rfl

/-- The ring congruence on the Rees algebra given by the two-sided ideal
`t · reesAlgebra R L` (note that `t` is central). -/
def grCon : RingCon (reesAlgebra R L) where
  r p q := ∃ c ∈ reesAlgebra R L,
    (p : (UniversalEnvelopingAlgebra R L)[X]) - (q : (UniversalEnvelopingAlgebra R L)[X]) = X * c
  iseqv :=
    ⟨fun _ ↦ ⟨0, zero_mem _, by simp⟩,
     fun ⟨c, hc, e⟩ ↦ ⟨-c, neg_mem hc, by rw [mul_neg, ← e, neg_sub]⟩,
     fun ⟨c, hc, e⟩ ⟨d, hd, f⟩ ↦ ⟨c + d, add_mem hc hd, by rw [mul_add, ← e, ← f,
      sub_add_sub_cancel]⟩⟩
  add' := fun ⟨c, hc, e⟩ ⟨d, hd, f⟩ ↦ ⟨c + d, add_mem hc hd, by
    simp only [Subalgebra.coe_add]; rw [mul_add, ← e, ← f]; abel⟩
  mul' {w x y z} := fun ⟨c, hc, e⟩ ⟨d, hd, f⟩ ↦ ⟨c * y + x * d,
    add_mem (mul_mem hc y.2) (mul_mem x.2 hd), by
    simp only [Subalgebra.coe_mul]
    rw [show (w : (UniversalEnvelopingAlgebra R L)[X]) * y - x * z =
      (w - x) * y + x * (y - z) by noncomm_ring, e, f, mul_add, mul_assoc,
      ← mul_assoc (x : (UniversalEnvelopingAlgebra R L)[X]) X, ← (commute_X _).eq, mul_assoc]⟩

/-- The associated graded algebra `gr U(L) = ⨁ₙ Fₙ / Fₙ₋₁` of the universal enveloping algebra
with respect to the PBW filtration, realised as the quotient of the Rees algebra by `t`. -/
def AssociatedGraded : Type _ := (grCon R L).Quotient

instance : Ring (AssociatedGraded R L) := inferInstanceAs (Ring (grCon R L).Quotient)

instance : Algebra R (AssociatedGraded R L) := inferInstanceAs (Algebra R (grCon R L).Quotient)

namespace AssociatedGraded

variable {R L}

/-- The quotient map from the Rees algebra onto the associated graded algebra. -/
def mk : reesAlgebra R L →ₐ[R] AssociatedGraded R L := RingCon.mkₐ R (grCon R L)

theorem mk_surjective : Function.Surjective (mk : reesAlgebra R L → AssociatedGraded R L) :=
  RingCon.mkₐ_surjective _

theorem mk_eq_mk_iff {p q : reesAlgebra R L} : mk p = mk q ↔ grCon R L p q := RingCon.eq _

end AssociatedGraded

open AssociatedGraded

/-- The map `Fₙ → reesAlgebra R L`, `x ↦ x tⁿ`. -/
def reesMonomial (n : ℕ) : filtration R L n →ₗ[R] reesAlgebra R L :=
  LinearMap.codRestrict (reesAlgebra R L).toSubmodule
    ((monomial n).restrictScalars R ∘ₗ (filtration R L n).subtype) fun x m ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearMap.coe_restrictScalars]
      rw [coeff_monomial]
      split_ifs with h
      · exact h ▸ x.2
      · exact zero_mem _

/-- The map `Fₙ → gr U(L)`, `x ↦ [x tⁿ]`, onto the graded piece of degree `n`; its kernel is
`Fₙ₋₁` (`ker_toGr_succ`). -/
def toGr (n : ℕ) : filtration R L n →ₗ[R] AssociatedGraded R L :=
  AssociatedGraded.mk.toLinearMap ∘ₗ reesMonomial R L n

variable {R L}

theorem toGr_apply (n : ℕ) (x : filtration R L n) :
    toGr R L n x = AssociatedGraded.mk (reesMonomial R L n x) := rfl

@[simp] theorem coe_reesMonomial (n : ℕ) (x : filtration R L n) :
    (reesMonomial R L n x : (UniversalEnvelopingAlgebra R L)[X]) =
      monomial n (x : UniversalEnvelopingAlgebra R L) := rfl

theorem toGr_congr {m n : ℕ} (h : m = n) {x : filtration R L m} {y : filtration R L n}
    (hxy : (x : UniversalEnvelopingAlgebra R L) = y) : toGr R L m x = toGr R L n y := by
  subst h; rw [Subtype.ext hxy]

/-- The multiplication of `gr U(L)` is induced by that of `U(L)`. -/
theorem toGr_mul {m n : ℕ} (x : filtration R L m) (y : filtration R L n) :
    toGr R L m x * toGr R L n y = toGr R L (m + n)
      ⟨(x * y : UniversalEnvelopingAlgebra R L), mul_mem_filtration x.2 y.2⟩ := by
  rw [toGr_apply, toGr_apply, toGr_apply, ← map_mul]
  congr 1
  ext1
  simp [monomial_mul_monomial]

/-- The kernel of `F_{n+1} → gr U(L)` is `Fₙ`. -/
theorem toGr_succ_eq_zero_iff {n : ℕ} (x : filtration R L (n + 1)) :
    toGr R L (n + 1) x = 0 ↔ (x : UniversalEnvelopingAlgebra R L) ∈ filtration R L n := by
  rw [toGr_apply, ← map_zero AssociatedGraded.mk, mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc, e⟩
    have := congr_arg (fun p : (UniversalEnvelopingAlgebra R L)[X] ↦ p.coeff (n + 1)) e
    simp only [coe_reesMonomial, ZeroMemClass.coe_zero, sub_zero, coeff_monomial_same,
      coeff_X_mul] at this
    exact this ▸ hc n
  · intro hx
    refine ⟨monomial n (x : UniversalEnvelopingAlgebra R L), ?_, ?_⟩
    · exact (reesMonomial R L n ⟨x, hx⟩).2
    · simp

theorem toGr_zero_eq_zero_iff (x : filtration R L 0) : toGr R L 0 x = 0 ↔ x = 0 := by
  rw [toGr_apply, ← map_zero AssociatedGraded.mk, mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc, e⟩
    have := congr_arg (fun p : (UniversalEnvelopingAlgebra R L)[X] ↦ p.coeff 0) e
    simp only [coe_reesMonomial, ZeroMemClass.coe_zero, sub_zero, coeff_monomial_same,
      coeff_X_mul_zero] at this
    exact Subtype.ext this
  · rintro rfl
    exact ⟨0, zero_mem _, by simp⟩

theorem mk_eq_sum_toGr (p : reesAlgebra R L) :
    AssociatedGraded.mk p =
      ∑ n ∈ (p : (UniversalEnvelopingAlgebra R L)[X]).support, toGr R L n ⟨_, p.2 n⟩ := by
  have : p = ∑ n ∈ (p : (UniversalEnvelopingAlgebra R L)[X]).support,
      reesMonomial R L n ⟨_, p.2 n⟩ := by
    ext1
    simp only [AddSubmonoidClass.coe_finsetSum, coe_reesMonomial]
    exact as_sum_support (p : (UniversalEnvelopingAlgebra R L)[X])
  conv_lhs => rw [this]
  rw [map_sum]
  rfl

/-- `gr U(L)` is spanned by its graded pieces. -/
theorem iSup_range_toGr : ⨆ n, LinearMap.range (toGr R L n) = ⊤ := by
  refine eq_top_iff.mpr fun a _ ↦ ?_
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [mk_eq_sum_toGr]
  exact Submodule.sum_mem _ fun n _ ↦ Submodule.mem_iSup_of_mem n ⟨_, rfl⟩

theorem toGr_eq_zero_of_mem {k : ℕ} (x : filtration R L k)
    (hx : (x : UniversalEnvelopingAlgebra R L) ∈ filtration R L (k - 1))
    (h0 : k = 0 → (x : UniversalEnvelopingAlgebra R L) = 0) : toGr R L k x = 0 := by
  cases k with
  | zero => rw [toGr_zero_eq_zero_iff]; exact Subtype.ext (h0 rfl)
  | succ k => exact (toGr_succ_eq_zero_iff x).mpr hx

theorem mk_eq_zero_iff (p : reesAlgebra R L) :
    AssociatedGraded.mk p = 0 ↔ ∀ n, toGr R L n ⟨_, p.2 n⟩ = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ by rw [mk_eq_sum_toGr]; exact Finset.sum_eq_zero fun n _ ↦ h n⟩
  rw [← map_zero AssociatedGraded.mk, mk_eq_mk_iff] at h
  obtain ⟨c, hc, e⟩ := h
  have hcoeff := congr_arg (fun q : (UniversalEnvelopingAlgebra R L)[X] ↦ q.coeff n) e
  simp only [ZeroMemClass.coe_zero, sub_zero] at hcoeff
  refine toGr_eq_zero_of_mem _ ?_ fun h ↦ ?_ <;> dsimp only
  · cases n with
    | zero => rw [hcoeff, coeff_X_mul_zero]; exact zero_mem _
    | succ n => rw [hcoeff, coeff_X_mul]; exact hc n
  · subst h; rw [hcoeff, coeff_X_mul_zero]

theorem ker_toGr_zero : LinearMap.ker (toGr R L 0) = ⊥ :=
  LinearMap.ker_eq_bot'.mpr fun x ↦ (toGr_zero_eq_zero_iff x).mp

theorem ker_toGr_succ (n : ℕ) :
    LinearMap.ker (toGr R L (n + 1)) =
      (filtration R L n).comap (filtration R L (n + 1)).subtype := by
  ext x
  exact toGr_succ_eq_zero_iff x

variable (R L) in
/-- The graded piece of degree `n + 1` of `AssociatedGraded R L` is `F_{n+1} / Fₙ`. -/
def quotEquivRangeToGr (n : ℕ) :
    (filtration R L (n + 1) ⧸ (filtration R L n).comap (filtration R L (n + 1)).subtype) ≃ₗ[R]
      LinearMap.range (toGr R L (n + 1)) :=
  (Submodule.quotEquivOfEq ((filtration R L n).comap (filtration R L (n + 1)).subtype)
    (LinearMap.ker (toGr R L (n + 1))) (ker_toGr_succ n).symm).trans
    (toGr R L (n + 1)).quotKerEquivRange

/-- `AssociatedGraded R L` is the internal direct sum of the images of the `toGr R L n`, i.e. of
the graded pieces `Fₙ / F_{n-1}`. -/
theorem isInternal_range_toGr : DirectSum.IsInternal fun n ↦ LinearMap.range (toGr R L n) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, iSup_range_toGr⟩
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum
  have : ∀ i, ∃ y : filtration R L i, i ∈ s → toGr R L i y = v i := fun i ↦ by
    by_cases hi : i ∈ s
    · obtain ⟨y, hy⟩ := hv i hi
      exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h ↦ absurd h hi⟩
  choose x hx using this
  let p : reesAlgebra R L := ∑ i ∈ s, reesMonomial R L i (x i)
  have hp : AssociatedGraded.mk p = 0 := by
    rw [← hsum, map_sum]
    exact Finset.sum_congr rfl fun i hi ↦ hx i hi
  intro i hi
  have := (mk_eq_zero_iff p).mp hp i
  rw [← hx i hi, ← this]
  refine toGr_congr rfl ?_
  simp only [p, AddSubmonoidClass.coe_finsetSum, coe_reesMonomial, finsetSum_coeff,
    coeff_monomial, Finset.sum_ite_eq', hi, ↓reduceIte]

/-- The images of the `toGr R L n` form an algebra grading of `AssociatedGraded R L`. -/
instance : SetLike.GradedMonoid fun n ↦ LinearMap.range (toGr R L n) where
  one_mem := ⟨⟨1, one_mem_filtration 0⟩, by
    rw [toGr_apply, ← map_one AssociatedGraded.mk]
    rfl⟩
  mul_mem := by
    rintro m n _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨_, (toGr_mul x y).symm⟩

theorem toGr_mul_comm {m n : ℕ} (x : filtration R L m) (y : filtration R L n) :
    toGr R L m x * toGr R L n y = toGr R L n y * toGr R L m x := by
  rw [toGr_mul, toGr_mul, toGr_congr (add_comm n m)
    (y := ⟨(y * x : UniversalEnvelopingAlgebra R L), add_comm n m ▸ mul_mem_filtration y.2 x.2⟩)
    rfl]
  have hc := commutator_mem_filtration x.2 y.2
  have h0 : toGr R L (m + n) ⟨(x * y - y * x : UniversalEnvelopingAlgebra R L),
      sub_mem (mul_mem_filtration x.2 y.2) (add_comm n m ▸ mul_mem_filtration y.2 x.2)⟩ = 0 := by
    refine toGr_eq_zero_of_mem _ hc fun h ↦ ?_
    obtain ⟨r, hr⟩ := mem_filtration_zero.mp (show (x : UniversalEnvelopingAlgebra R L) ∈
      filtration R L 0 from (show m = 0 by omega) ▸ x.2)
    simp [← hr, Algebra.commutes]
  conv_rhs => rw [← add_zero (toGr R L (m + n) _), ← h0, ← map_add]
  congr 1
  ext1
  simp

/-- The associated graded algebra of `U(L)` is commutative: this is a consequence of
`commutator_mem_filtration`. -/
instance AssociatedGraded.instCommRing : CommRing (AssociatedGraded R L) where
  __ := (inferInstance : Ring (AssociatedGraded R L))
  mul_comm a b := by
    change Commute a b
    have ha : a ∈ ⨆ n, LinearMap.range (toGr R L n) := by
      rw [iSup_range_toGr]; exact Submodule.mem_top
    have hb : b ∈ ⨆ n, LinearMap.range (toGr R L n) := by
      rw [iSup_range_toGr]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun a ↦ Commute a b) ha ?_
      (Commute.zero_left b) fun _ _ h₁ h₂ ↦ h₁.add_left h₂
    rintro m _ ⟨x, rfl⟩
    refine Submodule.iSup_induction _ (motive := fun b ↦ Commute (toGr R L m x) b) hb ?_
      (Commute.zero_right _) fun _ _ h₁ h₂ ↦ h₁.add_right h₂
    rintro n _ ⟨y, rfl⟩
    exact toGr_mul_comm x y

variable (R L) in
/-- The linear map `L → gr U(L)`, `x ↦ [ι x] ∈ F₁ / F₀`. -/
def ιGr : L →ₗ[R] AssociatedGraded R L :=
  toGr R L 1 ∘ₗ (ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L).toLinearMap.codRestrict _
    ι_mem_filtration_one

variable (R L) in
/-- The canonical algebra map `Sym(L) → gr U(L)` extending `x ↦ [ι x] ∈ F₁ / F₀`. -/
def symmetricAlgebraToAssociatedGraded : SymmetricAlgebra R L →ₐ[R] AssociatedGraded R L :=
  SymmetricAlgebra.lift (ιGr R L)

@[simp] theorem symmetricAlgebraToAssociatedGraded_ι (x : L) :
    symmetricAlgebraToAssociatedGraded R L (SymmetricAlgebra.ι R L x) =
      toGr R L 1 ⟨ι R x, ι_mem_filtration_one x⟩ :=
  SymmetricAlgebra.lift_ι_apply (ιGr R L) x

theorem toGr_zero_one : toGr R L 0 ⟨1, one_mem_filtration 0⟩ = 1 := by
  rw [toGr_apply, ← map_one AssociatedGraded.mk]
  rfl

/-- Every graded piece lies in the image of `Sym(L)`. -/
theorem toGr_mem_range (n : ℕ) (x : filtration R L n) :
    toGr R L n x ∈ (symmetricAlgebraToAssociatedGraded R L).range := by
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    have : toGr R L 0 ⟨algebraMap R _ r, algebraMap_mem_filtration r 0⟩ =
        algebraMap R (AssociatedGraded R L) r := by
      rw [toGr_apply, ← AlgHom.commutes (AssociatedGraded.mk (R := R) (L := L)) r]
      rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y i hx hy h₁ h₂ =>
    have := add_mem h₁ h₂
    rwa [← map_add] at this
  | mem_mul g hg i x hx ih =>
    have hx' : x ∈ filtration R L i := hx
    obtain ⟨y, hy, z, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hg
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hy
    have h₁ : algebraMap R _ r * x ∈ filtration R L (i + 1) := by
      rw [Algebra.algebraMap_eq_smul_one, smul_one_mul]
      exact Submodule.smul_mem _ _ (filtration_mono (Nat.le_succ i) hx)
    have h₂ : ι R w * x ∈ filtration R L (i + 1) := by
      rw [filtration_succ]
      exact Submodule.mul_mem_mul (Submodule.mem_sup_right ⟨w, rfl⟩) hx
    have e : (⟨(algebraMap R _ r + (ι R : L →ₗ⁅R⁆ UniversalEnvelopingAlgebra R L).toLinearMap w)
        * x, by rw [filtration_succ]; exact Submodule.mul_mem_mul hg hx⟩ :
        filtration R L (i + 1)) =
        ⟨_, h₁⟩ + ⟨_, h₂⟩ := Subtype.ext (add_mul _ _ _)
    rw [e, map_add, (toGr_succ_eq_zero_iff _).mpr, zero_add,
      ← toGr_congr (add_comm 1 i)
        (x := ⟨ι R w * x, mul_mem_filtration (ι_mem_filtration_one w) hx'⟩) rfl]
    · have := mul_mem (show toGr R L 1 ⟨ι R w, ι_mem_filtration_one w⟩ ∈
        (symmetricAlgebraToAssociatedGraded R L).range from
          ⟨SymmetricAlgebra.ι R L w, symmetricAlgebraToAssociatedGraded_ι w⟩) ih
      rwa [toGr_mul] at this
    · dsimp only
      rw [Algebra.algebraMap_eq_smul_one, smul_one_mul]
      exact Submodule.smul_mem _ _ hx

variable (R L) in
/-- The canonical map `Sym(L) → gr U(L)` is surjective, for any Lie algebra `L`. -/
theorem symmetricAlgebraToAssociatedGraded_surjective :
    Function.Surjective (symmetricAlgebraToAssociatedGraded R L) := by
  intro a
  have ha : a ∈ ⨆ n, LinearMap.range (toGr R L n) := by
    rw [iSup_range_toGr]; exact Submodule.mem_top
  refine (AlgHom.mem_range _).mp (Submodule.iSup_induction _
    (motive := fun a ↦ a ∈ (symmetricAlgebraToAssociatedGraded R L).range) ha ?_ (zero_mem _)
    fun _ _ ↦ add_mem)
  rintro n _ ⟨x, rfl⟩
  exact toGr_mem_range n x

section PBW

open PBW MvPolynomial

variable {σ : Type*} [LinearOrder σ] (b : Basis σ R L)

/-- Under `Sym(L) ≅ R[X_i]` (from a basis `b`), the monomial `X^s` maps to the class of the
ordered monomial `pbwMonomial R b s` in degree `|s|`. -/
theorem symmetricAlgebraToAssociatedGraded_symm_monomial (m : ℕ) : ∀ s : σ →₀ ℕ,
    s.degree = m → symmetricAlgebraToAssociatedGraded R L
      ((SymmetricAlgebra.equivMvPolynomial b).symm (monomial s 1)) =
      toGr R L s.degree ⟨pbwMonomial R b s, pbwMonomial_mem_filtration b s⟩ := by
  induction m with
  | zero =>
    intro s hs
    rw [Finsupp.degree_eq_zero_iff] at hs
    subst hs
    rw [monomial_zero', MvPolynomial.C_1, map_one, map_one, ← toGr_zero_one]
    exact toGr_congr (by simp) (by simp)
  | succ m ih =>
    intro s hs
    have hne : s.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
      rintro rfl; simp at hs
    have hts := sub_add_single_minIdx s hne
    have ht := leAll_minIdx s hne
    have htdeg := degree_sub_single_minIdx s hne
    set t := s - Finsupp.single (minIdx s hne) 1
    set j := minIdx s hne
    have e : monomial s (1 : R) = MvPolynomial.X j * monomial t 1 := by
      rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul, ← hts, add_comm]
    rw [e, map_mul, map_mul, SymmetricAlgebra.equivMvPolynomial_symm_X,
      symmetricAlgebraToAssociatedGraded_ι, ih t (by omega), toGr_mul]
    exact toGr_congr (by omega) (by dsimp only; rw [← hts, pbwMonomial_add_single ht])

namespace PBW

/-- Auxiliary map for the graded PBW theorem: `X^s ↦ pbwMonomial R b s • t ^ |s|`. -/
def reesLift : MvPolynomial σ R →ₗ[R] reesAlgebra R L :=
  (basisMonomials σ R).constr R fun s ↦
    reesMonomial R L s.degree ⟨pbwMonomial R b s, pbwMonomial_mem_filtration b s⟩

theorem mk_reesLift (P : MvPolynomial σ R) :
    AssociatedGraded.mk (reesLift b P) =
      symmetricAlgebraToAssociatedGraded R L ((SymmetricAlgebra.equivMvPolynomial b).symm P) := by
  have : AssociatedGraded.mk.toLinearMap ∘ₗ reesLift b =
      (symmetricAlgebraToAssociatedGraded R L).toLinearMap ∘ₗ
        (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearMap :=
    (basisMonomials σ R).ext fun s ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, reesLift, Basis.constr_basis,
        AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply]
      rw [coe_basisMonomials, symmetricAlgebraToAssociatedGraded_symm_monomial b _ s rfl]
      rfl
  exact LinearMap.congr_fun this P

/-- Auxiliary map for the graded PBW theorem: `∑ₙ uₙ tⁿ ↦ ∑ₙ (pbwEquiv b uₙ)_{(n)}`, where
`p_{(n)}` is the homogeneous component of degree `n`. -/
def grInv : (UniversalEnvelopingAlgebra R L)[X] →ₗ[R] MvPolynomial σ R :=
  Polynomial.lsum fun n ↦ (homogeneousComponent n).comp (pbwEquiv b).toLinearMap

theorem grInv_monomial (n : ℕ) (a : UniversalEnvelopingAlgebra R L) :
    grInv b (Polynomial.monomial n a) = homogeneousComponent n (pbwEquiv b a) := by
  simp [grInv, sum_monomial_index]

theorem grInv_reesLift (P : MvPolynomial σ R) : grInv b (reesLift b P) = P := by
  have : grInv b ∘ₗ (reesAlgebra R L).val.toLinearMap ∘ₗ reesLift b = LinearMap.id :=
    (basisMonomials σ R).ext fun s ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, reesLift, Basis.constr_basis,
        AlgHom.toLinearMap_apply, Subalgebra.coe_val, coe_reesMonomial, grInv_monomial,
        pbwEquiv_pbwMonomial, LinearMap.id_apply]
      rw [coe_basisMonomials]
      exact homogeneousComponent_eq_self (isHomogeneous_monomial 1 rfl)
  exact LinearMap.congr_fun this P

theorem grInv_X_mul {c : (UniversalEnvelopingAlgebra R L)[X]} (hc : c ∈ reesAlgebra R L) :
    grInv b (Polynomial.X * c) = 0 := by
  conv_lhs => rw [as_sum_support c, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun n _ ↦ ?_
  rw [X_mul_monomial, grInv_monomial]
  refine homogeneousComponent_eq_zero _ _ (lt_of_le_of_lt ?_ n.lt_succ_self)
  exact (mem_restrictTotalDegree _ _ _).mp ((mem_filtration_iff_pbwEquiv b).mp (hc n))

end PBW

open PBW in
include b in
/-- If `L` has a basis, the canonical map `Sym(L) → gr U(L)` is injective. -/
theorem symmetricAlgebraToAssociatedGraded_injective_of_basis :
    Function.Injective (symmetricAlgebraToAssociatedGraded R L) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨P, rfl⟩ := (SymmetricAlgebra.equivMvPolynomial b).symm.surjective a
  rw [← mk_reesLift, ← map_zero AssociatedGraded.mk, mk_eq_mk_iff] at ha
  obtain ⟨c, hc, e⟩ := ha
  have := congr_arg (grInv b) e
  rw [ZeroMemClass.coe_zero, sub_zero, grInv_reesLift, grInv_X_mul b hc] at this
  rw [this, map_zero]

end PBW

variable (R L) in
/-- **Poincaré–Birkhoff–Witt theorem, graded form**: if `L` is a free `R`-module, the canonical
map `Sym(L) → gr U(L)` is an isomorphism. See Humphreys, *Introduction to Lie algebras and
representation theory*, §17.3, PBW Theorem (proved in §17.4), stated there over a field;
and Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.7, Theorem 1. The proof here
deduces it from the PBW basis (`UniversalEnvelopingAlgebra.pbwBasis`) and its filtered version
(`UniversalEnvelopingAlgebra.map_pbwEquiv_filtration`). -/
theorem symmetricAlgebraToAssociatedGraded_bijective [Module.Free R L] :
    Function.Bijective (symmetricAlgebraToAssociatedGraded R L) := by
  let : LinearOrder (Module.Free.ChooseBasisIndex R L) := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨symmetricAlgebraToAssociatedGraded_injective_of_basis (Module.Free.chooseBasis R L),
    symmetricAlgebraToAssociatedGraded_surjective R L⟩

variable (R L) in
/-- **Poincaré–Birkhoff–Witt theorem, graded form**: the algebra isomorphism
`Sym(L) ≃ₐ[R] gr U(L)` for `L` free over `R`. See
`UniversalEnvelopingAlgebra.symmetricAlgebraToAssociatedGraded_bijective`. -/
def symmetricAlgebraEquivAssociatedGraded [Module.Free R L] :
    SymmetricAlgebra R L ≃ₐ[R] AssociatedGraded R L :=
  AlgEquiv.ofBijective _ (symmetricAlgebraToAssociatedGraded_bijective R L)

@[simp] theorem symmetricAlgebraEquivAssociatedGraded_ι [Module.Free R L] (x : L) :
    symmetricAlgebraEquivAssociatedGraded R L (SymmetricAlgebra.ι R L x) =
      toGr R L 1 ⟨ι R x, ι_mem_filtration_one x⟩ :=
  symmetricAlgebraToAssociatedGraded_ι x

end UniversalEnvelopingAlgebra
