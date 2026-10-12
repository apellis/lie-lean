/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm.Homogeneity

/-!
# The explicit intrinsic PBW degree

The signed Cartan recursion is `β(i :: w,c) = c₀ αᵢ + sᵢ β(w,tail c)`.
Its nonnegativity is proved from an actual homogeneous representative, so the associated
natural degree does not discard negative coordinates. Both degrees depend only on the
Cartan datum, reduced word and exponents, not on a realization or chosen basis.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF Modified
namespace PBWProductNorm
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU
variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I}

/-- The signed root-lattice degree, by the ordinary Cartan reflection recursion. -/
def signedDegree (D : LusztigCartanDatum I) :
    (w : List I) → (Fin w.length → ℕ) → I →₀ ℤ
  | [], _ => 0
  | i :: w, c => c 0 • Finsupp.single i 1 + signedDegree D w (fun n ↦ c n.succ) -
      ((signedDegree D w (fun n ↦ c n.succ)).sum fun j a ↦ a * D.cartanMatrix i j) •
        Finsupp.single i 1

/-- The candidate natural degree; nontruncation is proved below for every reduced word. -/
def degree (D : LusztigCartanDatum I) (w : List I) (c : Fin w.length → ℕ) : I →₀ ℕ :=
  (signedDegree D w c).mapRange Int.toNat (by simp)

omit [DecidableEq I] in
/-- The intrinsic signed degree has the actual inverse-braid PBW character. -/
theorem signedDegree_character (R : D.RootDatum Y) (w : List I) (c : Fin w.length → ℕ) :
    Finsupp.linearCombination ℤ R.root (signedDegree D w c) = pbwWt R w c := by
  induction w with
  | nil => simp [signedDegree, pbwWt]
  | cons i w ih =>
    simp only [signedDegree, map_sub, map_add, map_nsmul, map_smul,
      Finsupp.linearCombination_single, one_smul, pbwWt, comp_reflY_eq,
      ih]
    rw [← ih]
    rw [linearCombination_coroot]
    change c 0 • R.root i + _ - _ = c 0 • R.root i + (_ - _)
    abel

variable [Finite I] (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

/-- Explicit integer coordinates of an actual homogeneous representative. -/
theorem exists_homogeneous_signed {w : List I} (hw : cs.IsReduced w)
    (c : Fin w.length → ℕ) :
    ∃ ν : I →₀ ℕ, ν.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp) = signedDegree D w c ∧
      ∃ a : LusztigF 𝕂 I, a ∈ LusztigF.weightSpace 𝕂 ν ∧
        toQuotient D 𝕧 a = (integralPBWPreimage R hw c : Quotient D 𝕧) := by
  let := Fintype.ofFinite I
  obtain ⟨ν, hν, a, ha, he⟩ := exists_homogeneous_of_regular D.extendedRootDatum
    D.isXRegular_extendedRootDatum hw c
  have hdeg : ν.mapRange (fun n : ℕ ↦ (n : ℤ)) (by simp) = signedDegree D w c := by
    apply D.isXRegular_extendedRootDatum
    rw [linearCombination_natCast, signedDegree_character]
    exact hν
  exact ⟨ν, hdeg, a, ha,
    he.trans (preimage_realization_independent D.extendedRootDatum R hw c)⟩

/-- No coordinate is lost when passing from signed to natural PBW degree. -/
theorem signedDegree_nonneg {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ)
    (i : I) : 0 ≤ signedDegree D w c i := by
  let := Fintype.ofFinite I
  obtain ⟨ν, hν, _⟩ := exists_homogeneous_signed D.extendedRootDatum hw c
  rw [← hν, Finsupp.mapRange_apply]
  exact Int.natCast_nonneg _

/-- The original PBW preimage has precisely the intrinsic Cartan-recursive natural degree. -/
theorem homogeneous_degree {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    ∃ a : LusztigF 𝕂 I, a ∈ LusztigF.weightSpace 𝕂 (degree D w c) ∧
      toQuotient D 𝕧 a = (integralPBWPreimage R hw c : Quotient D 𝕧) := by
  obtain ⟨ν, hν, a, ha, he⟩ := exists_homogeneous_signed R hw c
  have hdeg : degree D w c = ν := by
    ext i
    simp [degree, ← hν]
  exact ⟨a, hdeg.symm ▸ ha, he⟩

/-- The exact degree premise of the accepted grand-loop norm criterion is now proved. -/
theorem homogeneous_Uw {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    (negativeQuotientEquiv D).symm (integralPBWPreimage R hw c) ∈
      GrandLoop.Uw D 𝕧 (degree D w c) := by
  obtain ⟨a, ha, he⟩ := homogeneous_degree R hw c
  rw [← he, negativeQuotientEquiv_symm_toQuotient]
  exact ⟨a, ha, rfl⟩

/-- General lattice membership at the computed intrinsic degree. -/
theorem mem_lattice_degree {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    (integralPBWPreimage R hw c : Quotient D 𝕧) ∈ quotientCrystalLattice D := by
  apply (mem_quotientCrystalLattice_iff D (homogeneous_Uw R hw c)).mpr
  obtain ⟨a, ha⟩ := norm_residue R hw c
  exact ⟨_, ha⟩

end PBWProductNorm
