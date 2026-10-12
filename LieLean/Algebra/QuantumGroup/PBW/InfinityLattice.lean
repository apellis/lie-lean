/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.PBW.ProductNorm.IntrinsicDegree

/-!
# Infinity-local coordinates of original PBW elements

The headline `intersectionBasis` gives an infinity-local basis of the existing lattice
intersected with the field span of the original PBW elements for any reduced word.
Its coefficient integrality follows from the actual pairing and unit PBW norms.
Reconstructed proof; no canonical-basis or bar-invariance assertion.
-/

noncomputable section
open LieLean LieLean.QuantumGroup LusztigF Modified
namespace PBWInfinityLattice
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝔄" => InfinityLocalRing
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)
  {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}

/-- The existing Kashiwara lattice with its actual restricted scalar action. -/
def lattice (D : LusztigCartanDatum I) : Submodule 𝔄 (Quotient D 𝕧) :=
  (GrandLoop.latInf (D := D) transcendental_ratFunc_X 𝔄).comap
    ({ toFun := (negativeQuotientEquiv D).symm
       map_add' := (negativeQuotientEquiv D).symm.map_add
       map_smul' := fun a x ↦ by
         change (negativeQuotientEquiv D).symm ((algebraMap 𝔄 𝕂 a) • x) = _
         rw [map_smul, algebraMap_smul]
         rfl } : Quotient D 𝕧 →ₗ[𝔄] GrandLoop.Um D 𝕧)

/-- This submodule has precisely the original lattice's membership predicate. -/
theorem mem_lattice_iff (x : Quotient D 𝕧) :
    x ∈ lattice D ↔ x ∈ quotientCrystalLattice D := Iff.rfl

/-- The actual form is integral on arbitrary, not necessarily homogeneous, lattice inputs. -/
theorem pairing_integral {x y : Quotient D 𝕧}
    (hx : x ∈ quotientCrystalLattice D) (hy : y ∈ quotientCrystalLattice D) :
    ∃ a : 𝔄, quotientForm D x y = algebraMap 𝔄 𝕂 a := by
  let := Fintype.ofFinite I
  exact GrandLoop.formU_mem (hvt := transcendental_ratFunc_X)
    (hR := D.isXRegular_extendedRootDatum)
    InfinityLocalRing.injective_algebraMap InfinityLocalRing.uniformizer_mem_maximalIdeal
    InfinityLocalRing.algebraMap_uniformizer InfinityLocalRing.exists_pow_mul
    D.exists_fundamental_extendedRootDatum hx hy

/-- Unit norm is derived from the actual PBW norm congruence. -/
theorem norm_unit {w : List I} (hw : cs.IsReduced w) (c : Fin w.length → ℕ) :
    ∃ u : 𝔄ˣ, quotientForm D (integralPBWPreimage R hw c)
      (integralPBWPreimage R hw c) = algebraMap 𝔄 𝕂 (u : 𝔄) := by
  obtain ⟨a, ha⟩ := PBWProductNorm.norm_residue R hw c
  obtain ⟨u, hu⟩ := isUnit_one_add_mul InfinityLocalRing.uniformizer_mem_maximalIdeal a
  exact ⟨u, ha.trans (congrArg (algebraMap 𝔄 𝕂) hu.symm)⟩

/-- Orthogonality extracts a coefficient of any finite field expansion. -/
theorem pairing_sum {w : List I} (hw : cs.IsReduced w)
    (a : (Fin w.length → ℕ) →₀ 𝕂) (c : Fin w.length → ℕ) :
    quotientForm D (a.sum fun d k ↦ k • (integralPBWPreimage R hw d : Quotient D 𝕧))
      (integralPBWPreimage R hw c) =
      a c * quotientForm D (integralPBWPreimage R hw c) (integralPBWPreimage R hw c) := by
  classical
  rw [Finsupp.sum, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  change a.sum (fun d k ↦ k * quotientForm D (integralPBWPreimage R hw d)
    (integralPBWPreimage R hw c)) = _
  apply Finsupp.sum_eq_single c
  · intro d _ hdc
    rw [PBWProductNorm.orthogonal R hw d c hdc, mul_zero]
  · intro _
    exact zero_mul _

/-- Every coefficient of a finite PBW expansion in the actual lattice is infinity-integral. -/
theorem coefficients_integral {w : List I} (hw : cs.IsReduced w)
    (a : (Fin w.length → ℕ) →₀ 𝕂)
    (ha : (a.sum fun c k ↦ k • (integralPBWPreimage R hw c : Quotient D 𝕧)) ∈
      quotientCrystalLattice D) (c : Fin w.length → ℕ) :
    ∃ b : 𝔄, a c = algebraMap 𝔄 𝕂 b := by
  obtain ⟨b, hb⟩ := pairing_integral ha (PBWProductNorm.mem_lattice_degree R hw c)
  obtain ⟨u, hu⟩ := norm_unit R hw c
  rw [pairing_sum R hw a c, hu] at hb
  refine ⟨b * ↑(u⁻¹), ?_⟩
  have h := congrArg (fun z : 𝕂 ↦ z * algebraMap 𝔄 𝕂 (↑(u⁻¹) : 𝔄)) hb
  simpa only [mul_assoc, ← _root_.map_mul, Units.mul_inv, _root_.map_one, mul_one] using h

/-- Independence follows from the actual pairing, without a basis hypothesis. -/
theorem field_linearIndependent {w : List I} (hw : cs.IsReduced w) :
    LinearIndependent 𝕂 (fun c ↦ (integralPBWPreimage R hw c : Quotient D 𝕧)) := by
  intro a b hab
  ext c
  have h := congrArg (fun x ↦ quotientForm D x (integralPBWPreimage R hw c)) hab
  simp only [Finsupp.linearCombination_apply] at h
  rw [pairing_sum R hw a c, pairing_sum R hw b c] at h
  obtain ⟨u, hu⟩ := norm_unit R hw c
  rw [hu] at h
  exact mul_right_cancel₀ (u.isUnit.map (algebraMap 𝔄 𝕂)).ne_zero h

/-- Independence over the actual infinity local ring. -/
theorem local_linearIndependent {w : List I} (hw : cs.IsReduced w) :
    LinearIndependent 𝔄 (fun c ↦ (integralPBWPreimage R hw c : Quotient D 𝕧)) := by
  apply LinearIndependent.restrict_scalars (K := 𝕂) _ (field_linearIndependent R hw)
  simpa only [Algebra.smul_def, mul_one] using InfinityLocalRing.injective_algebraMap

/-- The genuine submodule intersection inside the original radical quotient. -/
def intersection {w : List I} (hw : cs.IsReduced w) : Submodule 𝔄 (Quotient D 𝕧) :=
  lattice D ⊓ (Submodule.span 𝕂
    (Set.range fun c ↦ (integralPBWPreimage R hw c : Quotient D 𝕧))).restrictScalars 𝔄

/-- Membership is membership in the old lattice and the original PBW field span. -/
theorem mem_intersection_iff {w : List I} (hw : cs.IsReduced w) (x : Quotient D 𝕧) :
    x ∈ intersection R hw ↔ x ∈ quotientCrystalLattice D ∧
      x ∈ Submodule.span 𝕂 (Set.range fun c ↦
        (integralPBWPreimage R hw c : Quotient D 𝕧)) := Iff.rfl

/-- Coefficient integrality identifies the intersection with the local PBW span. -/
theorem intersection_eq_span {w : List I} (hw : cs.IsReduced w) :
    intersection R hw = Submodule.span 𝔄
      (Set.range fun c ↦ (integralPBWPreimage R hw c : Quotient D 𝕧)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx.2
    have hi := coefficients_integral R hw a hx.1
    classical
    apply Submodule.sum_mem
    intro c _
    obtain ⟨b, hb⟩ := hi c
    rw [hb]
    change (algebraMap 𝔄 𝕂 b) • (integralPBWPreimage R hw c : Quotient D 𝕧) ∈ _
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ b (Submodule.subset_span ⟨c, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    exact ⟨PBWProductNorm.mem_lattice_degree R hw c, Submodule.subset_span ⟨c, rfl⟩⟩

/-- In the original PBW field span, the old lattice is exactly the infinity-local span. -/
theorem mem_lattice_iff_mem_span {w : List I} (hw : cs.IsReduced w)
    {x : Quotient D 𝕧} (hx : x ∈ Submodule.span 𝕂
      (Set.range fun c ↦ (integralPBWPreimage R hw c : Quotient D 𝕧))) :
    x ∈ quotientCrystalLattice D ↔ x ∈ Submodule.span 𝔄
      (Set.range fun c ↦ (integralPBWPreimage R hw c : Quotient D 𝕧)) := by
  rw [← intersection_eq_span R hw, mem_intersection_iff]
  exact ⟨fun h ↦ ⟨h, hx⟩, And.left⟩

/-- The original PBW elements form an infinity-local basis of the actual intersection. -/
def intersectionBasis {w : List I} (hw : cs.IsReduced w) :
    Module.Basis (Fin w.length → ℕ) 𝔄 (intersection R hw) :=
  (Module.Basis.span (local_linearIndependent R hw)).map
    (LinearEquiv.ofEq _ _ (intersection_eq_span R hw).symm)

/-- The basis evaluates to the original integral PBW preimage, not a replacement family. -/
theorem intersectionBasis_apply {w : List I} (hw : cs.IsReduced w)
    (c : Fin w.length → ℕ) :
    (intersectionBasis R hw c : Quotient D 𝕧) = integralPBWPreimage R hw c := by
  simp [intersectionBasis, Module.Basis.span_apply]

end PBWInfinityLattice
