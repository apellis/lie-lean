/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.VermaHom

/-!
# Full-centre characters of Verma modules

## Main definitions

* `centralCharacter`: the actual `K`-algebra character of the full enveloping centre.

## Main results

* `centralCharacter_smul`: the centre acts through this character on the whole Verma module.
* `centralCharacter_eq_of_hom_ne_zero`: nonzero Verma maps force equality of characters.
* `rep_center_map`, `rep_center_eq_of_surjective`: scalar action on images and quotients.
* `centralCharacter_weyl_of_integral`: integral dot-Weyl invariance for generalized Cartan
  matrices, proved through actual simple-reflection embeddings in either direction.

## Proof and source status

The actual centre `Subalgebra.center K U(g)` acts by scalars on every Verma module.
The scalar is constructed from the one-dimensional top weight space and cyclicity,
not assumed. It defines a `K`-algebra character. Nonzero Verma morphisms force equality
of these characters. Arguments reconstructed.
This does not construct central block projections or a Harish-Chandra isomorphism.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝓤" => UniversalEnvelopingAlgebra K (KacMoodyAlgebra P)
local notation "𝓩" => Subalgebra.center K 𝓤

/-- A central enveloping element commutes with every enveloping action. -/
theorem center_smul_comm (Λ : Dual K H) (z : 𝓩) (u : 𝓤) (m : VermaModule P Λ) :
    u • ((z : 𝓤) • m) = (z : 𝓤) • (u • m) := by
  rw [← mul_smul, ← mul_smul, Subalgebra.mem_center_iff.mp z.property u]

/-- The centre preserves the top weight space; reconstructed from centrality. -/
theorem center_smul_hwv_mem (Λ : Dual K H) (z : 𝓩) :
    (z : 𝓤) • hwv P Λ ∈ weightSpace P Λ Λ := by
  intro a
  change UniversalEnvelopingAlgebra.ι K (h P a) • ((z : 𝓤) • hwv P Λ) = _
  rw [center_smul_comm, ← lie_eq_smul, lie_h_hwv, smul_algebra_smul_comm]

variable [CharZero K]

/-- Every central element acts by a scalar, proved from the top weight space and generation.
The argument is reconstructed, with no finite-type or algebraic-closure hypothesis. -/
theorem exists_center_smul_eq (Λ : Dual K H) (z : 𝓩) :
    ∃ c : K, ∀ m : VermaModule P Λ, (z : 𝓤) • m = c • m := by
  have hz := center_smul_hwv_mem P Λ z
  rw [weightSpace_self, Submodule.mem_span_singleton] at hz
  obtain ⟨c, hc⟩ := hz
  refine ⟨c, fun m ↦ ?_⟩
  obtain ⟨u, rfl⟩ := mk_surjective P Λ m
  rw [mk_eq_smul, ← center_smul_comm, ← hc, smul_algebra_smul_comm]

/-- The scalar of a central enveloping element on a Verma module. -/
def centralScalar (Λ : Dual K H) (z : 𝓩) : K :=
  Classical.choose (exists_center_smul_eq P Λ z)

/-- The constructed scalar is the actual action on every vector. -/
theorem center_smul_eq (Λ : Dual K H) (z : 𝓩) (m : VermaModule P Λ) :
    (z : 𝓤) • m = centralScalar P Λ z • m :=
  Classical.choose_spec (exists_center_smul_eq P Λ z) m

/-- The full-centre character of `M(Λ)`, as a field-algebra homomorphism.
Reconstructed from central scalar action and the PBW nonvanishing of the highest vector. -/
def centralCharacter (Λ : Dual K H) : 𝓩 →ₐ[K] K where
  toFun := centralScalar P Λ
  map_one' := by
    apply smul_left_injective K (hwv_ne_zero P Λ)
    dsimp only
    rw [← center_smul_eq]
    simp
  map_mul' z w := by
    apply smul_left_injective K (hwv_ne_zero P Λ)
    dsimp only
    rw [← center_smul_eq, Subalgebra.coe_mul, mul_smul, center_smul_eq,
      center_smul_eq, smul_smul]
  map_zero' := by
    apply smul_left_injective K (hwv_ne_zero P Λ)
    dsimp only
    rw [← center_smul_eq]
    simp
  map_add' z w := by
    apply smul_left_injective K (hwv_ne_zero P Λ)
    dsimp only
    rw [← center_smul_eq, Subalgebra.coe_add, add_smul, center_smul_eq,
      center_smul_eq, add_smul]
  commutes' c := by
    apply smul_left_injective K (hwv_ne_zero P Λ)
    dsimp only
    rw [← center_smul_eq]
    change algebraMap K 𝓤 c • hwv P Λ = c • hwv P Λ
    exact algebraMap_smul 𝓤 c (hwv P Λ)

/-- The full-centre character gives the actual scalar action, not only the top action. -/
theorem centralCharacter_smul (Λ : Dual K H) (z : 𝓩) (m : VermaModule P Λ) :
    (z : 𝓤) • m = centralCharacter P Λ z • m :=
  center_smul_eq P Λ z m

/-- Every nonzero Verma morphism forces equality of the full-centre characters.
Reconstructed using equivariance and scalar cancellation at the nonzero image of `hwv`. -/
theorem centralCharacter_eq_of_hom_ne_zero {Λ μ : Dual K H}
    (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) (hφ : φ ≠ 0) :
    centralCharacter P μ = centralCharacter P Λ := by
  ext z
  have hv : φ (hwv P μ) ≠ 0 := fun he ↦ hφ ((eq_zero_iff P φ).mpr he)
  apply smul_left_injective K hv
  dsimp only
  rw [← map_smul, ← centralCharacter_smul, map_smul_eq_smul, centralCharacter_smul]

/-- Distinct full-centre characters exclude every Verma morphism. -/
theorem hom_eq_zero_of_centralCharacter_ne {Λ μ : Dual K H}
    (hne : centralCharacter P μ ≠ centralCharacter P Λ)
    (φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ) : φ = 0 := by
  by_contra hφ
  exact hne (centralCharacter_eq_of_hom_ne_zero P φ hφ)

/-- The full-centre character is uniquely determined by its scalar action on the highest
vector; no character-existence hypothesis enters its construction. Reconstructed. -/
theorem centralCharacter_unique (Λ : Dual K H) (χ : 𝓩 →ₐ[K] K)
    (hχ : ∀ z : 𝓩, (z : 𝓤) • hwv P Λ = χ z • hwv P Λ) :
    χ = centralCharacter P Λ := by
  ext z
  exact smul_left_injective K (hwv_ne_zero P Λ)
    ((hχ z).symm.trans (centralCharacter_smul P Λ z (hwv P Λ)))

/-- Every Verma morphism has image in the genuine central eigenspace for its source
character, even when the target is not generated by that image. Reconstructed. -/
theorem rep_center_map (Λ : Dual K H) {V : Type*} [AddCommGroup V]
    [Module K V] [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (z : 𝓩) (m : VermaModule P Λ) :
    rep P V (z : 𝓤) (φ m) = centralCharacter P Λ z • φ m := by
  rw [← map_smul_eq_rep, centralCharacter_smul, map_smul]

/-- Scalar action passes to every module generated by a surjective Verma morphism.
In particular this applies to the irreducible highest-weight quotient. Reconstructed. -/
theorem rep_center_eq_of_surjective (Λ : Dual K H) {V : Type*} [AddCommGroup V]
    [Module K V] [LieRingModule P.KacMoodyAlgebra V] [LieModule K P.KacMoodyAlgebra V]
    (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (z : 𝓩) (v : V) : rep P V (z : 𝓤) v = centralCharacter P Λ z • v := by
  obtain ⟨m, rfl⟩ := hφ v
  rw [← map_smul_eq_rep, centralCharacter_smul, map_smul]

/-- A positive-integral simple-reflection embedding preserves the full-centre character.
Reconstructed from the actual embedding, not from a Casimir equality. -/
theorem centralCharacter_reflection_of_pos (hA : A.IsGeneralizedCartan)
    {Λ : Dual K H} {i : ι} {n : ℕ} (hn0 : 0 < n)
    (hn : (Λ + P.rho) (P.coroot i) = n) :
    centralCharacter P (P.reflection hA i (Λ + P.rho) - P.rho) = centralCharacter P Λ := by
  obtain ⟨φ, hφ, _⟩ := exists_injective_reflection P hA hn0 hn
  apply centralCharacter_eq_of_hom_ne_zero P φ
  intro he
  exact hwv_ne_zero P _ (hφ (by rw [he, _root_.zero_apply, map_zero]))

/-- Simple dot reflections preserve the full-centre character at integral pairings.
For a negative pairing the actual embedding is used in the reverse direction; the zero
pairing fixes the weight. Reconstructed, valid for generalized Cartan matrices. -/
theorem centralCharacter_reflection_of_integral (hA : A.IsGeneralizedCartan)
    {Λ : Dual K H} (i : ι) (hi : ∃ n : ℤ, (Λ + P.rho) (P.coroot i) = n) :
    centralCharacter P (P.reflection hA i (Λ + P.rho) - P.rho) = centralCharacter P Λ := by
  obtain ⟨n, hn⟩ := hi
  rcases lt_trichotomy n 0 with hneg | rfl | hpos
  · have hcast : ((-n).toNat : K) = -(n : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]
    have hp : 0 < (-n).toNat := by omega
    have he := centralCharacter_reflection_of_pos P hA
      (Λ := P.reflection hA i (Λ + P.rho) - P.rho) hp (i := i) (by
        rw [sub_add_cancel, P.reflection_apply_coroot_self, hn, hcast])
    simpa only [sub_add_cancel, P.reflection_reflection, add_sub_cancel_right] using he.symm
  · rw [P.reflection_apply, hn, Int.cast_zero, zero_smul, sub_zero, add_sub_cancel_right]
  · have hcast : (n.toNat : K) = (n : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    exact centralCharacter_reflection_of_pos P hA (by omega) (hn.trans hcast.symm)

/-- Integral dot-Weyl invariance of actual full-centre Verma characters.
Reconstructed by induction through actual simple-reflection embeddings in either direction.
Finite type is not needed; this theorem does not claim nonintegral dot-Weyl invariance. -/
theorem centralCharacter_weyl_of_integral (hA : A.IsGeneralizedCartan)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (Λ : Dual K H) (hΛ : ∀ i, ∃ n : ℤ, Λ (P.coroot i) = n) :
    centralCharacter P (w (Λ + P.rho) - P.rho) = centralCharacter P Λ := by
  have hρ : ∀ i, ∃ n : ℤ, (Λ + P.rho) (P.coroot i) = n := by
    intro i
    obtain ⟨n, hn⟩ := hΛ i
    exact ⟨n + 1, by simp [hn]⟩
  have aux := P.weylGroup_induction hA
    (p := fun w ↦ (∀ i, ∃ n : ℤ, w (Λ + P.rho) (P.coroot i) = n) ∧
      centralCharacter P (w (Λ + P.rho) - P.rho) = centralCharacter P Λ)
    (show (∀ i, ∃ n : ℤ, (1 : Dual K H ≃ₗ[K] Dual K H)
        (Λ + P.rho) (P.coroot i) = n) ∧ _ from
      ⟨hρ, by simp⟩) (fun i w ih ↦ ?_) hw
  · exact aux.2
  · constructor
    · intro j
      obtain ⟨nj, hj⟩ := ih.1 j
      obtain ⟨ni, hi⟩ := ih.1 i
      refine ⟨nj - A j i * ni, ?_⟩
      simp only [LinearEquiv.mul_apply, P.reflection_apply_apply,
        P.coreflection_coroot, map_sub, map_smul, hj, hi, smul_eq_mul,
        Int.cast_sub, Int.cast_mul]
    · rw [LinearEquiv.mul_apply]
      have he := centralCharacter_reflection_of_integral P hA
        (Λ := w (Λ + P.rho) - P.rho) i (by simpa only [sub_add_cancel] using ih.1 i)
      simpa only [sub_add_cancel] using he.trans ih.2

end Matrix.Realization.KacMoodyAlgebra.VermaModule
