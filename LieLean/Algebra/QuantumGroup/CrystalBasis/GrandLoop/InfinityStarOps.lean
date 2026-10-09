/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityStarB

/-!
# The operators `ẽᵢ*`, `f̃ᵢ*` on `U⁻`

Let `ẽᵢ* = * ẽᵢ *` and `f̃ᵢ* = * f̃ᵢ *` (`GrandLoop.kEs`, `GrandLoop.kFs`): the Kashiwara
operators of the boson structure `(e''ᵢ, · fᵢ)` of `U⁻` (`e''ᵢ` lifts `rᵢ`,
`GrandLoop.starU_e_starU_mk`). For `j ≠ i` the operators `e''ᵢ`, `· fᵢ` commute with `e'ⱼ`, `fⱼ ·`,
so the Kashiwara operators of the two structures commute exactly on `U⁻` (`GrandLoop.kE_kEs`,
`GrandLoop.kE_kFs`, `GrandLoop.kF_kEs`, `GrandLoop.kF_kFs`), and `ẽⱼ`, `f̃ⱼ` preserve `ker e''ᵢ`
(`GrandLoop.e_starU_kE_eq_zero`, `GrandLoop.e_starU_kF_eq_zero`). This is the part `j ≠ i` of
[Kas93a] Cor. 2.2.2, which Kashiwara deduces from the embeddings `Ψᵢ`; here it is a direct
computation in `U⁻`.

## References

* [Kas93a] M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*,
  Duke Math. J. 71 (1993), 839–858, §2.2.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

variable (hvt) in
/-- `ẽᵢ* = * ẽᵢ *` on `U⁻`. -/
def kEs (i : I) : Module.End k (Um D v) := starU D v ∘ₗ kE hvt i ∘ₗ starU D v

variable (hvt) in
/-- `f̃ᵢ* = * f̃ᵢ *` on `U⁻`. -/
def kFs (i : I) : Module.End k (Um D v) := starU D v ∘ₗ kF hvt i ∘ₗ starU D v

lemma kEs_apply (i : I) (u : Um D v) : kEs hvt i u = starU D v (kE hvt i (starU D v u)) := rfl

lemma kFs_apply (i : I) (u : Um D v) : kFs hvt i u = starU D v (kF hvt i (starU D v u)) := rfl

/-- `* e'ᵢ *` lifts `rᵢ`. -/
lemma starU_e_starU_mk (i : I) (y : LusztigF k I) :
    starU D v ((bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e
      (starU D v (Submodule.Quotient.mk y))) = Submodule.Quotient.mk (rDeriv D v i y) := by
  rw [starU_mk]
  change starU D v (Submodule.Quotient.mk (lDeriv D v i (rev k I y))) = _
  rw [starU_mk, lDeriv_rev, rev_rev]

omit [CharZero k] [DecidableEq I] [NeZero v] in
/-- `* fᵢ *` is right multiplication by `θᵢ`. -/
lemma starU_f_starU_mk (i : I) (y : LusztigF k I) :
    starU D v (NegativePart.f D v i (starU D v (Submodule.Quotient.mk y))) =
      Submodule.Quotient.mk (y * θ k i) := by
  rw [starU_mk, NegativePart.f_mk, starU_mk, rev_mul, rev_rev, rev_θ]

/-- For `j ≠ i`, `* e'ⱼ *` commutes with `e'ᵢ` and `fᵢ`. -/
lemma starU_e_starU_comm (i j : I) (u : Um D v) :
    starU D v ((bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e (starU D v
      ((bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e u))) =
    (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v
      ((bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e (starU D v u))) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  change starU D v ((bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e (starU D v
    (Submodule.Quotient.mk (lDeriv D v i y)))) = _
  rw [starU_e_starU_mk (hvt := hvt), starU_e_starU_mk (hvt := hvt)]
  change _ = Submodule.Quotient.mk (lDeriv D v i (rDeriv D v j y))
  rw [lDeriv_rDeriv]

lemma starU_e_starU_f_comm {i j : I} (hij : i ≠ j) (u : Um D v) :
    starU D v ((bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e (starU D v
      (NegativePart.f D v i u))) =
    NegativePart.f D v i (starU D v
      ((bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e (starU D v u))) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [NegativePart.f_mk, starU_e_starU_mk (hvt := hvt), starU_e_starU_mk (hvt := hvt),
    NegativePart.f_mk,
    rDeriv_θ_mul, ite_eq_right (Ne.symm hij), add_zero]

lemma starU_f_starU_e_comm {i j : I} (hij : i ≠ j) (u : Um D v) :
    starU D v (NegativePart.f D v j (starU D v
      ((bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e u))) =
    (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v
      (NegativePart.f D v j (starU D v u))) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  change starU D v (NegativePart.f D v j (starU D v
    (Submodule.Quotient.mk (lDeriv D v i y)))) = _
  rw [starU_f_starU_mk, starU_f_starU_mk]
  change _ = Submodule.Quotient.mk (lDeriv D v i (y * θ k j))
  rw [lDeriv_mul, lDeriv_θ, ite_eq_right hij, mul_zero, add_zero]

omit [CharZero k] [DecidableEq I] [NeZero v] in
lemma starU_f_starU_f_comm (i j : I) (u : Um D v) :
    starU D v (NegativePart.f D v j (starU D v (NegativePart.f D v i u))) =
    NegativePart.f D v i (starU D v (NegativePart.f D v j (starU D v u))) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [NegativePart.f_mk, starU_f_starU_mk, starU_f_starU_mk, NegativePart.f_mk, mul_assoc]

/-- For `j ≠ i`, the conjugates `* ẽⱼ *`, `* f̃ⱼ *` commute with `e'ᵢ`, `fᵢ`; hence `ẽᵢ*`, `f̃ᵢ*`
commute with `e'ⱼ`, `fⱼ`. -/
lemma kEs_e_comm {i j : I} (hij : i ≠ j) (u : Um D v) :
    kEs hvt i ((bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e u) =
      (bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e (kEs hvt i u) := by
  set B := bos (D := D) (pow_ne_one_of_transcendental' hvt)
  -- `φ = * e'ⱼ *` commutes with `e'ᵢ`, `fᵢ`, hence with `ẽᵢ`
  have h := BosonModule.map_eTilde (V := B i) (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) (B i)
    (starU D v ∘ₗ (B j).e ∘ₗ starU D v)
    (fun m ↦ starU_e_starU_comm (hvt := hvt) i j m)
    (fun m ↦ starU_e_starU_f_comm (hvt := hvt) hij m) (starU D v u)
  simp only [LinearMap.comp_apply, starU_starU] at h
  have h2 := congrArg (starU D v) h
  rw [starU_starU] at h2
  rw [kEs_apply, kEs_apply]
  exact h2.symm

lemma kEs_f_comm {i j : I} (hij : i ≠ j) (u : Um D v) :
    kEs hvt i (NegativePart.f D v j u) = NegativePart.f D v j (kEs hvt i u) := by
  set B := bos (D := D) (pow_ne_one_of_transcendental' hvt)
  have h := BosonModule.map_eTilde (V := B i) (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) (B i)
    (starU D v ∘ₗ NegativePart.f D v j ∘ₗ starU D v)
    (fun m ↦ starU_f_starU_e_comm (hvt := hvt) hij m)
    (fun m ↦ starU_f_starU_f_comm i j m) (starU D v u)
  simp only [LinearMap.comp_apply, starU_starU] at h
  have h2 := congrArg (starU D v) h
  rw [starU_starU] at h2
  rw [kEs_apply, kEs_apply]
  exact h2.symm

lemma kFs_e_comm {i j : I} (hij : i ≠ j) (u : Um D v) :
    kFs hvt i ((bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e u) =
      (bos (D := D) (pow_ne_one_of_transcendental' hvt) j).e (kFs hvt i u) := by
  set B := bos (D := D) (pow_ne_one_of_transcendental' hvt)
  have h := BosonModule.map_fTilde (V := B i) (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) (B i)
    (starU D v ∘ₗ (B j).e ∘ₗ starU D v)
    (fun m ↦ starU_e_starU_comm (hvt := hvt) i j m)
    (fun m ↦ starU_e_starU_f_comm (hvt := hvt) hij m) (starU D v u)
  simp only [LinearMap.comp_apply, starU_starU] at h
  have h2 := congrArg (starU D v) h
  rw [starU_starU] at h2
  rw [kFs_apply, kFs_apply]
  exact h2.symm

lemma kFs_f_comm {i j : I} (hij : i ≠ j) (u : Um D v) :
    kFs hvt i (NegativePart.f D v j u) = NegativePart.f D v j (kFs hvt i u) := by
  set B := bos (D := D) (pow_ne_one_of_transcendental' hvt)
  have h := BosonModule.map_fTilde (V := B i) (NegativePart.pow_d_ne_zero (NeZero.ne v) i)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) i) (B i)
    (starU D v ∘ₗ NegativePart.f D v j ∘ₗ starU D v)
    (fun m ↦ starU_f_starU_e_comm (hvt := hvt) hij m)
    (fun m ↦ starU_f_starU_f_comm i j m) (starU D v u)
  simp only [LinearMap.comp_apply, starU_starU] at h
  have h2 := congrArg (starU D v) h
  rw [starU_starU] at h2
  rw [kFs_apply, kFs_apply]
  exact h2.symm

/-- **[Kas93a] Cor. 2.2.2** (`j ≠ i`): `ẽⱼ ẽᵢ* = ẽᵢ* ẽⱼ`. -/
theorem kE_kEs {i j : I} (hij : i ≠ j) (u : Um D v) :
    kE hvt j (kEs hvt i u) = kEs hvt i (kE hvt j u) :=
  (BosonModule.map_eTilde (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) j)
    (NegativePart.pow_d_ne_zero (NeZero.ne v) j)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) j) _ (kEs hvt i)
    (kEs_e_comm hij) (kEs_f_comm hij) u).symm

/-- **[Kas93a] Cor. 2.2.2** (`j ≠ i`): `f̃ⱼ ẽᵢ* = ẽᵢ* f̃ⱼ`. -/
theorem kF_kEs {i j : I} (hij : i ≠ j) (u : Um D v) :
    kF hvt j (kEs hvt i u) = kEs hvt i (kF hvt j u) :=
  (BosonModule.map_fTilde (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) j)
    (NegativePart.pow_d_ne_zero (NeZero.ne v) j)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) j) _ (kEs hvt i)
    (kEs_e_comm hij) (kEs_f_comm hij) u).symm

/-- **[Kas93a] Cor. 2.2.2** (`j ≠ i`): `ẽⱼ f̃ᵢ* = f̃ᵢ* ẽⱼ`. -/
theorem kE_kFs {i j : I} (hij : i ≠ j) (u : Um D v) :
    kE hvt j (kFs hvt i u) = kFs hvt i (kE hvt j u) :=
  (BosonModule.map_eTilde (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) j)
    (NegativePart.pow_d_ne_zero (NeZero.ne v) j)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) j) _ (kFs hvt i)
    (kFs_e_comm hij) (kFs_f_comm hij) u).symm

/-- **[Kas93a] Cor. 2.2.2** (`j ≠ i`): `f̃ⱼ f̃ᵢ* = f̃ᵢ* f̃ⱼ`. -/
theorem kF_kFs {i j : I} (hij : i ≠ j) (u : Um D v) :
    kF hvt j (kFs hvt i u) = kFs hvt i (kF hvt j u) :=
  (BosonModule.map_fTilde (V := bos (D := D) (pow_ne_one_of_transcendental' hvt) j)
    (NegativePart.pow_d_ne_zero (NeZero.ne v) j)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) j) _ (kFs hvt i)
    (kFs_e_comm hij) (kFs_f_comm hij) u).symm

/-- For `j ≠ i`, `ẽⱼ` preserves `ker e''ᵢ`. -/
theorem e_starU_kE_eq_zero {i j : I} (hij : i ≠ j) {P : Um D v}
    (hP : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0) :
    (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v (kE hvt j P)) = 0 := by
  set B := bos (D := D) (pow_ne_one_of_transcendental' hvt)
  have h := BosonModule.map_eTilde (V := B j) (NegativePart.pow_d_ne_zero (NeZero.ne v) j)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) j) (B j)
    (starU D v ∘ₗ (B i).e ∘ₗ starU D v)
    (fun m ↦ starU_e_starU_comm (hvt := hvt) j i m)
    (fun m ↦ starU_e_starU_f_comm (hvt := hvt) (Ne.symm hij) m) P
  simp only [LinearMap.comp_apply, hP, map_zero] at h
  have h2 := congrArg (starU D v) h
  rw [starU_starU, map_zero] at h2
  exact h2

/-- For `j ≠ i`, `f̃ⱼ` preserves `ker e''ᵢ`. -/
theorem e_starU_kF_eq_zero {i j : I} (hij : i ≠ j) {P : Um D v}
    (hP : (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v P) = 0) :
    (bos (D := D) (pow_ne_one_of_transcendental' hvt) i).e (starU D v (kF hvt j P)) = 0 := by
  set B := bos (D := D) (pow_ne_one_of_transcendental' hvt)
  have h := BosonModule.map_fTilde (V := B j) (NegativePart.pow_d_ne_zero (NeZero.ne v) j)
    (NegativePart.pow_d_ne_one (pow_ne_one_of_transcendental' hvt) j) (B j)
    (starU D v ∘ₗ (B i).e ∘ₗ starU D v)
    (fun m ↦ starU_e_starU_comm (hvt := hvt) j i m)
    (fun m ↦ starU_e_starU_f_comm (hvt := hvt) (Ne.symm hij) m) P
  simp only [LinearMap.comp_apply, hP, map_zero] at h
  have h2 := congrArg (starU D v) h
  rw [starU_starU, map_zero] at h2
  exact h2

end GrandLoop

end LieLean.QuantumGroup
