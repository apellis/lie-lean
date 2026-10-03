/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.OfAssociative
import LieLean.Algebra.Lie.KacMoody.Basic

/-!
# Integrable modules over Kac–Moody algebras

Let `A` be a generalized Cartan matrix with realization `(𝔥, Π, Π^∨)` over a field `K`. A module
`V` over the Kac–Moody algebra `𝔤(A)` is *`𝔥`-diagonalizable* if it is the sum of its weight
spaces `V_λ = {v | h • v = ⟨λ, h⟩ v for all h ∈ 𝔥}`, and it is *integrable* if moreover all the
Chevalley generators `eᵢ`, `fᵢ` act locally nilpotently ([Kac] §3.6).

We show that the adjoint representation of `𝔤(A)` is integrable ([Kac] Lemma 3.5). The
proof follows [Kac] §3.4–3.5: the elements of a Lie algebra on which `ad x` acts locally
nilpotently form a Lie subalgebra (Mathlib's `LieSubalgebra.engel`), because of the Leibniz rule
`(ad x)ⁿ [y, z] = ∑ₖ (n choose k) [(ad x)ᵏ y, (ad x)ⁿ⁻ᵏ z]` ([Kac] §3.4); so it suffices
to check that `ad eᵢ` is nilpotent on the generators. This holds by the Serre relations for `eⱼ`
(`j ≠ i`), and because `(ad eᵢ)³ fᵢ = 0`, `(ad eᵢ)² h = 0`. The case of `fᵢ` follows by applying
the Chevalley involution.

We also record the module version of this argument ([Kac] Lemma 3.4 (b)): if `ad x` is
locally nilpotent on `L`, then the vectors of an `L`-module on which `x` acts locally nilpotently
form a Lie submodule.

## Main definitions

* `LieModule.locallyNilpotentSubmodule`: for `x` with `ad x` locally nilpotent, the Lie submodule
  of vectors on which `x` acts locally nilpotently.
* `Matrix.Realization.KacMoodyAlgebra.weightSpace`: the weight space `V_λ` of a `𝔤(A)`-module.
* `Matrix.Realization.KacMoodyAlgebra.IsHDiagonalizable`: `V = ∑_λ V_λ`.
* `Matrix.Realization.KacMoodyAlgebra.IsIntegrable`: integrable `𝔤(A)`-modules.

## Main results

* `LieModule.exists_toEnd_pow_eq_zero_of_lieSpan`: [Kac] Lemma 3.4 (b).
* `Matrix.Realization.KacMoodyAlgebra.engel_e_eq_top`, `engel_f_eq_top`: `ad eᵢ` and `ad fᵢ` are
  locally nilpotent on `𝔤(A)`.
* `Matrix.Realization.KacMoodyAlgebra.isIntegrable_adjoint`: the adjoint `𝔤(A)`-module is
  integrable ([Kac] Lemma 3.5).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.4–3.6.
-/

open Module LieModule LieAlgebra

noncomputable section

/-! ### Locally nilpotent actions -/

namespace LieModule

variable {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]

/-- If `ad x` is nilpotent on `y` and `x` is nilpotent on `m`, then `x` is nilpotent on `[y, m]`.
This is the key step of [Kac] Lemma 3.4 (b). -/
lemma exists_toEnd_pow_lie_eq_zero {x y : L} {m : M} (hy : ∃ n, (ad K L x ^ n) y = 0)
    (hm : ∃ n, (toEnd K L M x ^ n) m = 0) : ∃ n, (toEnd K L M x ^ n) ⁅y, m⁆ = 0 := by
  obtain ⟨a, ha⟩ := hy
  obtain ⟨b, hb⟩ := hm
  refine ⟨a + b, ?_⟩
  rw [toEnd_pow_lie]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  obtain (h | h) : a ≤ ij.1 ∨ b ≤ ij.2 := by rw [Finset.mem_antidiagonal] at hij; omega
  · rw [Module.End.pow_map_zero_of_le h ha, zero_lie, smul_zero]
  · rw [Module.End.pow_map_zero_of_le h hb, lie_zero, smul_zero]

variable (K L M) in
/-- For `x ∈ L` with `ad x` locally nilpotent on `L`, the vectors of `M` on which `x` acts locally
nilpotently form a Lie submodule. -/
def locallyNilpotentSubmodule (x : L) (hx : ∀ y : L, ∃ n, (ad K L x ^ n) y = 0) :
    LieSubmodule K L M where
  carrier := {m | ∃ n, (toEnd K L M x ^ n) m = 0}
  add_mem' := by
    rintro m m' ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [map_add, Module.End.pow_map_zero_of_le (Nat.le_add_right a b) ha,
      Module.End.pow_map_zero_of_le (Nat.le_add_left b a) hb, add_zero]
  zero_mem' := ⟨0, by simp⟩
  smul_mem' c m := by
    rintro ⟨a, ha⟩
    exact ⟨a, by rw [map_smul, ha, smul_zero]⟩
  lie_mem hm := exists_toEnd_pow_lie_eq_zero (hx _) hm

@[simp] lemma mem_locallyNilpotentSubmodule {x : L} (hx : ∀ y : L, ∃ n, (ad K L x ^ n) y = 0)
    {m : M} : m ∈ locallyNilpotentSubmodule K L M x hx ↔ ∃ n, (toEnd K L M x ^ n) m = 0 :=
  Iff.rfl

/-- Let `x ∈ L` be such that `ad x` is locally nilpotent on `L`. If an `L`-module `M` is generated
by a set `S` of vectors on which `x` acts locally nilpotently, then `x` acts locally nilpotently
on `M` ([Kac] Lemma 3.4 (b)). -/
theorem exists_toEnd_pow_eq_zero_of_lieSpan {x : L} (hx : ∀ y : L, ∃ n, (ad K L x ^ n) y = 0)
    {S : Set M} (hS : LieSubmodule.lieSpan K L S = ⊤)
    (hSx : ∀ m ∈ S, ∃ n, (toEnd K L M x ^ n) m = 0) (m : M) :
    ∃ n, (toEnd K L M x ^ n) m = 0 := by
  have : LieSubmodule.lieSpan K L S ≤ locallyNilpotentSubmodule K L M x hx :=
    LieSubmodule.lieSpan_le.mpr hSx
  rw [hS] at this
  exact this (LieSubmodule.mem_top m)

end LieModule

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

namespace KacMoodyAlgebra

/-! ### Weight spaces and integrable modules -/

section Module

variable (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- The weight space `V_λ = {v ∈ V | h • v = ⟨λ, h⟩ v for all h ∈ 𝔥}` of a `𝔤(A)`-module `V`
([Kac] §3.6). For the adjoint module it is the root space `𝔤_λ`. -/
abbrev weightSpace (μ : Dual K H) : Submodule K V :=
  weightSpaceOfMap V (h P) μ

/-- A `𝔤(A)`-module is `𝔥`-diagonalizable if it is the sum of its weight spaces ([Kac] §3.6
); the sum is then direct by `LieModule.iSupIndep_weightSpaceOfMap`. -/
def IsHDiagonalizable : Prop :=
  ⨆ μ, weightSpace P V μ = ⊤

/-- A `𝔤(A)`-module `V` is integrable if it is `𝔥`-diagonalizable and all the Chevalley generators
`eᵢ`, `fᵢ` act locally nilpotently on `V` ([Kac] §3.6). -/
structure IsIntegrable : Prop where
  isHDiagonalizable : IsHDiagonalizable P V
  exists_pow_e_eq_zero : ∀ i (v : V), ∃ n : ℕ, (toEnd K P.KacMoodyAlgebra V (e P i) ^ n) v = 0
  exists_pow_f_eq_zero : ∀ i (v : V), ∃ n : ℕ, (toEnd K P.KacMoodyAlgebra V (f P i) ^ n) v = 0

variable {P V}

open Classical in
/-- An `𝔥`-diagonalizable module is the internal direct sum of its weight spaces. -/
theorem IsHDiagonalizable.isInternal_weightSpace (hV : IsHDiagonalizable P V) :
    DirectSum.IsInternal (weightSpace P V) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_weightSpaceOfMap (M := V) (h P)) hV

/-- `eᵢ V_λ ⊆ V_{λ + αᵢ}`. -/
lemma toEnd_e_mem_weightSpace (i : ι) {μ : Dual K H} {v : V} (hv : v ∈ weightSpace P V μ) :
    toEnd K P.KacMoodyAlgebra V (e P i) v ∈ weightSpace P V (μ + P.root i) := by
  rw [add_comm]
  exact lie_mem_weightSpaceOfMap (h P) (fun a ↦ lie_h_e P a i) hv

/-- `fᵢ V_λ ⊆ V_{λ - αᵢ}`. -/
lemma toEnd_f_mem_weightSpace (i : ι) {μ : Dual K H} {v : V} (hv : v ∈ weightSpace P V μ) :
    toEnd K P.KacMoodyAlgebra V (f P i) v ∈ weightSpace P V (μ - P.root i) := by
  rw [sub_eq_neg_add]
  refine lie_mem_weightSpaceOfMap (h P) (fun a ↦ ?_) hv
  rw [lie_h_f, LinearMap.neg_apply, neg_smul]

/-- `eᵢⁿ V_λ ⊆ V_{λ + n αᵢ}`. -/
lemma toEnd_e_pow_mem_weightSpace (i : ι) {μ : Dual K H} {v : V} (hv : v ∈ weightSpace P V μ)
    (n : ℕ) : (toEnd K P.KacMoodyAlgebra V (e P i) ^ n) v ∈ weightSpace P V (μ + n • P.root i) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, succ_nsmul, ← add_assoc]
    exact toEnd_e_mem_weightSpace i ih

/-- `fᵢⁿ V_λ ⊆ V_{λ - n αᵢ}`. -/
lemma toEnd_f_pow_mem_weightSpace (i : ι) {μ : Dual K H} {v : V} (hv : v ∈ weightSpace P V μ)
    (n : ℕ) : (toEnd K P.KacMoodyAlgebra V (f P i) ^ n) v ∈ weightSpace P V (μ - n • P.root i) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, succ_nsmul, ← sub_sub]
    exact toEnd_f_mem_weightSpace i ih

end Module

/-! ### The adjoint module is integrable -/

/-- Induction principle for `𝔤(A)`: it is generated as a Lie algebra by the `eᵢ`, `fᵢ` and `𝔥`. -/
@[elab_as_elim]
lemma induction_on {p : P.KacMoodyAlgebra → Prop} (y : P.KacMoodyAlgebra)
    (he : ∀ i, p (e P i)) (hf : ∀ i, p (f P i)) (hh : ∀ a, p (h P a)) (zero : p 0)
    (add : ∀ y z, p y → p z → p (y + z)) (smul : ∀ (a : K) y, p y → p (a • y))
    (lie : ∀ y z, p y → p z → p ⁅y, z⁆) : p y := by
  obtain ⟨x, rfl⟩ := π_surjective P y
  induction x using AuxLieAlgebra.induction_on with
  | he i => exact he i
  | hf i => exact hf i
  | hh a => exact hh a
  | zero => simpa using zero
  | add y z hy hz => rw [map_add]; exact add _ _ hy hz
  | smul a y hy => rw [map_smul]; exact smul a _ hy
  | lie y z hy hz => rw [LieHom.map_lie]; exact lie _ _ hy hz

lemma exists_ad_pow_add_eq_zero {x y z : P.KacMoodyAlgebra} (hy : ∃ n, (ad K _ x ^ n) y = 0)
    (hz : ∃ n, (ad K _ x ^ n) z = 0) : ∃ n, (ad K _ x ^ n) (y + z) = 0 := by
  obtain ⟨a, ha⟩ := hy
  obtain ⟨b, hb⟩ := hz
  refine ⟨a + b, ?_⟩
  rw [map_add, Module.End.pow_map_zero_of_le (Nat.le_add_right a b) ha,
    Module.End.pow_map_zero_of_le (Nat.le_add_left b a) hb, add_zero]

/-- The adjoint `𝔤(A)`-module is `𝔥`-diagonalizable: this is the root space decomposition. -/
theorem isHDiagonalizable_adjoint : IsHDiagonalizable P P.KacMoodyAlgebra :=
  eq_top_iff.mpr ((iSup_rootSpace_eq_top P).symm.le.trans
    (iSup₂_le fun μ _ ↦ le_iSup (weightSpace P P.KacMoodyAlgebra) μ))

variable [CharZero K] (hA : A.IsGeneralizedCartan)
include hA

/-- `ad eᵢ` is locally nilpotent on `𝔤(A)` ([Kac] Lemma 3.5). -/
theorem exists_ad_e_pow_eq_zero (i : ι) (y : P.KacMoodyAlgebra) :
    ∃ n, (ad K _ (e P i) ^ n) y = 0 := by
  induction y using induction_on with
  | he j =>
    by_cases hij : i = j
    · subst hij; exact ⟨1, by simp⟩
    · refine ⟨(-A i j).toNat + 1, ?_⟩
      rw [pow_succ, Module.End.mul_apply, ad_apply, serre_e P hA hij]
  | hf j =>
    by_cases hij : i = j
    · subst hij
      have h1 : ⁅e P i, h P (P.coroot i)⁆ = -((2 : K) • e P i) := by
        rw [← lie_skew, lie_h_e, P.root_coroot, hA.diag]
        norm_num
      refine ⟨3, ?_⟩
      simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, ad_apply, lie_e_f_self, h1,
        lie_neg, lie_smul, lie_self, smul_zero, neg_zero]
    · exact ⟨1, by simp [lie_e_f_of_ne P hij]⟩
  | hh a =>
    refine ⟨2, ?_⟩
    simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, ad_apply]
    rw [← lie_skew (e P i) (h P a), lie_h_e, lie_neg, lie_smul, lie_self, smul_zero, neg_zero]
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz => exact exists_ad_pow_add_eq_zero P hy hz
  | smul c y hy =>
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, by rw [map_smul, hn, smul_zero]⟩
  | lie y z hy hz => exact exists_toEnd_pow_lie_eq_zero hy hz

/-- `ad fᵢ` is locally nilpotent on `𝔤(A)` ([Kac] Lemma 3.5). -/
theorem exists_ad_f_pow_eq_zero (i : ι) (y : P.KacMoodyAlgebra) :
    ∃ n, (ad K _ (f P i) ^ n) y = 0 := by
  obtain ⟨n, hn⟩ := exists_ad_e_pow_eq_zero P hA i (chevalleyInvolution P y)
  refine ⟨n, ?_⟩
  have := congr_arg (chevalleyInvolution P) hn
  rw [LieHom.map_ad_pow, chevalleyInvolution_e, chevalleyInvolution_chevalleyInvolution,
    map_zero, ad_neg_pow_apply] at this
  exact (smul_eq_zero.mp this).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- The adjoint representation of `𝔤(A)` is integrable ([Kac] Lemma 3.5). -/
theorem isIntegrable_adjoint : IsIntegrable P P.KacMoodyAlgebra where
  isHDiagonalizable := isHDiagonalizable_adjoint P
  exists_pow_e_eq_zero := exists_ad_e_pow_eq_zero P hA
  exists_pow_f_eq_zero := exists_ad_f_pow_eq_zero P hA

end KacMoodyAlgebra

end Matrix.Realization
