/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Lattice

/-!
# Lengths of strings in a crystal base

Let `M` be an integrable `U_q(𝔰𝔩₂)`-module, `L ⊆ M` a Kashiwara-stable `A`-submodule and
`B ⊆ L / cL` a set of nonzero vectors with `ẽ B, f̃ B ⊆ B ∪ {0}` and `f̃ b = b' ↔ ẽ b' = b`
(the conditions of a crystal base at one colour, [HK] Def. 4.2.3). If `b ∈ B` is the class of a
vector of `Mⁿ`, then `b ≡ F^{(k)} η` with `η ∈ Mᵖ` primitive, `p = n + 2k`, `k ≤ p` and `[η] ∈ B`
([HK] Prop. 4.2.11 (3)); hence `ẽᵃ b = 0` exactly when `a > k` and `f̃ᵃ b = 0` exactly when
`k + a > p` (`IntegrableSl2.IsKashiwaraStable.exists_string_counts`). So
`ε(b) = max {a | ẽᵃ b ≠ 0} = k` and `φ(b) = max {a | f̃ᵃ b ≠ 0} = p - k = ε(b) + n`, as in
[HK] (4.9).

We also record that `ẽ` is locally nilpotent (`IntegrableSl2.exists_eTilde_pow_eq_zero`).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.2.
-/

open Finset Pointwise

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M} (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]

/-! ### Iterates on strings -/

include hq0 hq in
/-- `ẽᵃ F^{(j)} η = F^{(j-a)} η` for `η ∈ Mᵖ` primitive and `a ≤ j ≤ p`. -/
lemma eTilde_pow_dF {p : ℤ} {η : M} (hη : η ∈ V.prim p) {a j : ℕ} (haj : a ≤ j)
    (hjp : (j : ℤ) ≤ p) : (V.eTilde hq0 hq ^ a) (V.dF j η) = V.dF (j - a) η := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, ih (by omega),
      show j - a = (j - (a + 1)) + 1 by omega,
      eTilde_dF_succ hq0 hq hη.2 hη.1 (by omega)]

include hq0 hq in
/-- `ẽᵃ F^{(j)} η = 0` for `η` primitive and `a > j`. -/
lemma eTilde_pow_dF_eq_zero {p : ℤ} {η : M} (hη : η ∈ V.prim p) {a j : ℕ} (haj : j < a) :
    (V.eTilde hq0 hq ^ a) (V.dF j η) = 0 := by
  by_cases hjp : (j : ℤ) ≤ p
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt haj
    rw [show j + b + 1 = b + (j + 1) by omega, pow_add, Module.End.mul_apply, pow_succ',
      Module.End.mul_apply, eTilde_pow_dF hq0 hq hη le_rfl hjp, Nat.sub_self, dF_zero,
      eTilde_of_primitive hq0 hq hη.2 hη.1, map_zero]
  · rw [dF_eq_zero_of_primitive hq0 hq hη.1 hη.2 (by omega), map_zero]

include hq0 hq in
/-- `f̃ᵃ F^{(j)} η = F^{(j+a)} η` for `η` primitive. -/
lemma fTilde_pow_dF {p : ℤ} {η : M} (hη : η ∈ V.prim p) (a j : ℕ) :
    (V.fTilde hq0 hq ^ a) (V.dF j η) = V.dF (j + a) η := by
  rw [← fTilde_pow_apply hq0 hq hη, ← Module.End.mul_apply, ← pow_add, add_comm,
    fTilde_pow_apply hq0 hq hη]

include hq0 hq in
lemma eTilde_pow_sum_eq_zero (N : ℕ) :
    ∀ (n : ℤ) (η : ℕ → M), (∀ j : ℕ, η j ∈ V.prim (n + 2 * j)) →
      (∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) →
      (V.eTilde hq0 hq ^ N) (∑ j ∈ range N, V.dF j (η j)) = 0 := by
  induction N with
  | zero => intro _ _ _ _; simp
  | succ N ih =>
    intro n η h1 h2
    rw [pow_succ, Module.End.mul_apply, eTilde_sum hq0 hq h1 h2]
    exact ih (n + 2) _ (prim_shift h1) (norm_shift h2)

include hq0 hq in
/-- `ẽ` is locally nilpotent. -/
theorem exists_eTilde_pow_eq_zero {n : ℤ} {m : M} (hm : m ∈ V.wt n) :
    ∃ N : ℕ, (V.eTilde hq0 hq ^ N) m = 0 := by
  obtain ⟨N, η, h1, h2, -, rfl⟩ := exists_sum_dF hq0 hq hm
  exact ⟨N, eTilde_pow_sum_eq_zero hq0 hq N n η h1 h2⟩

/-! ### Iterates on `L / c L` -/

variable {L : Submodule A M}

omit [Algebra A k] [IsScalarTower A k M] in
lemma pow_apply_mem {T : Module.End k M} (hT : ∀ m ∈ L, T m ∈ L) (a : ℕ) :
    ∀ m ∈ L, (T ^ a) m ∈ L := by
  intro m hm
  induction a with
  | zero => simpa using hm
  | succ a ih => rw [pow_succ', Module.End.mul_apply]; exact hT _ ih

lemma eTildeQ_pow_mk (hL : ∀ m ∈ L, V.eTilde hq0 hq m ∈ L) (c : A) (a : ℕ) (x : L) :
    (V.eTildeQ hq0 hq hL c ^ a) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(V.eTilde hq0 hq ^ a) x, pow_apply_mem hL a x x.2⟩ := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, ih, eTildeQ_mk]
    congr 2
    rw [pow_succ', Module.End.mul_apply]

lemma fTildeQ_pow_mk (hL : ∀ m ∈ L, V.fTilde hq0 hq m ∈ L) (c : A) (a : ℕ) (x : L) :
    (V.fTildeQ hq0 hq hL c ^ a) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(V.fTilde hq0 hq ^ a) x, pow_apply_mem hL a x x.2⟩ := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, ih, fTildeQ_mk]
    congr 2
    rw [pow_succ', Module.End.mul_apply]

variable {hq0 hq} in
/-- The lengths of the strings through an element of a crystal base at one colour
([HK] Prop. 4.2.11 (3), (4.9)): if `b ∈ B` is the class of `x ∈ L ∩ Mⁿ`, there are `k ≤ p` with
`p = n + 2k` such that `ẽᵃ b = 0 ↔ a > k` and `f̃ᵃ b = 0 ↔ k + a > p`. -/
theorem IsKashiwaraStable.exists_string_counts (hL : V.IsKashiwaraStable hq0 hq L) (c : A)
    (B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))) (hB0 : 0 ∉ B)
    (hBe : ∀ b ∈ B, V.eTildeQ hq0 hq hL.eTilde_mem c b ∈ B ∨
      V.eTildeQ hq0 hq hL.eTilde_mem c b = 0)
    (hBef : ∀ b ∈ B, ∀ b' ∈ B, V.fTildeQ hq0 hq hL.fTilde_mem c b = b' ↔
      V.eTildeQ hq0 hq hL.eTilde_mem c b' = b)
    {n : ℤ} (x : L) (hx : (x : M) ∈ V.wt n) (hxB : Submodule.Quotient.mk x ∈ B) :
    ∃ k p : ℕ, (p : ℤ) = n + 2 * k ∧ k ≤ p ∧
      (∀ a, (V.eTildeQ hq0 hq hL.eTilde_mem c ^ a) (Submodule.Quotient.mk x) = 0 ↔ k < a) ∧
      (∀ a, (V.fTildeQ hq0 hq hL.fTilde_mem c ^ a) (Submodule.Quotient.mk x) = 0 ↔
        p < k + a) := by
  obtain ⟨N, η, h1, h2, -, hxη⟩ := exists_sum_dF hq0 hq hx
  have hu : ∑ j ∈ range N, V.dF j (η j) ∈ L := hxη ▸ x.2
  have hxB' : Submodule.Quotient.mk ⟨_, hu⟩ ∈ B := by
    convert hxB using 2; exact Subtype.ext hxη.symm
  obtain ⟨k, -, hkL, hkB, -, hmod⟩ := hL.exists_of_mk_mem c B hB0 hBe hBef N n η h1 h2 hu hxB'
  rw [← hxη] at hmod
  have hη0 : η k ≠ 0 := by
    rintro h
    apply hB0
    have : (⟨η k, hkL⟩ : L) = 0 := Subtype.ext h
    rw [this, Submodule.Quotient.mk_zero] at hkB
    exact hkB
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = n + 2 * k :=
    ⟨_, Int.toNat_of_nonneg (by have := h2 k hη0; omega)⟩
  have hηp : η k ∈ V.prim p := hp ▸ h1 k
  have hkp : k ≤ p := by have := h2 k hη0; omega
  -- `[F^{(j)} η] ≠ 0` for `j ≤ p`
  have hne : ∀ j ≤ p, V.dF j (η k) ∉ c • L := by
    intro j hj h
    have := LinearMap.map_mem_smul_of_mem (f := V.eTilde hq0 hq ^ j) c
      (pow_apply_mem hL.eTilde_mem j) h
    rw [eTilde_pow_dF hq0 hq hηp le_rfl (by exact_mod_cast hj), Nat.sub_self, dF_zero] at this
    exact hB0 (by convert hkB using 1; exact ((mk_eq_zero_iff c _).2 this).symm)
  refine ⟨k, p, hp, hkp, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [eTildeQ_pow_mk, mk_eq_zero_iff]
    have hmod' := LinearMap.map_mem_smul_of_mem (f := V.eTilde hq0 hq ^ a) c
      (pow_apply_mem hL.eTilde_mem a) hmod
    rw [map_sub] at hmod'
    constructor
    · intro h
      by_contra hak
      have h' := sub_mem h hmod'
      rw [sub_sub_cancel, eTilde_pow_dF hq0 hq hηp (not_lt.1 hak)
        (by exact_mod_cast hkp)] at h'
      exact hne _ (by omega) h'
    · intro hak
      rwa [eTilde_pow_dF_eq_zero hq0 hq hηp hak, sub_zero] at hmod'
  · rw [fTildeQ_pow_mk, mk_eq_zero_iff]
    have hmod' := LinearMap.map_mem_smul_of_mem (f := V.fTilde hq0 hq ^ a) c
      (pow_apply_mem hL.fTilde_mem a) hmod
    rw [map_sub, fTilde_pow_dF hq0 hq hηp] at hmod'
    constructor
    · intro h
      by_contra hka
      have h' := sub_mem h hmod'
      rw [sub_sub_cancel] at h'
      exact hne _ (by omega) h'
    · intro hka
      rw [dF_eq_zero_of_primitive hq0 hq hηp.1 hηp.2 (by push_cast; omega), sub_zero] at hmod'
      exact hmod'

end IntegrableSl2

end LieLean.QuantumGroup
