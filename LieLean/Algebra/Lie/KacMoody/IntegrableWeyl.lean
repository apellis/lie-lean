/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.Sl2
import LieLean.Algebra.Lie.KacMoody.Integrable
import LieLean.Algebra.Lie.Sl2
import LieLean.LinearAlgebra.Matrix.Cartan.WeylGroup

/-!
# Weights of integrable modules are invariant under the Weyl group

Let `A` be a generalized Cartan matrix, `K` a field of characteristic zero and `V` an integrable
module over the Kac–Moody algebra `𝔤(A)`. We show that `dim V_λ = dim V_{w λ}` for every weight
`λ ∈ 𝔥*` and every element `w` of the Weyl group `W` ([Kac] Prop. 3.7 (a)); in particular
the set of weights of `V` is `W`-invariant, and so are the root multiplicities of `𝔤(A)`.
We also show that the weights of an integrable module are integral: `⟨λ, αᵢ^∨⟩ ∈ ℤ`
([Kac] Prop. 3.6).

## Proof

We reconstructed the following argument, which avoids decomposing `V` into finite-dimensional
irreducible `𝔰𝔩₂`-modules (as in [Kac] §3.6–3.7). Let `(h, e, f)` be an `𝔰𝔩₂`-triple acting on a
module `M` over a field of characteristic zero.

1. If `h v = c v`, then `e fᵐ⁺¹ v = fᵐ⁺¹ e v + (m + 1)(c - m) fᵐ v`
   (`IsSl2Triple.lie_e_pow_succ_toEnd_f_of_lie_h`, a special case of
   `IsSl2Triple.lie_e_pow_succ_toEnd_f` in `LieLean/Algebra/Lie/Sl2.lean`). Hence for a primitive
   vector `v` (`e v = 0`, `h v = c v`) we get `eᵐ fᵐ v = ∏_{j < m} (j + 1)(c - j) v`
   (`IsSl2Triple.pow_toEnd_e_pow_toEnd_f`).
2. Suppose `e` acts locally nilpotently. If `h v = n v` with `n ∈ ℕ` and `fⁿ v = 0`, then `v = 0`
   (`IsSl2Triple.eq_zero_of_pow_toEnd_f_eq_zero`). Indeed, argue by induction on `k` with
   `eᵏ v = 0`: the vector `w = e v` satisfies `h w = (n + 2) w`, `eᵏ⁻¹ w = 0` and, by step 1 with
   `m = n + 1`, `fⁿ⁺² w = 0`; so `w = 0` by induction. Then `v` is primitive and
   `0 = eⁿ fⁿ v = (n!)² v`.
3. If `e` and `f` act locally nilpotently and `h v = c v` with `v ≠ 0`, then `c ∈ ℤ`
   (`IsSl2Triple.exists_int_of_lie_h_eq_smul`): if `e v ≠ 0` replace `v` by `e v` (eigenvalue
   `c + 2`) and use induction; otherwise `v` is primitive, and `fᵐ v = 0` for some `m` gives
   `∏_{j < m} (j + 1)(c - j) = 0` by step 1, so `c = j` for some `j ∈ ℕ`.

Now let `V` be an integrable `𝔤(A)`-module, `λ ∈ 𝔥*` and `i ∈ ι`, and apply this to the triple
`(αᵢ^∨, eᵢ, fᵢ)`. If `V_λ ≠ 0` then `c = ⟨λ, αᵢ^∨⟩ ∈ ℤ` by step 3. If `c = n ≥ 0`, then
`fᵢⁿ : V_λ → V_{λ - n αᵢ} = V_{rᵢ λ}` is injective by step 2; if `c = -n ≤ 0`, then
`eᵢⁿ : V_λ → V_{λ + n αᵢ} = V_{rᵢ λ}` is injective by step 2 for the triple `(-αᵢ^∨, fᵢ, eᵢ)`.
Hence `dim V_λ ≤ dim V_{rᵢ λ}`, and equality follows since `rᵢ` is an involution. We work with
`Module.rank`, so weight spaces of infinite dimension are allowed.

## Main results

* `IsSl2Triple.eq_zero_of_pow_toEnd_f_eq_zero`, `IsSl2Triple.exists_int_of_lie_h_eq_smul`: the
  `𝔰𝔩₂` facts above.
* `Matrix.Realization.KacMoodyAlgebra.isSl2Triple`: `(αᵢ^∨, eᵢ, fᵢ)` is an `𝔰𝔩₂`-triple.
* `Matrix.Realization.KacMoodyAlgebra.exists_int_of_weightSpace_ne_bot`: weights of integrable
  modules are integral ([Kac] Prop. 3.6).
* `Matrix.Realization.KacMoodyAlgebra.rank_weightSpace_weylGroup`: `dim V_{w λ} = dim V_λ`
  ([Kac] Prop. 3.7 (a)).
* `Matrix.Realization.KacMoodyAlgebra.weightSpace_weylGroup_eq_bot_iff`: the set of weights is
  `W`-invariant.
* `Matrix.Realization.KacMoodyAlgebra.rank_rootSpace_weylGroup`: root multiplicities are
  `W`-invariant ([Kac] Prop. 3.7 (b)).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §3.3, §3.6–3.7.
-/

open Module LieModule LieAlgebra

noncomputable section

/-! ### `𝔰𝔩₂`-triples acting with `e` locally nilpotent -/

namespace IsSl2Triple

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] {h e f : L} (t : IsSl2Triple h e f)
include t

lemma lie_h_lie_f {c : K} {v : M} (hv : ⁅h, v⁆ = c • v) : ⁅h, ⁅f, v⁆⁆ = (c - 2) • ⁅f, v⁆ := by
  rw [leibniz_lie, t.lie_lie_smul_f K, hv, neg_lie, smul_lie, lie_smul, sub_smul]
  abel

lemma lie_h_lie_e {c : K} {v : M} (hv : ⁅h, v⁆ = c • v) : ⁅h, ⁅e, v⁆⁆ = (c + 2) • ⁅e, v⁆ := by
  rw [leibniz_lie, t.lie_h_e_smul K, hv, smul_lie, lie_smul, add_smul]
  abel

/-- If `h v = c v`, then `e fᵐ⁺¹ v = fᵐ⁺¹ e v + (m + 1)(c - m) fᵐ v`. -/
lemma lie_e_pow_succ_toEnd_f_of_lie_h (m : ℕ) {c : K} {v : M} (hv : ⁅h, v⁆ = c • v) :
    ⁅e, (toEnd K L M f ^ (m + 1)) v⁆ =
      (toEnd K L M f ^ (m + 1)) ⁅e, v⁆ + ((m + 1 : K) * (c - m)) • (toEnd K L M f ^ m) v := by
  rw [t.lie_e_pow_succ_toEnd_f, hv, ← sub_smul, map_smul, smul_smul]

/-- For a primitive vector `v` (`e v = 0`, `h v = c v`), `eᵐ fᵐ v = ∏_{j < m} (j + 1)(c - j) v`. -/
lemma pow_toEnd_e_pow_toEnd_f (m : ℕ) {c : K} {v : M} (hv : ⁅h, v⁆ = c • v) (he : ⁅e, v⁆ = 0) :
    (toEnd K L M e ^ m) ((toEnd K L M f ^ m) v) =
      (∏ j ∈ Finset.range m, ((j + 1 : K) * (c - j))) • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, toEnd_apply_apply, t.lie_e_pow_succ_toEnd_f_of_lie_h m hv,
      he, map_zero, zero_add, map_smul, ih, smul_smul, Finset.prod_range_succ, mul_comm]

variable [CharZero K]

/-- If `e` acts locally nilpotently (here: `eᵏ v = 0`), `h v = n v` with `n ∈ ℕ` and `fⁿ v = 0`,
then `v = 0`. -/
theorem eq_zero_of_pow_toEnd_f_eq_zero {k n : ℕ} {v : M} (hk : (toEnd K L M e ^ k) v = 0)
    (hv : ⁅h, v⁆ = (n : K) • v) (hf : (toEnd K L M f ^ n) v = 0) : v = 0 := by
  induction k generalizing n v with
  | zero => simpa using hk
  | succ k ih =>
    -- first `e v = 0`
    have hev : ⁅e, v⁆ = 0 := by
      refine ih (n := n + 2) ?_ ?_ ?_
      · rwa [pow_succ, Module.End.mul_apply, toEnd_apply_apply] at hk
      · rw [t.lie_h_lie_e hv]; push_cast; ring_nf
      · have h1 : (toEnd K L M f ^ (n + 1)) v = 0 := by
          rw [pow_succ', Module.End.mul_apply, hf, map_zero]
        have h2 : (toEnd K L M f ^ (n + 2)) v = 0 := by
          rw [pow_succ', Module.End.mul_apply, h1, map_zero]
        have := t.lie_e_pow_succ_toEnd_f_of_lie_h (n + 1) hv
        rwa [h2, h1, lie_zero, smul_zero, add_zero, eq_comm] at this
    -- then `v` is primitive and `0 = eⁿ fⁿ v = (n!)² v`
    have := t.pow_toEnd_e_pow_toEnd_f n hv hev
    rw [hf, map_zero, eq_comm, smul_eq_zero] at this
    refine this.resolve_left (Finset.prod_ne_zero_iff.mpr fun j hj ↦ mul_ne_zero ?_ ?_)
    · exact_mod_cast Nat.succ_ne_zero j
    · rw [sub_ne_zero, Ne, Nat.cast_inj]
      exact (Finset.mem_range.mp hj).ne'

/-- If `e` and `f` act locally nilpotently on `v` and its images, the eigenvalues of `h` are
integers: if `h v = c v` with `v ≠ 0`, `eᵏ v = 0`, and `f` is locally nilpotent, then `c ∈ ℤ`. -/
theorem exists_int_of_lie_h_eq_smul (hf : ∀ v : M, ∃ m, (toEnd K L M f ^ m) v = 0) {k : ℕ}
    {c : K} {v : M} (hk : (toEnd K L M e ^ k) v = 0) (hv : ⁅h, v⁆ = c • v) (hv0 : v ≠ 0) :
    ∃ z : ℤ, c = z := by
  induction k generalizing c v with
  | zero => exact absurd (by simpa using hk) hv0
  | succ k ih =>
    by_cases hev : ⁅e, v⁆ = 0
    · obtain ⟨m, hm⟩ := hf v
      have := t.pow_toEnd_e_pow_toEnd_f m hv hev
      rw [hm, map_zero, eq_comm, smul_eq_zero, Finset.prod_eq_zero_iff] at this
      obtain ⟨j, -, hj⟩ := this.resolve_right hv0
      rcases mul_eq_zero.mp hj with hj | hj
      · exact absurd hj (by exact_mod_cast Nat.succ_ne_zero j)
      · exact ⟨j, by rw [sub_eq_zero] at hj; exact_mod_cast hj⟩
    · obtain ⟨z, hz⟩ := ih (by rwa [pow_succ, Module.End.mul_apply, toEnd_apply_apply] at hk)
        (t.lie_h_lie_e hv) hev
      exact ⟨z - 2, by push_cast; rw [← hz]; ring⟩

end IsSl2Triple

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

namespace KacMoodyAlgebra

variable [CharZero K] (hA : A.IsGeneralizedCartan)
include hA

/-- `(αᵢ^∨, eᵢ, fᵢ)` is an `𝔰𝔩₂`-triple in `𝔤(A)` ([Kac] §3.3). -/
theorem isSl2Triple (i : ι) : IsSl2Triple (h P (P.coroot i)) (e P i) (f P i) where
  h_ne_zero := by
    rw [Ne, ← map_zero (h P), (h_injective P).eq_iff]
    exact P.linearIndependent_coroot.ne_zero i
  lie_e_f := lie_e_f_self P i
  lie_h_e_nsmul := by rw [lie_h_e, P.root_coroot_self hA, two_smul, two_smul]
  lie_h_f_nsmul := by rw [lie_h_f, P.root_coroot_self hA, two_smul, two_smul]

section Module

variable {P} {V : Type*} [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

/-- The weights of an integrable module are integral: if `V_λ ≠ 0` then `⟨λ, αᵢ^∨⟩ ∈ ℤ` for all
`i` ([Kac] Prop. 3.6). -/
theorem exists_int_of_weightSpace_ne_bot (hV : IsIntegrable P V) {μ : Dual K H}
    (hμ : weightSpace P V μ ≠ ⊥) (i : ι) : ∃ z : ℤ, μ (P.coroot i) = z := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  obtain ⟨k, hk⟩ := hV.exists_pow_e_eq_zero i v
  exact (isSl2Triple P hA i).exists_int_of_lie_h_eq_smul (hV.exists_pow_f_eq_zero i) hk (hv _)
    hv0

/-- For an integrable module, `dim V_λ ≤ dim V_{rᵢ λ}`: the map `fᵢⁿ` (if `n = ⟨λ, αᵢ^∨⟩ ≥ 0`) or
`eᵢ⁻ⁿ` (if `n ≤ 0`) embeds `V_λ` into `V_{rᵢ λ}`. -/
theorem rank_weightSpace_le_reflection (hV : IsIntegrable P V) (i : ι) (μ : Dual K H) :
    Module.rank K (weightSpace P V μ) ≤
      Module.rank K (weightSpace P V (P.reflection hA i μ)) := by
  by_cases hμ : weightSpace P V μ = ⊥
  · rw [hμ, rank_bot]; exact zero_le
  obtain ⟨z, hz⟩ := exists_int_of_weightSpace_ne_bot hA hV hμ i
  have t := isSl2Triple P hA i
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · -- `⟨λ, αᵢ^∨⟩ = n ≥ 0`: `fᵢⁿ : V_λ → V_{λ - n αᵢ}` is injective
    have hr : P.reflection hA i μ = μ - n • P.root i := by
      rw [reflection_apply, hz, Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    let φ : weightSpace P V μ →ₗ[K] weightSpace P V (P.reflection hA i μ) :=
      (toEnd K _ V (f P i) ^ n).restrict fun v hv ↦ hr ▸ toEnd_f_pow_mem_weightSpace i hv n
    refine LinearMap.rank_le_of_injective φ (LinearMap.ker_eq_bot.mp ?_)
    refine LinearMap.ker_eq_bot'.mpr fun v hv ↦ Subtype.ext ?_
    obtain ⟨k, hk⟩ := hV.exists_pow_e_eq_zero i v
    refine t.eq_zero_of_pow_toEnd_f_eq_zero hk ?_ (congr_arg Subtype.val hv)
    rw [v.2 (P.coroot i), hz, Int.cast_natCast]
  · -- `⟨λ, αᵢ^∨⟩ = -n ≤ 0`: `eᵢⁿ : V_λ → V_{λ + n αᵢ}` is injective
    have hr : P.reflection hA i μ = μ + n • P.root i := by
      rw [reflection_apply, hz, Int.cast_neg, Int.cast_natCast, ← Nat.cast_smul_eq_nsmul K]
      module
    let φ : weightSpace P V μ →ₗ[K] weightSpace P V (P.reflection hA i μ) :=
      (toEnd K _ V (e P i) ^ n).restrict fun v hv ↦ hr ▸ toEnd_e_pow_mem_weightSpace i hv n
    refine LinearMap.rank_le_of_injective φ (LinearMap.ker_eq_bot.mp ?_)
    refine LinearMap.ker_eq_bot'.mpr fun v hv ↦ Subtype.ext ?_
    obtain ⟨k, hk⟩ := hV.exists_pow_f_eq_zero i v
    refine t.symm.eq_zero_of_pow_toEnd_f_eq_zero hk ?_ (congr_arg Subtype.val hv)
    rw [neg_lie, v.2 (P.coroot i), hz, Int.cast_neg, Int.cast_natCast, neg_smul, neg_neg]

/-- For an integrable module, `dim V_{rᵢ λ} = dim V_λ` ([Kac] Prop. 3.7 (a)). -/
theorem rank_weightSpace_reflection (hV : IsIntegrable P V) (i : ι) (μ : Dual K H) :
    Module.rank K (weightSpace P V (P.reflection hA i μ)) = Module.rank K (weightSpace P V μ) := by
  refine le_antisymm ?_ (rank_weightSpace_le_reflection hA hV i μ)
  have := rank_weightSpace_le_reflection hA hV i (P.reflection hA i μ)
  rwa [reflection_reflection] at this

/-- For an integrable module `V`, the weight multiplicities are `W`-invariant:
`dim V_{w λ} = dim V_λ` for all `w ∈ W` ([Kac] Prop. 3.7 (a)). -/
theorem rank_weightSpace_weylGroup (hV : IsIntegrable P V) {w : Dual K H ≃ₗ[K] Dual K H}
    (hw : w ∈ P.weylGroup hA) (μ : Dual K H) :
    Module.rank K (weightSpace P V (w μ)) = Module.rank K (weightSpace P V μ) := by
  refine P.weylGroup_induction hA
    (p := fun w ↦ ∀ μ, Module.rank K (weightSpace P V (w μ)) = Module.rank K (weightSpace P V μ))
    (fun μ ↦ rfl) (fun i w ih μ ↦ ?_) hw μ
  rw [LinearEquiv.mul_apply, rank_weightSpace_reflection hA hV, ih]

/-- For an integrable module `V`, the weight spaces `V_λ` and `V_{w λ}` (`w ∈ W`) are isomorphic
([Kac] Prop. 3.7 (a)). -/
theorem nonempty_weightSpace_weylGroup_equiv (hV : IsIntegrable P V)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA) (μ : Dual K H) :
    Nonempty (weightSpace P V (w μ) ≃ₗ[K] weightSpace P V μ) :=
  Module.nonempty_linearEquiv_iff_rank_eq.mpr (rank_weightSpace_weylGroup hA hV hw μ)

/-- The set of weights of an integrable module is `W`-invariant ([Kac] Prop. 3.7 (a)). -/
theorem weightSpace_weylGroup_eq_bot_iff (hV : IsIntegrable P V)
    {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA) (μ : Dual K H) :
    weightSpace P V (w μ) = ⊥ ↔ weightSpace P V μ = ⊥ := by
  rw [← Submodule.rank_eq_zero, ← Submodule.rank_eq_zero, rank_weightSpace_weylGroup hA hV hw]

end Module

/-- The root multiplicities of `𝔤(A)` are `W`-invariant: `dim 𝔤_{w α} = dim 𝔤_α` for `w ∈ W`
([Kac] Prop. 3.7 (b)). -/
theorem rank_rootSpace_weylGroup {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (μ : Dual K H) : Module.rank K (rootSpace P (w μ)) = Module.rank K (rootSpace P μ) :=
  rank_weightSpace_weylGroup hA (isIntegrable_adjoint P hA) hw μ

end KacMoodyAlgebra

end Matrix.Realization
