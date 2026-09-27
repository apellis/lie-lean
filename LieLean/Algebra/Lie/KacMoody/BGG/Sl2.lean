/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Sl2
import LieLean.Algebra.Lie.LocallyNilpotent

/-!
# Injectivity of powers of `e` on negative weight spaces of `𝔰𝔩₂`-modules

Let `(h, e, f)` be an `𝔰𝔩₂`-triple in a Lie algebra `L` over a field `K` of characteristic zero,
and `M` an `L`-module on which `e` and `f` act locally nilpotently. If `x ∈ M` has `h`-weight `-m`,
`m ∈ ℕ`, and `eᵏ x = 0` with `k < m`, then `x = 0`. (In a finite-dimensional irreducible module
`L(n)`, `eᵏ` is injective on the weight space `-m` for `k ≤ m ≤ n`.) This is used in the proof that
Verma modules over Kac–Moody algebras are "projective in the `𝔰𝔩₂`-directions", which gives the
uniqueness of homomorphisms between Verma modules in the BGG resolution.

## Main results

* `IsSl2Triple.four_pow_smul_pow_f_pow_e`: `4ᵏ fᵏ eᵏ x = ∏_{j < k} (Ω - cⱼ (cⱼ + 2)) x` for `x` of
  weight `μ`, where `cⱼ = μ + 2j` and `Ω = h² + 2h + 4fe` is the Casimir operator.
* `IsSl2Triple.eq_zero_of_toEnd_e_pow_eq_zero_of_finiteDimensional`: the statement for
  finite-dimensional modules.
* `IsSl2Triple.eq_zero_of_toEnd_e_pow_eq_zero`: the statement for modules on which `e` and `f` act
  locally nilpotently.

## Proof

For `x` of weight `-m` with `eᵏ x = 0`, the identity above shows that `x` is killed by
`∏_{j < k} (Ω - cⱼ (cⱼ + 2))`, `cⱼ = 2j - m`. On a finite-dimensional module `x` is also killed by
a power of `∏_{n ≤ N} (Ω - n (n + 2))`. The factors with `n ≥ m` are coprime to the first product
(as `|cⱼ + 1| < m`), so `x` lies in the sum of the generalized eigenspaces of `Ω` for the
eigenvalues `n (n + 2)`, `n < m`; these consist of `f`-strings through primitive vectors of weight
`n` (`IsSl2Triple.mem_primitiveSpan`), whose weights are `≥ -n > -m`. Hence `x = 0`. The locally
nilpotent case reduces to this one by passing to the finite-dimensional subspace spanned by the
`fᵃ eᵇ x`. The argument was reconstructed by us.

## References

* [Hum] J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §7
  (representations of `𝔰𝔩₂`).
-/

open LieModule Module Polynomial

namespace IsSl2Triple

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] {h e f : L} (t : IsSl2Triple h e f)
include t

/-- The Casimir operator of the triple `(-h, f, e)` is that of `(h, e, f)`. -/
lemma casimir_symm : casimir K M (-h) f e = casimir K M h e f := by
  ext v
  simp only [casimir_apply, neg_lie, lie_neg, smul_neg, neg_neg, leibniz_lie e f v, t.lie_e_f]
  module

/-- The Casimir operator commutes with `f`. -/
lemma commute_casimir_f : Commute (casimir K M h e f) (toEnd K L M f) := by
  rw [← t.casimir_symm]
  exact t.symm.commute_casimir_e

omit t in
/-- `4 f e w = (Ω - c (c + 2)) w` for `w` of weight `c`. -/
lemma four_smul_f_e {c : K} {w : M} (hw : ⁅h, w⁆ = c • w) :
    (4 : K) • ⁅f, ⁅e, w⁆⁆ = casimir K M h e f w - (c * (c + 2)) • w := by
  rw [casimir_apply, hw, lie_smul, hw, smul_smul]
  module

/-- `4ᵏ fᵏ eᵏ x = ∏_{j < k} (Ω - cⱼ (cⱼ + 2)) x` for `x` of weight `μ`, where `cⱼ = μ + 2j` and `Ω`
is the Casimir operator. -/
theorem four_pow_smul_pow_f_pow_e {μ : K} {x : M} (hx : ⁅h, x⁆ = μ • x) (k : ℕ) :
    (4 : K) ^ k • (toEnd K L M f ^ k) ((toEnd K L M e ^ k) x) =
      aeval (casimir K M h e f)
        (∏ j ∈ Finset.range k, (X - C ((μ + 2 * j) * (μ + 2 * j + 2)))) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    set Ω := casimir K M h e f
    have hw : ⁅h, (toEnd K L M e ^ k) x⁆ = (μ + 2 * k) • (toEnd K L M e ^ k) x := by
      rw [← toEnd_apply_apply (R := K), ← Module.End.mul_apply, t.toEnd_h_mul_e_pow,
        LinearMap.add_apply, Module.End.mul_apply, toEnd_apply_apply, hx, map_smul,
        LinearMap.smul_apply, ← add_smul, add_comm]
    have hΩf : ∀ n (v : M), Ω ((toEnd K L M f ^ n) v) = (toEnd K L M f ^ n) (Ω v) := fun n v ↦ by
      rw [← Module.End.mul_apply, ((t.commute_casimir_f (M := M)).pow_right n).eq,
        Module.End.mul_apply]
    have e1 : (toEnd K L M f ^ (k + 1)) ((toEnd K L M e ^ (k + 1)) x) =
        (toEnd K L M f ^ k) ⁅f, ⁅e, (toEnd K L M e ^ k) x⁆⁆ := by
      rw [pow_succ, Module.End.mul_apply, pow_succ', Module.End.mul_apply, toEnd_apply_apply,
        toEnd_apply_apply]
    set y := (toEnd K L M e ^ k) x
    have e2 : aeval Ω (X - C ((μ + 2 * k) * (μ + 2 * k + 2))) ((toEnd K L M f ^ k) y) =
        (toEnd K L M f ^ k) (Ω y - ((μ + 2 * k) * (μ + 2 * k + 2)) • y) := by
      rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, hΩf,
        map_sub, map_smul]
    rw [Finset.prod_range_succ, mul_comm, map_mul, Module.End.mul_apply, ← ih, map_smul, e1,
      e2, ← four_smul_f_e (e := e) (f := f) hw, map_smul, smul_smul, ← pow_succ]

variable [CharZero K]

omit t in
/-- `n (n + 2) ≠ c (c + 2)` in `K` if `c = 2j - m` with `j < k < m ≤ n`. -/
lemma cast_mul_ne {n m j k : ℕ} (hj : j < k) (hkm : k < m) (hmn : m ≤ n) :
    (-(m : K) + 2 * j) * (-(m : K) + 2 * j + 2) - n * (n + 2) ≠ 0 := by
  have : ((-(m : ℤ) + 2 * j) * (-(m : ℤ) + 2 * j + 2) - n * (n + 2) : ℤ) ≠ 0 := by
    have h1 : (-(m : ℤ) + 2 * j + 1) - (n + 1) < 0 := by omega
    have h2 : 0 < (-(m : ℤ) + 2 * j + 1) + (n + 1) := by omega
    nlinarith
  exact_mod_cast this

/-- Every `f`-string through a primitive vector of weight `n ∈ ℕ` stops after `n + 1` steps if `f`
acts locally nilpotently. -/
lemma pow_f_succ_eq_zero {n : ℕ} {w : M} (hwe : ⁅e, w⁆ = 0) (hwh : ⁅h, w⁆ = (n : K) • w)
    (hf : ∃ N, (toEnd K L M f ^ N) w = 0) : (toEnd K L M f ^ (n + 1)) w = 0 := by
  by_contra h0
  have hp : t.HasPrimitiveVectorWith ((toEnd K L M f ^ (n + 1)) w) (-(n : K) - 2) := by
    refine ⟨h0, ?_, ?_⟩
    · rw [t.lie_h_pow_toEnd_f_of_eq hwh]
      congr 1
      push_cast
      ring
    · rw [t.lie_e_pow_succ_toEnd_f, hwe, map_zero, zero_add, hwh, sub_self, map_zero,
        smul_zero]
  obtain ⟨N, hN⟩ := hf
  obtain ⟨p, hp'⟩ := hp.exists_nat_of_exists_pow_eq_zero ⟨N, by
    rw [← Module.End.mul_apply, ← pow_add, add_comm, pow_add, Module.End.mul_apply, hN,
      map_zero]⟩
  have : ((p + n + 2 : ℕ) : K) = 0 := by push_cast; linear_combination -hp'
  exact absurd (Nat.cast_eq_zero.mp this) (by omega)

/-- **`eᵏ` is injective on the weight space `-m` for `k < m`** (finite-dimensional case). -/
theorem eq_zero_of_toEnd_e_pow_eq_zero_of_finiteDimensional [FiniteDimensional K M] {x : M}
    {m k : ℕ} (hx : ⁅h, x⁆ = -(m : K) • x) (hkm : k < m) (hk : (toEnd K L M e ^ k) x = 0) :
    x = 0 := by
  classical
  set Ω := casimir K M h e f
  obtain ⟨d, hd⟩ := t.isNilpotent_toEnd_e (K := K) (M := M)
  obtain ⟨N, hN'⟩ := t.isNilpotent_toEnd_f (K := K) (M := M)
  have hN : toEnd K L M f ^ (N + 1) = 0 := by rw [pow_succ, hN', zero_mul]
  -- `x` is killed by `P₁(Ω)`
  set c : ℕ → K := fun j ↦ -(m : K) + 2 * j
  set P₁ := ∏ j ∈ Finset.range k, (X - C (c j * (c j + 2)))
  have h₁ : aeval Ω P₁ x = 0 := by
    rw [← t.four_pow_smul_pow_f_pow_e hx k, hk, map_zero, smul_zero]
  -- `x` is killed by `Q(Ω)ᵈ`
  set g : ℕ → K[X] := fun n ↦ (X - C ((n : K) * (n + 2))) ^ d
  set s := Finset.range (N + 1)
  have h₂ : aeval Ω (∏ n ∈ s, g n) x = 0 := by
    have := t.aeval_casimir_pow_apply_eq_zero hN d (v := x) (by rw [hd, LinearMap.zero_apply])
    rwa [← map_pow, ← Finset.prod_pow] at this
  -- split off the factors with `n ≥ m`
  set A := ∏ n ∈ s.filter (· < m), g n
  set B := ∏ n ∈ s.filter (fun n ↦ ¬ n < m), g n
  have hAB : ∏ n ∈ s, g n = A * B := (Finset.prod_filter_mul_prod_filter_not s (· < m) g).symm
  have hcop : IsCoprime P₁ B := by
    refine IsCoprime.prod_right fun n hn ↦ IsCoprime.pow_right (IsCoprime.prod_left fun j hj ↦ ?_)
    rw [Finset.mem_filter, not_lt] at hn
    refine isCoprime_X_sub_C_of_isUnit_sub (Ne.isUnit ?_)
    exact cast_mul_ne (Finset.mem_range.mp hj) hkm hn.2
  have hAx : aeval Ω A x = 0 := by
    have hker := Polynomial.disjoint_ker_aeval_of_isCoprime Ω hcop
    refine Submodule.disjoint_def.mp hker _ ?_ ?_
    · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
        Module.End.mul_apply, h₁, map_zero]
    · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← map_mul, mul_comm, ← hAB, h₂]
  -- hence `x` lies in the sum of the eigenspaces of `h` for weights `> -m`
  set S := ⨆ (c : K) (_ : c ≠ -(m : K)), (toEnd K L M h).eigenspace c
  have hS : ∀ n < m, LinearMap.ker (aeval Ω (g n)) ≤ S := by
    intro n hn v hv
    have hvp := t.mem_primitiveSpan hN n d d (v := v) (by rw [hd, LinearMap.zero_apply]) hv
    refine (iSup_le fun j ↦ Submodule.map_le_iff_le_comap.mpr ?_ :
      primitiveSpan K M h e f (n : K) ≤ S) hvp
    rintro w ⟨hwe, hwh⟩
    replace hwe : ⁅e, w⁆ = 0 := hwe
    replace hwh : ⁅h, w⁆ = (n : K) • w := Module.End.mem_eigenspace_iff.mp hwh
    rw [Submodule.mem_comap]
    by_cases hj : j ≤ n
    · refine Submodule.mem_iSup_of_mem ((n : K) - 2 * j) (Submodule.mem_iSup_of_mem ?_ ?_)
      · intro heq
        have : ((m + n : ℕ) : K) = ((2 * j : ℕ) : K) := by push_cast; linear_combination heq
        have := Nat.cast_injective this
        omega
      · rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply]
        exact t.lie_h_pow_toEnd_f_of_eq hwh j
    · rw [show j = (j - (n + 1)) + (n + 1) by omega, pow_add, Module.End.mul_apply,
        t.pow_f_succ_eq_zero hwe hwh ⟨N + 1, by rw [hN, LinearMap.zero_apply]⟩, map_zero]
      exact zero_mem _
  have hxS : x ∈ S := by
    have hcopg : ∀ i ∈ s.filter (· < m), ∀ j ∈ s.filter (· < m), i ≠ j →
        IsCoprime (g i) (g j) := by
      intro i _ j _ hij
      refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub (Ne.isUnit fun hc ↦ hij ?_))
      have : ((i * (i + 2) : ℕ) : K) = ((j * (j + 2) : ℕ) : K) := by
        push_cast; linear_combination hc
      have h' := Nat.cast_injective this
      rcases lt_trichotomy i j with h | h | h
      · exact absurd h' (Nat.mul_lt_mul'' h (by omega)).ne
      · exact h
      · exact absurd h' (Nat.mul_lt_mul'' h (by omega)).ne'
    have := Module.End.ker_aeval_prod_le_iSup Ω (s.filter (· < m)) g hcopg
      (LinearMap.mem_ker.mpr hAx)
    have hle : (⨆ n ∈ s.filter (· < m), LinearMap.ker (aeval Ω (g n))) ≤ S :=
      iSup₂_le fun n hn ↦ hS n (Finset.mem_filter.mp hn).2
    exact hle this
  have hxm : x ∈ (toEnd K L M h).eigenspace (-(m : K)) := by
    rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply, hx]
  exact Submodule.disjoint_def.mp
    ((Module.End.eigenspaces_iSupIndep (toEnd K L M h)).disjoint_biSup
      (x := -(m : K)) (y := {c | c ≠ -(m : K)}) fun hc ↦ hc rfl) x hxm hxS

/-- **`eᵏ` is injective on the weight space `-m` for `k < m`**: let `e` and `f` act locally
nilpotently on `M`, and let `x ∈ M` have `h`-weight `-m`, `m ∈ ℕ`. If `eᵏ x = 0` with `k < m`, then
`x = 0`. -/
theorem eq_zero_of_toEnd_e_pow_eq_zero
    (he : ∀ v : M, ∃ n, (toEnd K L M e ^ n) v = 0) (hf : ∀ v : M, ∃ n, (toEnd K L M f ^ n) v = 0)
    {x : M} {m k : ℕ} (hx : ⁅h, x⁆ = -(m : K) • x) (hkm : k < m)
    (hk : (toEnd K L M e ^ k) x = 0) : x = 0 := by
  classical
  obtain ⟨B, hB⟩ := he x
  rcases Nat.eq_zero_or_pos B with rfl | hB0
  · simpa using hB
  choose A hA using fun b : ℕ ↦ hf ((toEnd K L M e ^ b) x)
  set A' := ∑ b ∈ Finset.range B, A b
  set E := toEnd K L M e
  set F := toEnd K L M f
  have hFA : ∀ b < B, ∀ a, A' ≤ a → (F ^ a) ((E ^ b) x) = 0 := by
    intro b hb a ha
    have : A b ≤ a := (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr hb)).trans ha
    rw [show a = (a - A b) + A b by omega, pow_add, Module.End.mul_apply, hA b, map_zero]
  have hEB : ∀ b, B ≤ b → (E ^ b) x = 0 := fun b hb ↦ by
    rw [show b = (b - B) + B by omega, pow_add, Module.End.mul_apply, hB, map_zero]
  set S : Finset M := ((Finset.range A') ×ˢ (Finset.range B)).image fun p ↦ (F ^ p.1) ((E ^ p.2) x)
  set W := Submodule.span K (S : Set M)
  have hmem : ∀ a b, (F ^ a) ((E ^ b) x) ∈ W := by
    intro a b
    by_cases hb : b < B
    · by_cases ha : a < A'
      · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩,
            rfl⟩))
      · rw [hFA b hb a (by omega)]; exact zero_mem _
    · rw [hEB b (by omega), map_zero]; exact zero_mem _
  have hwt : ∀ b : ℕ, ⁅h, (E ^ b) x⁆ = (-(m : K) + 2 * b) • (E ^ b) x := fun b ↦ by
    rw [← toEnd_apply_apply (R := K), ← Module.End.mul_apply, t.toEnd_h_mul_e_pow,
      LinearMap.add_apply, Module.End.mul_apply, toEnd_apply_apply, hx, map_smul,
      LinearMap.smul_apply, ← add_smul, add_comm]
  have hstab : ∀ T : Module.End K M, (∀ a b, T ((F ^ a) ((E ^ b) x)) ∈ W) → ∀ v ∈ W, T v ∈ W := by
    intro T hT v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      exact hT a b
    | zero => rw [map_zero]; exact zero_mem _
    | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
    | smul c v _ hv => rw [map_smul]; exact W.smul_mem c hv
  have hfW : ∀ v ∈ W, ⁅f, v⁆ ∈ W := hstab F fun a b ↦ by
    rw [← Module.End.mul_apply, ← pow_succ']; exact hmem _ _
  have hhW : ∀ v ∈ W, ⁅h, v⁆ ∈ W := hstab (toEnd K L M h) fun a b ↦ by
    rw [toEnd_apply_apply, t.lie_h_pow_toEnd_f_of_eq (hwt b)]; exact W.smul_mem _ (hmem _ _)
  have heW : ∀ v ∈ W, ⁅e, v⁆ ∈ W := hstab E fun a b ↦ by
    rcases a with _ | a
    · rw [pow_zero, Module.End.one_apply, ← Module.End.mul_apply, ← pow_succ']
      simpa using hmem 0 (b + 1)
    · rw [toEnd_apply_apply, t.lie_e_pow_succ_toEnd_f, hwt b, ← sub_smul, map_smul]
      refine add_mem ?_ (W.smul_mem _ (W.smul_mem _ (hmem _ _)))
      have : ⁅e, (E ^ b) x⁆ = (E ^ (b + 1)) x := by rw [pow_succ', Module.End.mul_apply]; rfl
      rw [this]
      exact hmem _ _
  -- the finite-dimensional submodule `W` over the subalgebra spanned by the triple
  set L' := LieSubalgebra.lieSpan K L {h, e, f}
  have hL' : ∀ z ∈ L', ∀ v ∈ W, ⁅z, v⁆ ∈ W := by
    intro z hz
    induction hz using LieSubalgebra.lieSpan_induction with
    | mem z hz =>
      rcases hz with rfl | rfl | rfl
      · exact hhW
      · exact heW
      · exact hfW
    | zero => intro v _; rw [zero_lie]; exact zero_mem _
    | add z z' _ _ hz hz' => intro v hv; rw [add_lie]; exact add_mem (hz v hv) (hz' v hv)
    | smul c z _ hz => intro v hv; rw [smul_lie]; exact W.smul_mem c (hz v hv)
    | lie z z' _ _ hz hz' =>
      intro v hv
      rw [lie_lie]
      exact sub_mem (hz _ (hz' v hv)) (hz' _ (hz v hv))
  let Y : LieSubmodule K L' M :=
    { W with lie_mem := fun {z v} hv ↦ hL' z z.2 v hv }
  have : FiniteDimensional K Y := FiniteDimensional.span_finset K S
  let h' : L' := ⟨h, LieSubalgebra.subset_lieSpan (by simp)⟩
  let e' : L' := ⟨e, LieSubalgebra.subset_lieSpan (by simp)⟩
  let f' : L' := ⟨f, LieSubalgebra.subset_lieSpan (by simp)⟩
  have t' : IsSl2Triple h' e' f' :=
    { h_ne_zero := fun h0 ↦ t.h_ne_zero (congrArg Subtype.val h0)
      lie_e_f := Subtype.ext t.lie_e_f
      lie_h_e_nsmul := Subtype.ext t.lie_h_e_nsmul
      lie_h_f_nsmul := Subtype.ext t.lie_h_f_nsmul }
  have hxY : x ∈ Y := by
    change x ∈ W
    simpa using hmem 0 0
  have hpow : ∀ n (y : Y), ((toEnd K L' Y e' ^ n) y : M) = (E ^ n) (y : M) := by
    intro n y
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  have := t'.eq_zero_of_toEnd_e_pow_eq_zero_of_finiteDimensional (M := Y) (x := ⟨x, hxY⟩)
    (Subtype.ext hx) hkm (Subtype.ext (by rw [hpow]; exact hk))
  exact congrArg Subtype.val this

end IsSl2Triple
