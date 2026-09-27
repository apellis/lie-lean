/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.GroupTheory.Coxeter.Exchange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-!
# The geometric representation and the order of `sᵢ sⱼ`

Let `cs : CoxeterSystem M W` be a Coxeter system. We construct a version of the geometric
representation of `W` ([HumC] §5.3, [Bou] Ch. V §4) on `V = B →₀ K`, for an algebraically closed
field `K` of characteristic zero: `W` acts through the reflections `σᵢ v = v - 2 B(αᵢ, v) αᵢ`,
where `B(αᵢ, αⱼ) = -cos(π / mᵢⱼ)`. To stay within algebra, `cos(π / m)` is replaced by
`(ζ + ζ⁻¹) / 2` for a chosen `ζ ∈ K` of multiplicative order `2m` (and by `1` if `m = ∞`); for
`K = ℂ` and `ζ = e^{πi/m}` this is the usual (complexified) representation.

On the plane spanned by `αᵢ, αⱼ` the element `σᵢ σⱼ` acts with eigenvalues `ζ^{±2}`; the closed
formula `Module.End.sub_smul_pow_mul_apply` for its powers shows that `(σᵢ σⱼ)^{mᵢⱼ} = 1` (so the
`σᵢ` define a representation of `W`) and that `(σᵢ σⱼ)^k ≠ 1` for `0 < k < mᵢⱼ`. Hence
`sᵢ sⱼ` has order exactly `mᵢⱼ` in `W`, the simple reflections are distinct (two items of the
TODO list of `Mathlib/GroupTheory/Coxeter/Basic.lean`), and alternating words
`⋯ sᵢ sⱼ sᵢ sⱼ` of length at most `mᵢⱼ` are reduced. The last fact is what Matsumoto's theorem
needs.

## Main definitions

* `CoxeterMatrix.geomReflection`: the reflections `σᵢ` of the geometric representation.
* `CoxeterSystem.geometricRepresentation`: the representation `W →* Module.End K (B →₀ K)`.

## Main results

* `IsAlgClosed.exists_orderOf_eq`: an algebraically closed field of characteristic zero has
  elements of every finite order.
* `CoxeterSystem.orderOf_simple_mul_simple`: `orderOf (sᵢ sⱼ) = mᵢⱼ`.
* `CoxeterSystem.simple_injective`: the simple reflections are distinct.
* `CoxeterSystem.isReduced_alternatingWord`: alternating words of length `≤ mᵢⱼ` are reduced.

## Implementation notes

The proof that `(σᵢ σⱼ)^{mᵢⱼ}` is the identity on all of `V` (not only on the plane of `αᵢ, αⱼ`)
writes a vector as the sum of a vector in that plane and a vector fixed by `σᵢ` and `σⱼ`; this
uses that the form is nondegenerate on the plane, i.e. `cos²(π / m) ≠ 1` for `m ≥ 2`. The
reducedness of alternating words is deduced from the order of `sᵢ sⱼ` via the criterion
`CoxeterSystem.isReduced_iff_nodup_leftInvSeq`; these arguments were reconstructed by us.

## References

* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §5.3–5.4.
* [Bou] N. Bourbaki, *Lie groups and Lie algebras*, Ch. IV–VI, Ch. V §4.
-/

open Polynomial in
/-- An algebraically closed field of characteristic zero contains an element of every positive
multiplicative order. -/
theorem IsAlgClosed.exists_orderOf_eq (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hn : 0 < n) : ∃ ζ : K, orderOf ζ = n := by
  have : NeZero n := ⟨hn.ne'⟩
  classical
  have hsep : (X ^ n - C (1 : K)).Separable :=
    separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hn.ne') one_ne_zero
  have hnd : (nthRoots n (1 : K)).Nodup := nodup_roots hsep
  have hcard : Multiset.card (nthRoots n (1 : K)) = n := by
    rw [nthRoots, splits_iff_card_roots.mp (IsAlgClosed.splits _), natDegree_X_pow_sub_C]
  have : Nat.card (rootsOfUnity n K) = n := by
    rw [Nat.card_congr (rootsOfUnityEquivNthRoots K n),
      Nat.card_congr (Equiv.subtypeEquivRight fun x ↦
        (Multiset.mem_toFinset (s := nthRoots n (1 : K)) (a := x)).symm),
      Nat.card_eq_fintype_card, Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard]
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity n K)
  exact ⟨((g : Kˣ) : K), by rw [orderOf_units, Subgroup.orderOf_coe, hg, this]⟩

section Dihedral

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Closed form for the powers of a product of two reflections `σ, τ` of a plane spanned by
`α, β`, where `σ α = -α`, `τ β = -β` and the off-diagonal entries are `x + y` with `x y = 1`:
`(x - y) (στ)ᵏ α = (x^{2k+1} - y^{2k+1}) α + (x^{2k} - y^{2k}) β`. -/
theorem Module.End.sub_smul_pow_mul_apply {σ τ : Module.End K V} {α β : V} {x y : K}
    (hxy : x * y = 1) (hσα : σ α = -α) (hσβ : σ β = β + (x + y) • α)
    (hτα : τ α = α + (x + y) • β) (hτβ : τ β = -β) (k : ℕ) :
    (x - y) • ((σ * τ) ^ k) α =
      (x ^ (2 * k + 1) - y ^ (2 * k + 1)) • α + (x ^ (2 * k) - y ^ (2 * k)) • β := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ← map_smul, ih, map_add, map_smul, map_smul,
      Module.End.mul_apply, Module.End.mul_apply, hτα, hτβ, map_add, map_smul, map_neg, hσα, hσβ]
    have e1 : (x ^ (2 * k + 1) - y ^ (2 * k + 1)) * ((x + y) ^ 2 - 1) -
        (x ^ (2 * k) - y ^ (2 * k)) * (x + y) = x ^ (2 * (k + 1) + 1) - y ^ (2 * (k + 1) + 1) := by
      linear_combination (2 * x ^ (2 * k) * x + x ^ (2 * k) * y - y ^ (2 * k) * x -
        2 * y ^ (2 * k) * y) * hxy
    have e2 : (x ^ (2 * k + 1) - y ^ (2 * k + 1)) * (x + y) - (x ^ (2 * k) - y ^ (2 * k)) =
        x ^ (2 * (k + 1)) - y ^ (2 * (k + 1)) := by
      linear_combination (x ^ (2 * k) - y ^ (2 * k)) * hxy
    rw [← e1, ← e2]
    module

/-- Closed form for the powers of a product of two reflections `σ, τ` of a plane spanned by
`α, β` with off-diagonal entries `2`: `(στ)ᵏ α = (2k + 1) α + 2k β`. -/
theorem Module.End.pow_mul_apply_of_two {σ τ : Module.End K V} {α β : V}
    (hσα : σ α = -α) (hσβ : σ β = β + (2 : K) • α)
    (hτα : τ α = α + (2 : K) • β) (hτβ : τ β = -β) (k : ℕ) :
    ((σ * τ) ^ k) α = (2 * k + 1 : K) • α + (2 * k : K) • β := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, map_smul,
      Module.End.mul_apply, Module.End.mul_apply, hτα, hτβ, map_add, map_smul, map_neg, hσα, hσβ]
    push_cast
    module

variable {σ τ : Module.End K V} {α β : V} {φ ψ : V →ₗ[K] K} {c : K}

private theorem aux_hyps (hσ : ∀ v, σ v = v - (2 * φ v) • α)
    (hτ : ∀ v, τ v = v - (2 * ψ v) • β) (hφα : φ α = 1) (hφβ : φ β = -c) (hψα : ψ α = -c)
    (hψβ : ψ β = 1) :
    σ α = -α ∧ σ β = β + (2 * c) • α ∧ τ α = α + (2 * c) • β ∧ τ β = -β := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hσ, hφα]; module
  · rw [hσ, hφβ]; module
  · rw [hτ, hψα]; module
  · rw [hτ, hψβ]; module

/-- Let `σ, τ` be the reflections `σ v = v - 2 φ(v) α`, `τ v = v - 2 ψ(v) β` with
`φ(α) = ψ(β) = 1` and `φ(β) = ψ(α) = -c`, where `2c = x + x⁻¹` for an element `x` with
`x^{2m} = 1` and `x² ≠ 1`. Then `(στ)^m = 1`. -/
theorem Module.End.mul_pow_eq_one_of_reflections (hσ : ∀ v, σ v = v - (2 * φ v) • α)
    (hτ : ∀ v, τ v = v - (2 * ψ v) • β) (hφα : φ α = 1) (hφβ : φ β = -c) (hψα : ψ α = -c)
    (hψβ : ψ β = 1) {x : K} (hx : x ≠ 0) (hc : 2 * c = x + x⁻¹) (hx2 : x ^ 2 ≠ 1) {m : ℕ}
    (hxm : x ^ (2 * m) = 1) : (σ * τ) ^ m = 1 := by
  obtain ⟨hσα, hσβ, hτα, hτβ⟩ := aux_hyps hσ hτ hφα hφβ hψα hψβ
  rw [hc] at hσβ hτα
  have hxy : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have hym : x⁻¹ ^ (2 * m) = 1 := by rw [inv_pow, hxm, inv_one]
  have hne : x - x⁻¹ ≠ 0 := by
    intro h
    apply hx2
    have hxx : x = x⁻¹ := sub_eq_zero.mp h
    calc x ^ 2 = x * x := sq x
      _ = x * x⁻¹ := by rw [← hxx]
      _ = 1 := hxy
  have hgα : ((σ * τ) ^ m) α = α := by
    have := Module.End.sub_smul_pow_mul_apply hxy hσα hσβ hτα hτβ m
    rw [pow_succ, pow_succ, hxm, hym, sub_self, zero_smul, add_zero, one_mul, one_mul] at this
    exact smul_right_injective V hne this
  have hhβ : ((τ * σ) ^ m) β = β := by
    have := Module.End.sub_smul_pow_mul_apply hxy hτβ hτα hσβ hσα m
    rw [pow_succ, pow_succ, hxm, hym, sub_self, zero_smul, add_zero, one_mul, one_mul] at this
    exact smul_right_injective V hne this
  have hσσ : σ * σ = 1 := by
    refine LinearMap.ext fun v ↦ ?_
    rw [Module.End.mul_apply, hσ (σ v), hσ v, map_sub, map_smul, hφα, Module.End.one_apply]
    module
  have hττ : τ * τ = 1 := by
    refine LinearMap.ext fun v ↦ ?_
    rw [Module.End.mul_apply, hτ (τ v), hτ v, map_sub, map_smul, hψβ, Module.End.one_apply]
    module
  have h1 : σ * τ * (τ * σ) = 1 := by
    rw [mul_assoc, ← mul_assoc τ, hττ, one_mul, hσσ]
  have h2 : τ * σ * (σ * τ) = 1 := by
    rw [mul_assoc, ← mul_assoc σ, hσσ, one_mul, hττ]
  have hgβ : ((σ * τ) ^ m) β = β := by
    conv_lhs => rw [← hhβ]
    rw [← Module.End.mul_apply, ← (show Commute (σ * τ) (τ * σ) from h1.trans h2.symm).mul_pow,
      h1, one_pow, Module.End.one_apply]
  -- a general vector differs from a combination of `α, β` by a vector fixed by `σ` and `τ`
  have hd : 1 - c ^ 2 ≠ 0 := by
    intro h
    apply hne
    have : (x - x⁻¹) ^ 2 = 0 := by
      linear_combination (-4) * h - (2 * c + x + x⁻¹) * hc - 4 * hxy
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  refine LinearMap.ext fun v ↦ ?_
  set a := (φ v + c * ψ v) / (1 - c ^ 2)
  set b := (ψ v + c * φ v) / (1 - c ^ 2)
  have hw1 : φ (v - (a • α + b • β)) = 0 := by
    simp only [map_sub, map_add, map_smul, hφα, hφβ, smul_eq_mul, a, b]
    field_simp
    ring
  have hw2 : ψ (v - (a • α + b • β)) = 0 := by
    simp only [map_sub, map_add, map_smul, hψα, hψβ, smul_eq_mul, a, b]
    field_simp
    ring
  have hfix : ∀ n, ((σ * τ) ^ n) (v - (a • α + b • β)) = v - (a • α + b • β) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, hτ, hw2, mul_zero, zero_smul,
        sub_zero, hσ, hw1, mul_zero, zero_smul, sub_zero, ih]
  have hv : v = (v - (a • α + b • β)) + (a • α + b • β) := by abel
  rw [hv, map_add, hfix, map_add, map_smul, map_smul, hgα, hgβ, Module.End.one_apply]

/-- With the notation of `Module.End.mul_pow_eq_one_of_reflections`, if `x` has multiplicative
order `2m` and `α, β` are linearly independent, then `(στ)^k α ≠ α` for `0 < k < m`. -/
theorem Module.End.mul_pow_apply_ne_of_reflections (hσ : ∀ v, σ v = v - (2 * φ v) • α)
    (hτ : ∀ v, τ v = v - (2 * ψ v) • β) (hφα : φ α = 1) (hφβ : φ β = -c) (hψα : ψ α = -c)
    (hψβ : ψ β = 1) (hαβ : ∀ a b : K, a • α + b • β = 0 → a = 0 ∧ b = 0) [CharZero K] {x : K}
    (hc : 2 * c = x + x⁻¹) {m : ℕ} (hxm : orderOf x = 2 * m) {k : ℕ} (hk0 : 0 < k)
    (hkm : k < m) : ((σ * τ) ^ k) α ≠ α := by
  obtain ⟨hσα, hσβ, hτα, hτβ⟩ := aux_hyps hσ hτ hφα hφβ hψα hψβ
  rw [hc] at hσβ hτα
  have hx : x ≠ 0 := by
    rintro rfl
    rw [orderOf_eq_zero_iff'.mpr (fun n hn ↦ by simp [zero_pow hn.ne'])] at hxm
    omega
  have hxy : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  intro h
  have := Module.End.sub_smul_pow_mul_apply hxy hσα hσβ hτα hτβ k
  rw [h] at this
  obtain ⟨h1, h2⟩ := hαβ (x ^ (2 * k + 1) - x⁻¹ ^ (2 * k + 1) - (x - x⁻¹))
    (x ^ (2 * k) - x⁻¹ ^ (2 * k)) (by rw [sub_smul, this]; abel)
  -- `x^{2k} = x^{-2k}`, so `x^{4k} = 1` and `2k = m`
  have h4 : x ^ (2 * k) * x ^ (2 * k) = 1 :=
    calc x ^ (2 * k) * x ^ (2 * k) = x ^ (2 * k) * x⁻¹ ^ (2 * k) := by
          rw [← sub_eq_zero.mp h2]
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
  have hdvd : 2 * m ∣ 2 * k + 2 * k := by
    rw [← hxm]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_add, h4])
  have hkm' : 2 * k = m := by
    obtain ⟨d, hd⟩ := hdvd
    rcases d with _ | _ | d <;> [omega; omega; nlinarith]
  -- then `x^m = -1`, and `h1` gives `x = x⁻¹`
  have hxm1 : x ^ m ≠ 1 := by
    intro h'
    have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h')
    omega
  have hxm2 : x ^ m = -1 := by
    have : (x ^ m - 1) * (x ^ m + 1) = 0 := by
      rw [← hkm']
      linear_combination h4
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hxm1
    · exact eq_neg_of_add_eq_zero_left h
  have hym : x⁻¹ ^ m = -1 := by rw [inv_pow, hxm2, inv_neg, inv_one]
  rw [hkm', pow_succ, pow_succ, hxm2, hym] at h1
  have hxx : x = x⁻¹ := by
    have : (2 : K) * (x - x⁻¹) = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left two_ne_zero)
  have : x ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hxx]; exact hxy
  have := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one this)
  omega

/-- With the notation of `Module.End.mul_pow_eq_one_of_reflections` and `c = 1`, if `α, β` are
linearly independent over a field of characteristic zero, then `(στ)^k α ≠ α` for `k > 0`. -/
theorem Module.End.mul_pow_apply_ne_of_reflections_of_eq_one
    (hσ : ∀ v, σ v = v - (2 * φ v) • α) (hτ : ∀ v, τ v = v - (2 * ψ v) • β) (hφα : φ α = 1)
    (hφβ : φ β = -1) (hψα : ψ α = -1) (hψβ : ψ β = 1)
    (hαβ : ∀ a b : K, a • α + b • β = 0 → a = 0 ∧ b = 0) [CharZero K] {k : ℕ} (hk0 : 0 < k) :
    ((σ * τ) ^ k) α ≠ α := by
  obtain ⟨hσα, hσβ, hτα, hτβ⟩ := aux_hyps hσ hτ hφα hφβ hψα hψβ
  rw [mul_one] at hσβ hτα
  intro h
  rw [Module.End.pow_mul_apply_of_two hσα hσβ hτα hτβ k] at h
  have e : (2 * k : K) • α + (2 * k : K) • β = ((2 * k + 1 : K) • α + (2 * k : K) • β) - α := by
    module
  obtain ⟨-, h2⟩ := hαβ (2 * k) (2 * k) (by rw [e, h, sub_self])
  norm_cast at h2
  omega

end Dihedral

private theorem smul_single_add_smul_single_eq_zero {K B : Type*} [Field K] {i j : B}
    (hij : i ≠ j) (a b : K) :
    a • Finsupp.single i (1 : K) + b • Finsupp.single j 1 = 0 → a = 0 ∧ b = 0 := by
  intro h
  exact ⟨by simpa [Finsupp.single_apply, hij.symm] using congrArg (· i) h,
    by simpa [Finsupp.single_apply, hij] using congrArg (· j) h⟩

namespace CoxeterMatrix

variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]

/-- For `m > 0`, a chosen element of `K` of multiplicative order `2m`, playing the role of
`e^{πi/m}`; for `m = 0` it is `1`. -/
noncomputable def geomRoot (m : ℕ) : K :=
  if h : 0 < m then Classical.choose (IsAlgClosed.exists_orderOf_eq K (Nat.mul_pos two_pos h))
  else 1

/-- `geomRoot K m` has order `2m`. -/
theorem orderOf_geomRoot {m : ℕ} (hm : 0 < m) : orderOf (geomRoot K m) = 2 * m := by
  simp only [geomRoot, hm, ↓reduceDIte]
  exact Classical.choose_spec (IsAlgClosed.exists_orderOf_eq K (Nat.mul_pos two_pos hm))

/-- `ζ^{2m} = 1`. -/
theorem geomRoot_pow_two_mul (m : ℕ) : geomRoot K m ^ (2 * m) = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [← orderOf_geomRoot K hm]
    exact pow_orderOf_eq_one _

/-- `ζ ≠ 0`. -/
theorem geomRoot_ne_zero (m : ℕ) : geomRoot K m ≠ 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [geomRoot]
  · intro h
    have := geomRoot_pow_two_mul K m
    rw [h, zero_pow (by omega)] at this
    exact zero_ne_one this

/-- `ζ² ≠ 1` for `m ≥ 2`. -/
theorem geomRoot_sq_ne_one {m : ℕ} (hm : 1 < m) : geomRoot K m ^ 2 ≠ 1 := by
  intro h
  have := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h)
  rw [orderOf_geomRoot K (by omega)] at this
  omega

/-- The coefficient `cos(π/m)` of the geometric representation: `(ζ + ζ⁻¹)/2` for
`ζ = geomRoot K m` if `m > 0`, and `1` if `m = 0` (that is, `m = ∞`). -/
noncomputable def geomCoeff (m : ℕ) : K :=
  if m = 0 then 1 else (geomRoot K m + (geomRoot K m)⁻¹) / 2

/-- `2 cos(π/m) = ζ + ζ⁻¹`. -/
theorem two_mul_geomCoeff {m : ℕ} (hm : m ≠ 0) :
    2 * geomCoeff K m = geomRoot K m + (geomRoot K m)⁻¹ := by
  simp only [geomCoeff, hm, ↓reduceIte]
  ring

/-- `cos(π/∞) = 1`. -/
theorem geomCoeff_zero : geomCoeff K 0 = 1 := by simp [geomCoeff]

/-- `cos(π/1) = -1`. -/
theorem geomCoeff_one : geomCoeff K 1 = -1 := by
  have h1 : geomRoot K 1 ^ 2 = 1 := by simpa using geomRoot_pow_two_mul K 1
  have h2 : geomRoot K 1 ≠ 1 := by
    intro h
    have := orderOf_geomRoot K one_pos
    rw [h, orderOf_one] at this
    omega
  have h3 : geomRoot K 1 = -1 := by
    have : (geomRoot K 1 - 1) * (geomRoot K 1 + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h2
    · exact eq_neg_of_add_eq_zero_left h
  simp only [geomCoeff, one_ne_zero, ↓reduceIte, h3]
  norm_num

variable {B : Type*} (M : CoxeterMatrix B)

/-- The linear form `v ↦ B(αᵢ, v)` on `V = B →₀ K`, where `B(αᵢ, αⱼ) = -cos(π / mᵢⱼ)`
(see `CoxeterMatrix.geomCoeff`). -/
noncomputable def geomForm (i : B) : (B →₀ K) →ₗ[K] K :=
  Finsupp.linearCombination K fun j ↦ -geomCoeff K (M i j)

/-- The reflection `σᵢ v = v - 2 B(αᵢ, v) αᵢ` of the geometric representation. -/
noncomputable def geomReflection (i : B) : Module.End K (B →₀ K) :=
  LinearMap.id - (M.geomForm K i).smulRight (Finsupp.single i 2)

/-- `B(αᵢ, a αⱼ) = -a cos(π / mᵢⱼ)`. -/
theorem geomForm_single (i j : B) (a : K) :
    M.geomForm K i (Finsupp.single j a) = a * -geomCoeff K (M i j) := by
  simp [geomForm, Finsupp.linearCombination_single]

/-- `B(αᵢ, a αᵢ) = a`. -/
theorem geomForm_single_self (i : B) (a : K) : M.geomForm K i (Finsupp.single i a) = a := by
  rw [geomForm_single, M.diagonal, geomCoeff_one]
  ring

/-- The defining formula of `σᵢ`. -/
theorem geomReflection_apply (i : B) (v : B →₀ K) :
    M.geomReflection K i v = v - M.geomForm K i v • Finsupp.single i 2 := rfl

/-- `σᵢ` fixes the hyperplane `B(αᵢ, -) = 0`. -/
theorem geomReflection_of_geomForm_eq_zero {i : B} {v : B →₀ K} (h : M.geomForm K i v = 0) :
    M.geomReflection K i v = v := by
  rw [geomReflection_apply, h, zero_smul, sub_zero]

/-- `σᵢ αⱼ = αⱼ + 2 cos(π / mᵢⱼ) αᵢ`. -/
theorem geomReflection_single (i j : B) :
    M.geomReflection K i (Finsupp.single j 1) =
      Finsupp.single j 1 + (2 * geomCoeff K (M i j)) • Finsupp.single i 1 := by
  rw [geomReflection_apply, geomForm_single, ← Finsupp.smul_single_one i (2 : K)]
  module

/-- `σᵢ αᵢ = -αᵢ`. -/
theorem geomReflection_single_self (i : B) :
    M.geomReflection K i (Finsupp.single i 1) = -Finsupp.single i 1 := by
  rw [geomReflection_single, M.diagonal, geomCoeff_one]
  module

/-- `σᵢ² = 1`. -/
theorem geomReflection_mul_self (i : B) : M.geomReflection K i * M.geomReflection K i = 1 := by
  refine LinearMap.ext fun v ↦ ?_
  have : M.geomForm K i (M.geomReflection K i v) = -M.geomForm K i v := by
    rw [geomReflection_apply, map_sub, map_smul, geomForm_single_self, smul_eq_mul]
    ring
  rw [Module.End.mul_apply, Module.End.one_apply,
    M.geomReflection_apply K i (M.geomReflection K i v), this, geomReflection_apply]
  module

/-- The formula `σᵢ v = v - 2 B(αᵢ, v) αᵢ`. -/
theorem geomReflection_apply' (i : B) (v : B →₀ K) :
    M.geomReflection K i v = v - (2 * M.geomForm K i v) • Finsupp.single i 1 := by
  rw [geomReflection_apply, ← Finsupp.smul_single_one i (2 : K), smul_smul, mul_comm]

/-- `B(αⱼ, αᵢ) = -cos(π / mᵢⱼ)`. -/
theorem geomForm_single_one_of_symm (i j : B) :
    M.geomForm K j (Finsupp.single i 1) = -geomCoeff K (M i j) := by
  rw [geomForm_single, one_mul, M.symmetric j i]

/-- The reflections `σᵢ` satisfy the Coxeter relations `(σᵢ σⱼ)^{mᵢⱼ} = 1`. -/
theorem isLiftable_geomReflection : M.IsLiftable (M.geomReflection K) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal, pow_one, geomReflection_mul_self]
  by_cases hm0 : M i j = 0
  · rw [hm0, pow_zero]
  have hm : 1 < M i j := by have := M.off_diagonal i j hij; omega
  exact Module.End.mul_pow_eq_one_of_reflections (M.geomReflection_apply' K i)
    (M.geomReflection_apply' K j) (M.geomForm_single_self K i 1)
    (by rw [geomForm_single, one_mul]) (M.geomForm_single_one_of_symm K i j)
    (M.geomForm_single_self K j 1) (geomRoot_ne_zero K _) (two_mul_geomCoeff K hm0)
    (geomRoot_sq_ne_one K hm) (geomRoot_pow_two_mul K _)

/-- For `i ≠ j` and `0 < k` with `k < mᵢⱼ` or `mᵢⱼ = ∞`, `(σᵢ σⱼ)^k` does not fix `αᵢ`. -/
theorem geomReflection_mul_pow_apply_ne {i j : B} (hij : i ≠ j) {k : ℕ} (hk0 : 0 < k)
    (hk : M i j = 0 ∨ k < M i j) :
    ((M.geomReflection K i * M.geomReflection K j) ^ k) (Finsupp.single i 1) ≠
      Finsupp.single i 1 := by
  rcases hk with hm0 | hk
  · have hc : geomCoeff K (M i j) = 1 := by rw [hm0, geomCoeff_zero]
    exact Module.End.mul_pow_apply_ne_of_reflections_of_eq_one (M.geomReflection_apply' K i)
      (M.geomReflection_apply' K j) (M.geomForm_single_self K i 1)
      (by rw [geomForm_single, one_mul, hc]) (by rw [geomForm_single_one_of_symm, hc])
      (M.geomForm_single_self K j 1) (smul_single_add_smul_single_eq_zero hij) hk0
  · exact Module.End.mul_pow_apply_ne_of_reflections (M.geomReflection_apply' K i)
      (M.geomReflection_apply' K j) (M.geomForm_single_self K i 1)
      (by rw [geomForm_single, one_mul]) (M.geomForm_single_one_of_symm K i j)
      (M.geomForm_single_self K j 1) (smul_single_add_smul_single_eq_zero hij)
      (two_mul_geomCoeff K (by omega)) (orderOf_geomRoot K (by omega)) hk0 hk

end CoxeterMatrix

namespace CoxeterSystem

variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The geometric representation of `W` on `B →₀ K` ([HumC] §5.3, [Bou] Ch. V §4), with
`cos(π / m)` replaced by `(ζ + ζ⁻¹) / 2` for an element `ζ ∈ K` of order `2m`
(`CoxeterMatrix.geomCoeff`); for `K = ℂ` and `ζ = e^{πi/m}` this is the complexification of the
usual geometric representation. -/
noncomputable def geometricRepresentation : W →* Module.End K (B →₀ K) :=
  cs.lift ⟨M.geomReflection K, M.isLiftable_geomReflection K⟩

/-- The geometric representation maps `sᵢ` to `σᵢ`. -/
theorem geometricRepresentation_simple (i : B) :
    cs.geometricRepresentation K (cs.simple i) = M.geomReflection K i :=
  cs.lift_apply_simple _ i

omit K

/-- The order of `sᵢ sⱼ` is exactly `mᵢⱼ` (with `orderOf = 0` meaning infinite order, matching
the convention `mᵢⱼ = 0` for `mᵢⱼ = ∞`) ([HumC] §5.3–5.4, [Bou] Ch. V §4.3 (check)). -/
theorem orderOf_simple_mul_simple (i j : B) : orderOf (cs.simple i * cs.simple j) = M i j := by
  by_cases hij : i = j
  · subst hij
    simp
  let K := AlgebraicClosure ℚ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have key : ∀ k, 0 < k → (M i j = 0 ∨ k < M i j) → (cs.simple i * cs.simple j) ^ k ≠ 1 := by
    intro k hk0 hk h
    apply M.geomReflection_mul_pow_apply_ne K hij hk0 hk
    have := congrArg (cs.geometricRepresentation K) h
    rw [map_pow, map_mul, geometricRepresentation_simple, geometricRepresentation_simple,
      map_one] at this
    rw [this, Module.End.one_apply]
  by_cases hm0 : M i j = 0
  · rw [hm0, orderOf_eq_zero_iff']
    exact fun k hk ↦ key k hk (.inl hm0)
  · rw [orderOf_eq_iff (Nat.pos_of_ne_zero hm0)]
    exact ⟨cs.simple_mul_simple_pow i j, fun k hk hk0 ↦ key k hk0 (.inr hk)⟩

/-- The simple reflections are pairwise distinct. -/
theorem simple_injective : Function.Injective cs.simple := by
  intro i j h
  by_contra hij
  have := cs.orderOf_simple_mul_simple i j
  rw [h, simple_mul_simple_self, orderOf_one] at this
  exact M.off_diagonal i j hij this.symm

private theorem nodup_take_leftInvSeq_alternatingWord (a b : B) {k : ℕ}
    (hk : M a b = 0 ∨ k ≤ M a b) :
    ((cs.leftInvSeq (alternatingWord a b (2 * k))).take k).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro n n' hn hn' hlt
  simp only [List.length_take, length_leftInvSeq, length_alternatingWord] at hn hn'
  rw [List.getElem_take, List.getElem_take,
    getElem_leftInvSeq_alternatingWord cs a b k n (by omega),
    getElem_leftInvSeq_alternatingWord cs a b k n' (by omega), prod_alternatingWord_eq_mul_pow,
    prod_alternatingWord_eq_mul_pow]
  simp only [Nat.not_even_two_mul_add_one, ↓reduceIte]
  rw [show (2 * n + 1) / 2 = n by omega, show (2 * n' + 1) / 2 = n' by omega]
  intro h
  replace h := mul_left_cancel h
  have hord := cs.orderOf_simple_mul_simple b a
  rw [M.symmetric b a] at hord
  rcases hk with h0 | hk
  · rw [h0] at hord
    have := injective_pow_iff_not_isOfFinOrder.mpr (orderOf_eq_zero_iff.mp hord) h
    omega
  · have := pow_injOn_Iio_orderOf (x := cs.simple b * cs.simple a)
      (by rw [Set.mem_Iio, hord]; omega) (by rw [Set.mem_Iio, hord]; omega) h
    omega

/-- Alternating words `⋯ sᵢ sⱼ` of length at most `mᵢⱼ` are reduced (a standard consequence of
the fact that `sᵢ sⱼ` has order `mᵢⱼ`, cf. [HumC] §5.4 (check)). -/
theorem isReduced_alternatingWord (i j : B) {k : ℕ} (hk : M i j = 0 ∨ k ≤ M i j) :
    cs.IsReduced (alternatingWord i j k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [IsReduced, alternatingWord]
  rw [isReduced_iff_nodup_leftInvSeq]
  by_cases he : Even k
  · have := listTake_alternatingWord i j k k (by omega)
    simp only [he, ↓reduceIte] at this
    rw [← this, leftInvSeq_take]
    exact cs.nodup_take_leftInvSeq_alternatingWord i j hk
  · have := listTake_alternatingWord j i k k (by omega)
    simp only [he, ↓reduceIte] at this
    rw [← this, leftInvSeq_take]
    exact cs.nodup_take_leftInvSeq_alternatingWord j i (by rwa [M.symmetric j i])

/-- The length of an alternating word of length at most `mᵢⱼ`. -/
theorem length_wordProd_alternatingWord (i j : B) {k : ℕ} (hk : M i j = 0 ∨ k ≤ M i j) :
    cs.length (cs.wordProd (alternatingWord i j k)) = k := by
  rw [(cs.isReduced_alternatingWord i j hk).eq, length_alternatingWord]

end CoxeterSystem
