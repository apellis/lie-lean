/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Finite-dimensional representations of `𝔰𝔩₂`

Let `(h, e, f)` be an `𝔰𝔩₂`-triple in a Lie algebra `L` over a field `K` of characteristic zero,
and `M` a finite-dimensional `L`-module. We show that `e` and `f` act nilpotently on `M` and that
`h` acts diagonalizably with integer eigenvalues. Over an algebraically closed field these are
usually deduced from Weyl's complete reducibility theorem and the classification of irreducible
`𝔰𝔩₂`-modules ([Hum] §7.2); we give a direct argument that works over any field of characteristic
zero, without assuming that the eigenvalues of `h` lie in `K`. The argument was reconstructed by
us; it is a variant of the usual Casimir-operator proof of complete reducibility.

## Main definitions

* `IsSl2Triple.casimir`: the Casimir operator `Ω = h² + 2h + 4fe` acting on `M`.
* `IsSl2Triple.primitiveSpan`: the subspace `∑ⱼ fʲ (ker e ∩ ker (h - m))`.

## Main results

* `IsSl2Triple.isNilpotent_toEnd_e`, `IsSl2Triple.isNilpotent_toEnd_f`: `e` and `f` act
  nilpotently. Proof: on the stable range `R` of the powers of `e`, `e` is invertible and
  `h = e h e⁻¹ + 2`; taking traces gives `2 dim R = 0`.
* `IsSl2Triple.aeval_prod_apply_mem`: if `fᴺ⁺¹ = 0` then `h (h - 1) ⋯ (h - N)` kills `ker e`
  (also relative to a stable subspace).
* `IsSl2Triple.mem_primitiveSpan`: vectors in the generalized `m(m + 2)`-eigenspace of `Ω` lie in
  `∑ⱼ fʲ (ker e ∩ ker (h - m))`.
* `IsSl2Triple.iSup_eigenspace_toEnd_h_eq_top`: `M = ⨁_{k ∈ ℤ} ker (h - k)`.

## References

* [Hum] J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9,
  §6.2–6.3, §7.
-/

open LieModule Module Polynomial

namespace Module.End

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {T : Module.End K M}
  {P : Submodule K M}

/-- A subspace stable under `T` is stable under every polynomial in `T`. -/
lemma aeval_apply_mem (hP : ∀ x ∈ P, T x ∈ P) (q : K[X]) {x : M} (hx : x ∈ P) :
    aeval T q x ∈ P := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine P.smul_mem a ?_
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hP _ ih

/-- A subspace stable under `T` is stable under every power of `T`. -/
lemma pow_apply_mem (hP : ∀ x ∈ P, T x ∈ P) (n : ℕ) {x : M} (hx : x ∈ P) : (T ^ n) x ∈ P := by
  simpa using aeval_apply_mem hP (X ^ n) hx

/-- If `a(T) x` and `b(T) x` lie in a `T`-stable subspace `P`, so does `(c a + d b)(T) x`. -/
lemma aeval_add_mul_apply_mem (hP : ∀ x ∈ P, T x ∈ P) (c d : K[X]) {a b : K[X]} {x : M}
    (ha : aeval T a x ∈ P) (hb : aeval T b x ∈ P) : aeval T (c * a + d * b) x ∈ P := by
  rw [map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply]
  exact add_mem (aeval_apply_mem hP c ha) (aeval_apply_mem hP d hb)

/-- A polynomial in `T` commutes with every endomorphism commuting with `T`. -/
lemma commute_aeval_left {S : Module.End K M} (hTS : Commute T S) (q : K[X]) :
    Commute (aeval T q) S := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left a S).mul_left (hTS.pow_left n)

/-- If `p(T) x ∈ P` for `p = ∏_{k ≤ N} (X - k)` and `((X - m)ʳ w)(T) x ∈ P` with `w` coprime to
the factors `X - k`, `k ≠ m`, of `p`, then `(T - m) x ∈ P`. -/
lemma aeval_X_sub_C_apply_mem [CharZero K] (hP : ∀ x ∈ P, T x ∈ P) {x : M} {N m r : ℕ}
    {w : K[X]} (hw : IsCoprime (∏ k ∈ (Finset.range (N + 1)).erase m, (X - C (k : K))) w)
    (hp : aeval T (∏ k ∈ Finset.range (N + 1), (X - C (k : K))) x ∈ P)
    (hg : aeval T ((X - C (m : K)) ^ r * w) x ∈ P) : aeval T (X - C (m : K)) x ∈ P := by
  have hu : IsCoprime (∏ k ∈ (Finset.range (N + 1)).erase m, (X - C (k : K)))
      ((X - C (m : K)) ^ r) := IsCoprime.pow_right
    (IsCoprime.prod_left fun k hk ↦ isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr (by exact_mod_cast Finset.ne_of_mem_erase hk)).isUnit)
  generalize hu_def : ∏ k ∈ (Finset.range (N + 1)).erase m, (X - C (k : K)) = u at hu hw
  obtain ⟨a, b, hab⟩ := hu.mul_right hw
  have hdvd : (∏ k ∈ Finset.range (N + 1), (X - C (k : K))) ∣ (X - C (m : K)) * u := by
    by_cases hm : m ∈ Finset.range (N + 1)
    · rw [← hu_def, Finset.mul_prod_erase _ (fun k : ℕ ↦ X - C (k : K)) hm]
    · rw [← hu_def, Finset.erase_eq_of_notMem hm]
      exact dvd_mul_left _ _
  obtain ⟨z, hz⟩ := hdvd
  have h1 : aeval T ((X - C (m : K)) * u) x ∈ P := by
    rw [hz, mul_comm, map_mul, Module.End.mul_apply]
    exact aeval_apply_mem hP z hp
  have heq : X - C (m : K) = a * ((X - C (m : K)) * u) + b * (X - C (m : K)) *
      ((X - C (m : K)) ^ r * w) := by
    linear_combination (-(X - C (m : K))) * hab
  rw [heq]
  exact aeval_add_mul_apply_mem hP a (b * (X - C (m : K))) h1 hg

/-- Kernel of a product of pairwise coprime polynomials in `T`. -/
lemma ker_aeval_prod_le_iSup {ι : Type*} (T : Module.End K M) (s : Finset ι)
    (g : ι → K[X]) (hg : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (g i) (g j)) :
    LinearMap.ker (aeval T (∏ i ∈ s, g i)) ≤ ⨆ i ∈ s, LinearMap.ker (aeval T (g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert a s ha ih =>
    have hcop : IsCoprime (g a) (∏ i ∈ s, g i) := IsCoprime.prod_right fun i hi ↦
      hg a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hcop]
    refine sup_le (le_biSup (fun i ↦ LinearMap.ker (aeval T (g i))) (Finset.mem_insert_self a s))
      ((ih fun i hi j hj ↦ hg i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)).trans
        (biSup_mono fun i hi ↦ Finset.mem_insert_of_mem hi))

end Module.End

namespace IsSl2Triple

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] {h e f : L} (t : IsSl2Triple h e f)
variable (K M) in
/-- The Casimir operator `h² + 2h + 4fe` of an `𝔰𝔩₂`-triple `(h, e, f)`, acting on `M`. -/
def casimir (h e f : L) : Module.End K M :=
  toEnd K L M h * toEnd K L M h + (2 : K) • toEnd K L M h +
    (4 : K) • (toEnd K L M f * toEnd K L M e)

/-- `Ω v = h h v + 2 h v + 4 f e v`. -/
lemma casimir_apply (v : M) :
    casimir K M h e f v = ⁅h, ⁅h, v⁆⁆ + (2 : K) • ⁅h, v⁆ + (4 : K) • ⁅f, ⁅e, v⁆⁆ :=
  rfl

variable (K M) in
/-- The subspace `∑ⱼ fʲ (ker e ∩ ker (h - m))` spanned by the `f`-strings through the vectors of
weight `m` killed by `e`. -/
def primitiveSpan (h e f : L) (m : K) : Submodule K M :=
  ⨆ j : ℕ, (LinearMap.ker (toEnd K L M e) ⊓ (toEnd K L M h).eigenspace m).map (toEnd K L M f ^ j)

/-- `(X² + 2X - k(k + 2)) = (X - k)(X + k + 2)`, multiplied over `k ≤ N`. -/
lemma prod_comp_eq (N : ℕ) :
    (∏ k ∈ Finset.range (N + 1), (X - C ((k : K) * (k + 2)))).comp (X ^ 2 + 2 * X) =
      (∏ k ∈ Finset.range (N + 1), (X - C (k : K))) *
        ∏ k ∈ Finset.range (N + 1), (X + C ((k : K) + 2)) := by
  rw [prod_comp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  simp only [sub_comp, X_comp, C_comp]
  simp only [map_mul, map_add, C_ofNat]
  ring

/-- `((X - m(m + 2))ʳ)(X² + 2X) = (X - m)ʳ (X + m + 2)ʳ`. -/
lemma pow_comp_eq (m : K) (r : ℕ) :
    ((X - C (m * (m + 2))) ^ r).comp (X ^ 2 + 2 * X) = (X - C m) ^ r * (X + C (m + 2)) ^ r := by
  rw [pow_comp, ← mul_pow]
  congr 1
  simp only [sub_comp, X_comp, C_comp]
  simp only [map_mul, map_add, C_ofNat]
  ring

include t

/-- The Casimir operator commutes with `e`. -/
lemma commute_casimir_e : Commute (casimir K M h e f) (toEnd K L M e) := by
  have A1 : ∀ x : M, ⁅h, ⁅e, x⁆⁆ = ⁅e, ⁅h, x⁆⁆ + (2 : K) • ⁅e, x⁆ := fun x ↦ by
    rw [leibniz_lie h e x, t.lie_h_e_smul K, smul_lie, add_comm]
  have A2 : ∀ x : M, ⁅e, ⁅f, x⁆⁆ = ⁅f, ⁅e, x⁆⁆ + ⁅h, x⁆ := fun x ↦ by
    rw [leibniz_lie e f x, t.lie_e_f, add_comm]
  ext v
  simp only [Module.End.mul_apply, casimir_apply, toEnd_apply_apply, lie_add, lie_smul, A1, A2]
  module

/-- `h e = e h + 2 e` as endomorphisms. -/
lemma toEnd_h_mul_e : toEnd K L M h * toEnd K L M e =
    toEnd K L M e * toEnd K L M h + (2 : K) • toEnd K L M e := by
  ext m
  simp only [Module.End.mul_apply, toEnd_apply_apply, LinearMap.add_apply, LinearMap.smul_apply,
    leibniz_lie h e m, t.lie_h_e_smul K, smul_lie]
  abel

/-- `h f = f h - 2 f` as endomorphisms. -/
lemma toEnd_h_mul_f : toEnd K L M h * toEnd K L M f =
    toEnd K L M f * toEnd K L M h - (2 : K) • toEnd K L M f := by
  ext m
  simp only [Module.End.mul_apply, toEnd_apply_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    leibniz_lie h f m, t.lie_lie_smul_f K, smul_lie, neg_lie]
  abel

/-- `e f = f e + h` as endomorphisms. -/
lemma toEnd_e_mul_f : toEnd K L M e * toEnd K L M f =
    toEnd K L M f * toEnd K L M e + toEnd K L M h := by
  ext m
  simp only [Module.End.mul_apply, toEnd_apply_apply, LinearMap.add_apply,
    leibniz_lie e f m, t.lie_e_f]
  abel

/-- `h eⁿ = eⁿ h + 2n eⁿ`. -/
lemma toEnd_h_mul_e_pow (n : ℕ) : toEnd K L M h * toEnd K L M e ^ n =
    toEnd K L M e ^ n * toEnd K L M h + (2 * n : K) • toEnd K L M e ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc, t.toEnd_h_mul_e, mul_add, ← mul_assoc,
      smul_mul_assoc, mul_smul_comm, add_assoc, ← add_smul]
    push_cast; ring_nf

/-- `h fⁿ = fⁿ h - 2n fⁿ`. -/
lemma toEnd_h_mul_f_pow (n : ℕ) : toEnd K L M h * toEnd K L M f ^ n =
    toEnd K L M f ^ n * toEnd K L M h - (2 * n : K) • toEnd K L M f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, sub_mul, mul_assoc, t.toEnd_h_mul_f, mul_sub, ← mul_assoc,
      smul_mul_assoc, mul_smul_comm, sub_sub, ← add_smul]
    push_cast; ring_nf

/-- If `h w = c w`, then `h fʲ w = (c - 2j) fʲ w`. -/
lemma lie_h_pow_toEnd_f_of_eq {c : K} {w : M} (hw : ⁅h, w⁆ = c • w) (j : ℕ) :
    ⁅h, (toEnd K L M f ^ j) w⁆ = (c - 2 * j) • (toEnd K L M f ^ j) w := by
  rw [← toEnd_apply_apply (R := K), ← Module.End.mul_apply, t.toEnd_h_mul_f_pow,
    LinearMap.sub_apply, Module.End.mul_apply, toEnd_apply_apply, hw, map_smul,
    LinearMap.smul_apply, sub_smul]

/-- `e fⁿ⁺¹ v = fⁿ⁺¹ e v + (n + 1) fⁿ (h v - n v)`. -/
lemma lie_e_pow_succ_toEnd_f (n : ℕ) (v : M) :
    ⁅e, (toEnd K L M f ^ (n + 1)) v⁆ = (toEnd K L M f ^ (n + 1)) ⁅e, v⁆ +
      (n + 1 : K) • (toEnd K L M f ^ n) (⁅h, v⁆ - (n : K) • v) := by
  have base : ∀ v : M, ⁅e, ⁅f, v⁆⁆ = ⁅f, ⁅e, v⁆⁆ + ⁅h, v⁆ := fun v ↦ by
    rw [leibniz_lie, t.lie_e_f, add_comm]
  have hf : ∀ v : M, ⁅h, ⁅f, v⁆⁆ = ⁅f, ⁅h, v⁆⁆ - (2 : K) • ⁅f, v⁆ := fun v ↦ by
    rw [leibniz_lie, t.lie_lie_smul_f K, neg_lie, smul_lie]; abel
  have e1 : ∀ (n : ℕ) (w : M), (toEnd K L M f ^ (n + 1)) w = (toEnd K L M f ^ n) ⁅f, w⁆ := by
    intro n w; rw [pow_succ, Module.End.mul_apply, toEnd_apply_apply]
  induction n generalizing v with
  | zero => simp [base v]
  | succ n ih =>
    rw [e1 (n + 1) v, ih, base v, hf v, e1 (n + 1) ⁅e, v⁆]
    simp only [map_add, map_sub, map_smul, ← e1 n]
    push_cast
    module

/-- `e h w = h e w - 2 e w`. -/
lemma lie_e_lie_h (w : M) : ⁅e, ⁅h, w⁆⁆ = ⁅h, ⁅e, w⁆⁆ - (2 : K) • ⁅e, w⁆ := by
  rw [leibniz_lie h e w, t.lie_h_e_smul K, smul_lie]
  abel

section Stable

variable {P : Submodule K M} (hPe : ∀ x ∈ P, ⁅e, x⁆ ∈ P) (hPf : ∀ x ∈ P, ⁅f, x⁆ ∈ P)
  (hPh : ∀ x ∈ P, ⁅h, x⁆ ∈ P)
include hPe hPh

omit hPe in
/-- If `P` is stable under `h`, then so is `{w | e w ∈ P}`. -/
lemma comap_e_stable : ∀ w ∈ P.comap (toEnd K L M e),
    toEnd K L M h w ∈ P.comap (toEnd K L M e) := by
  intro w hw
  simp only [Submodule.mem_comap, toEnd_apply_apply] at hw ⊢
  rw [t.lie_e_lie_h (K := K)]
  exact sub_mem (hPh _ hw) (P.smul_mem _ hw)

include hPf

/-- Let `P` be stable under `e`, `f`, `h` and `e v ∈ P`. Then `q(Ω) v ≡ q(h² + 2h) v` modulo `P`
for every polynomial `q`, where `Ω` is the Casimir operator. -/
lemma aeval_casimir_sub_mem {v : M} (hv : ⁅e, v⁆ ∈ P) (q : K[X]) :
    aeval (casimir K M h e f) q v - aeval (toEnd K L M h) (q.comp (X ^ 2 + 2 * X)) v ∈ P := by
  set Ω := casimir K M h e f
  set D := aeval (toEnd K L M h) (X ^ 2 + 2 * X : K[X])
  have hW := t.comap_e_stable hPh
  have hDW : ∀ w ∈ P.comap (toEnd K L M e), D w ∈ P.comap (toEnd K L M e) :=
    fun w hw ↦ Module.End.aeval_apply_mem hW _ hw
  have hΩP : ∀ x ∈ P, Ω x ∈ P := fun x hx ↦ by
    rw [casimir_apply]
    exact add_mem (add_mem (hPh _ (hPh _ hx)) (P.smul_mem _ (hPh _ hx)))
      (P.smul_mem _ (hPf _ (hPe _ hx)))
  have hΩD : ∀ w ∈ P.comap (toEnd K L M e), Ω w - D w ∈ P := fun w hw ↦ by
    have : Ω w - D w = (4 : K) • ⁅f, ⁅e, w⁆⁆ := by
      simp only [Ω, D, casimir_apply, map_add, map_mul, aeval_X, LinearMap.add_apply,
        Module.End.mul_apply, sq, toEnd_apply_apply]
      rw [show (2 : K[X]) = C 2 from rfl, aeval_C, Module.algebraMap_end_apply]
      abel
    rw [this]
    exact P.smul_mem _ (hPf _ hw)
  have hpow : ∀ n : ℕ, (Ω ^ n) v - (D ^ n) v ∈ P := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hDn : (D ^ n) v ∈ P.comap (toEnd K L M e) := Module.End.pow_apply_mem hDW n hv
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        show Ω ((Ω ^ n) v) - D ((D ^ n) v) =
          Ω ((Ω ^ n) v - (D ^ n) v) + (Ω ((D ^ n) v) - D ((D ^ n) v)) by
          rw [map_sub]; abel]
      exact add_mem (hΩP _ ih) (hΩD _ hDn)
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      add_sub_add_comm]
    exact add_mem hp hq
  | monomial n a =>
    rw [monomial_comp, aeval_monomial, map_mul, map_pow, aeval_C]
    simp only [Module.End.mul_apply, Module.algebraMap_end_apply, ← smul_sub]
    exact P.smul_mem a (hpow n)

variable [CharZero K]

/-- Let `P` be a subspace stable under `e`, `f` and `h`, and suppose that `f^{N+1} = 0`. If
`e v ∈ P`, then `h (h - 1) ⋯ (h - N) v ∈ P`. -/
theorem aeval_prod_apply_mem {N : ℕ} (hN : toEnd K L M f ^ (N + 1) = 0) {v : M}
    (hv : ⁅e, v⁆ ∈ P) :
    aeval (toEnd K L M h) (∏ k ∈ Finset.range (N + 1), (X - C (k : K))) v ∈ P := by
  have hW := t.comap_e_stable hPh
  have hPf' : ∀ x ∈ P, toEnd K L M f x ∈ P := hPf
  have key : ∀ d j, j + d = N + 1 → ∀ w, ⁅e, w⁆ ∈ P → (toEnd K L M f ^ j)
      (aeval (toEnd K L M h) (∏ k ∈ Finset.Ico j (N + 1), (X - C (k : K))) w) ∈ P := by
    intro d
    induction d with
    | zero =>
      intro j hj w _
      rw [add_zero] at hj
      subst hj
      rw [hN, LinearMap.zero_apply]
      exact zero_mem P
    | succ d ih =>
      intro j hj w hw
      set u := aeval (toEnd K L M h) (∏ k ∈ Finset.Ico (j + 1) (N + 1), (X - C (k : K))) w
      have hu : ⁅e, u⁆ ∈ P := Module.End.aeval_apply_mem hW _ (x := w) hw
      have h2 := hPe _ (ih (j + 1) (by omega) w hw)
      rw [t.lie_e_pow_succ_toEnd_f] at h2
      have h3 := sub_mem h2 (Module.End.pow_apply_mem hPf' (j + 1) hu)
      rw [add_sub_cancel_left] at h3
      have h4 := P.smul_mem (j + 1 : K)⁻¹ h3
      rw [smul_smul, inv_mul_cancel₀ (Nat.cast_add_one_ne_zero j), one_smul] at h4
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : j < N + 1), map_mul, Module.End.mul_apply]
      convert h4 using 2
      simp [Nat.cast_smul_eq_nsmul]
  have := key (N + 1) 0 (by simp) v hv
  rwa [pow_zero, Module.End.one_apply, Nat.Ico_zero_eq_range] at this

end Stable

/-! ### The subspace generated by primitive vectors of weight `m` -/

section PrimitiveSpan

variable (m : K)

omit t in
/-- `fʲ w ∈ primitiveSpan m` for `w` with `e w = 0` and `h w = m w`. -/
lemma pow_apply_mem_primitiveSpan (j : ℕ) {w : M} (hwe : ⁅e, w⁆ = 0) (hwh : ⁅h, w⁆ = m • w) :
    (toEnd K L M f ^ j) w ∈ primitiveSpan K M h e f m :=
  Submodule.mem_iSup_of_mem j (Submodule.mem_map_of_mem
    ⟨LinearMap.mem_ker.mpr hwe, Module.End.mem_eigenspace_iff.mpr hwh⟩)

omit t in
/-- To check that `primitiveSpan m` is `T`-stable, it suffices to check it on the vectors `fʲ w`. -/
lemma primitiveSpan_le_comap {T : Module.End K M}
    (hT : ∀ (j : ℕ) (w : M), ⁅e, w⁆ = 0 → ⁅h, w⁆ = m • w →
      T ((toEnd K L M f ^ j) w) ∈ primitiveSpan K M h e f m) :
    ∀ x ∈ primitiveSpan K M h e f m, T x ∈ primitiveSpan K M h e f m := by
  refine fun x hx ↦ (iSup_le fun j ↦ Submodule.map_le_iff_le_comap.mpr ?_ :
    primitiveSpan K M h e f m ≤ (primitiveSpan K M h e f m).comap T) hx
  rintro w ⟨hwe, hwh⟩
  exact hT j w (LinearMap.mem_ker.mp hwe) (Module.End.mem_eigenspace_iff.mp hwh)

omit t in
/-- `primitiveSpan m` is stable under `f`. -/
lemma primitiveSpan_f : ∀ x ∈ primitiveSpan K M h e f m, ⁅f, x⁆ ∈ primitiveSpan K M h e f m :=
  primitiveSpan_le_comap m (T := toEnd K L M f) fun j w hwe hwh ↦ by
    rw [← Module.End.mul_apply, ← pow_succ']
    exact pow_apply_mem_primitiveSpan m (j + 1) hwe hwh

/-- `primitiveSpan m` is stable under `h`. -/
lemma primitiveSpan_h : ∀ x ∈ primitiveSpan K M h e f m, ⁅h, x⁆ ∈ primitiveSpan K M h e f m :=
  primitiveSpan_le_comap m (T := toEnd K L M h) fun j w hwe hwh ↦ by
    rw [toEnd_apply_apply, t.lie_h_pow_toEnd_f_of_eq hwh]
    exact Submodule.smul_mem _ _ (pow_apply_mem_primitiveSpan m j hwe hwh)

/-- `primitiveSpan m` is stable under `e`. -/
lemma primitiveSpan_e : ∀ x ∈ primitiveSpan K M h e f m, ⁅e, x⁆ ∈ primitiveSpan K M h e f m :=
  primitiveSpan_le_comap m (T := toEnd K L M e) fun j w hwe hwh ↦ by
    rw [toEnd_apply_apply]
    rcases j with _ | j
    · rw [pow_zero, Module.End.one_apply, hwe]
      exact zero_mem _
    · rw [t.lie_e_pow_succ_toEnd_f, hwe, map_zero, zero_add, hwh, ← sub_smul, map_smul,
        smul_smul]
      exact Submodule.smul_mem _ _ (pow_apply_mem_primitiveSpan m j hwe hwh)

/-- `primitiveSpan m ⊆ ⨁_{k ∈ ℤ} ker (h - k)` for `m ∈ ℕ`. -/
lemma primitiveSpan_le_iSup_eigenspace (m : ℕ) :
    primitiveSpan K M h e f (m : K) ≤ ⨆ k : ℤ, (toEnd K L M h).eigenspace (k : K) := by
  refine iSup_le fun j ↦ Submodule.map_le_iff_le_comap.mpr ?_
  rintro w ⟨hwe, hwh⟩
  refine Submodule.mem_iSup_of_mem ((m : ℤ) - 2 * j) (Module.End.mem_eigenspace_iff.mpr ?_)
  rw [toEnd_apply_apply, t.lie_h_pow_toEnd_f_of_eq (Module.End.mem_eigenspace_iff.mp hwh)]
  push_cast
  rfl

/-- If `f^{N+1} = 0`, then `∏_{j ≤ N} (h - (m - 2j))` vanishes on `primitiveSpan m`. -/
lemma aeval_prod_apply_eq_zero_of_mem_primitiveSpan {N : ℕ}
    (hN : toEnd K L M f ^ (N + 1) = 0) {x : M} (hx : x ∈ primitiveSpan K M h e f m) :
    aeval (toEnd K L M h) (∏ j ∈ Finset.range (N + 1), (X - C (m - 2 * (j : K)))) x = 0 := by
  refine LinearMap.mem_ker.mp ((iSup_le fun j ↦ Submodule.map_le_iff_le_comap.mpr ?_ :
    primitiveSpan K M h e f m ≤ (LinearMap.ker _).comap (LinearMap.id)) hx)
  rintro w ⟨hwe, hwh⟩
  simp only [Submodule.mem_comap, LinearMap.id_apply, LinearMap.mem_ker]
  by_cases hj : j ≤ N
  · rw [Module.End.aeval_apply_of_mem_apply_eq_smul (by
      rw [toEnd_apply_apply]
      exact t.lie_h_pow_toEnd_f_of_eq (Module.End.mem_eigenspace_iff.mp hwh) j),
      eval_prod, Finset.prod_eq_zero (i := j) (Finset.mem_range.mpr (by omega)) (by simp),
      zero_smul]
  · rw [show j = (j - (N + 1)) + (N + 1) by omega, pow_add, hN, mul_zero, LinearMap.zero_apply,
      map_zero]

end PrimitiveSpan

variable [CharZero K]

/-- If `f^{N+1} = 0` and `e^d v = 0`, then `q(Ω)^d v = 0`, where `Ω` is the Casimir operator and
`q = ∏_{k ≤ N} (X - k(k + 2))`. -/
theorem aeval_casimir_pow_apply_eq_zero {N : ℕ} (hN : toEnd K L M f ^ (N + 1) = 0) (d : ℕ)
    {v : M} (hv : (toEnd K L M e ^ d) v = 0) :
    (aeval (casimir K M h e f) (∏ k ∈ Finset.range (N + 1), (X - C ((k : K) * (k + 2)))) ^ d)
      v = 0 := by
  set Q := aeval (casimir K M h e f) (∏ k ∈ Finset.range (N + 1), (X - C ((k : K) * (k + 2))))
  induction d generalizing v with
  | zero => simpa using hv
  | succ d ih =>
    have hQe : Commute Q (toEnd K L M e) :=
      Module.End.commute_aeval_left t.commute_casimir_e _
    have hw : ⁅e, (Q ^ d) v⁆ = 0 := by
      rw [← toEnd_apply_apply (R := K), ← Module.End.mul_apply, ((hQe.pow_left d).eq).symm,
        Module.End.mul_apply, toEnd_apply_apply]
      exact ih (by rwa [pow_succ, Module.End.mul_apply] at hv)
    have hw' : ⁅e, (Q ^ d) v⁆ ∈ (⊥ : Submodule K M) := by rw [hw]; exact zero_mem _
    have hb : ∀ x : L, ∀ y ∈ (⊥ : Submodule K M), ⁅x, y⁆ ∈ (⊥ : Submodule K M) := by simp
    have h1 := t.aeval_casimir_sub_mem (hb e) (hb f) (hb h) hw'
      (∏ k ∈ Finset.range (N + 1), (X - C ((k : K) * (k + 2))))
    have h2 := t.aeval_prod_apply_mem (hb e) (hb f) (hb h) hN hw'
    rw [Submodule.mem_bot, sub_eq_zero] at h1
    rw [Submodule.mem_bot] at h2
    rw [pow_succ', Module.End.mul_apply, h1, prod_comp_eq, mul_comm, map_mul,
      Module.End.mul_apply, h2, map_zero]


/-- The key step: let `f^{N+1} = 0`, `m ∈ ℕ`, and let `v` be killed by a power of `e` and by a
power of `Ω - m(m + 2)`, where `Ω` is the Casimir operator. Then `v ∈ ∑ⱼ fʲ (ker e ∩ ker (h - m))`.

Proof, by induction on the least `d` with `eᵈ v = 0`: let `P = ∑ⱼ fʲ (ker e ∩ ker (h - m))`.
By induction `e v ∈ P`. Modulo `P`, `v` is killed by `∏_{k ≤ N} (h - k)` (`aeval_prod_apply_mem`)
and by `((h - m)(h + m + 2))ʳ` (as `Ω ≡ h² + 2h`), hence by `h - m`. As `h` acts on
`fʲ (ker e ∩ ker (h - m))` by `m - 2j`, a suitable polynomial `s` in `h` gives
`v' = s(h) v / s(m) ≡ v` with `(h - m)² v' = 0`; then `e v' ∈ P` has generalized weight `m + 2`,
which does not occur in `P`, so `e v' = 0`, and then `h v' = m v'`, so `v' ∈ P`. -/
theorem mem_primitiveSpan {N : ℕ} (hN : toEnd K L M f ^ (N + 1) = 0) (m r d : ℕ) {v : M}
    (hd : (toEnd K L M e ^ d) v = 0)
    (hv : aeval (casimir K M h e f) ((X - C ((m : K) * (m + 2))) ^ r) v = 0) :
    v ∈ primitiveSpan K M h e f (m : K) := by
  induction d generalizing v with
  | zero => rw [pow_zero, Module.End.one_apply] at hd; rw [hd]; exact zero_mem _
  | succ d ih =>
  set P := primitiveSpan K M h e f (m : K)
  have hPe := t.primitiveSpan_e (M := M) (m : K)
  have hPf := primitiveSpan_f (K := K) (M := M) (h := h) (e := e) (f := f) (m : K)
  have hPh := t.primitiveSpan_h (M := M) (m : K)
  have hEv : ⁅e, v⁆ ∈ P := by
    refine ih (by rwa [pow_succ, Module.End.mul_apply] at hd) ?_
    have hc := Module.End.commute_aeval_left (t.commute_casimir_e (K := K) (M := M))
      ((X - C ((m : K) * (m + 2))) ^ r)
    rw [← toEnd_apply_apply (R := K), ← Module.End.mul_apply, hc.eq, Module.End.mul_apply,
      hv, map_zero]
  set T := toEnd K L M h
  have hTP : ∀ x ∈ P, T x ∈ P := hPh
  -- `v` is killed modulo `P` by `h - m`
  have hp := t.aeval_prod_apply_mem hPe hPf hPh hN hEv
  have hg : aeval T ((X - C (m : K)) ^ r * (X + C ((m : K) + 2)) ^ r) v ∈ P := by
    have := t.aeval_casimir_sub_mem hPe hPf hPh hEv ((X - C ((m : K) * (m + 2))) ^ r)
    rwa [hv, zero_sub, neg_mem_iff, pow_comp_eq] at this
  have hcopw : IsCoprime (∏ k ∈ (Finset.range (N + 1)).erase m, (X - C (k : K)))
      ((X + C ((m : K) + 2)) ^ r) := by
    refine IsCoprime.pow_right (IsCoprime.prod_left fun k _ ↦ ?_)
    rw [show X + C ((m : K) + 2) = X - C (-((m : K) + 2)) by rw [map_neg, sub_neg_eq_add]]
    refine isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr fun hk ↦ ?_).isUnit
    have : ((k + m + 2 : ℕ) : K) = 0 := by push_cast; linear_combination hk
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)
  have hm : aeval T (X - C (m : K)) v ∈ P := Module.End.aeval_X_sub_C_apply_mem hTP hcopw hp hg
  -- the polynomial `s = ∏_{1 ≤ j ≤ N} (X - (m - 2j))`
  set s := ∏ j ∈ Finset.range N, (X - C ((m : K) - 2 * ((j + 1 : ℕ) : K)))
  have hprod : (X - C (m : K)) * s =
      ∏ j ∈ Finset.range (N + 1), (X - C ((m : K) - 2 * (j : K))) := by
    rw [Finset.prod_range_succ', mul_comm]
    congr 1
    simp
  have hkill : ∀ x ∈ P, aeval T ((X - C (m : K)) * s) x = 0 := fun x hx ↦ by
    rw [hprod]; exact t.aeval_prod_apply_eq_zero_of_mem_primitiveSpan (m : K) hN hx
  have hs0 : s.eval (m : K) ≠ 0 := by
    rw [eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun j _ ↦ ?_
    simp only [eval_sub, eval_X, eval_C, sub_sub_cancel]
    exact mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))
  set v' := (s.eval (m : K))⁻¹ • aeval T s v
  have hvv' : v - v' ∈ P := by
    obtain ⟨z, hz⟩ := X_sub_C_dvd_sub_C_eval (p := s) (a := (m : K))
    have h1 : aeval T (s - C (s.eval (m : K))) v ∈ P := by
      rw [hz, mul_comm, map_mul, Module.End.mul_apply]
      exact Module.End.aeval_apply_mem hTP z hm
    rw [map_sub, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply] at h1
    have h2 := P.smul_mem (-(s.eval (m : K))⁻¹) h1
    have e : v - v' = (-(s.eval (m : K))⁻¹) • (aeval T s v - s.eval (m : K) • v) := by
      simp only [v', smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hs0, neg_smul, one_smul]
      abel
    rw [e]
    exact h2
  have hv'2 : aeval T ((X - C (m : K)) ^ 2) v' = 0 := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul,
      show (X - C (m : K)) ^ 2 * s = ((X - C (m : K)) * s) * (X - C (m : K)) by ring, map_mul,
      Module.End.mul_apply, hkill _ hm, smul_zero]
  -- `e v' = 0`
  have hEv'P : ⁅e, v'⁆ ∈ P := by
    have := sub_mem hEv (hPe _ hvv')
    rwa [lie_sub, sub_sub_cancel] at this
  have hshift : ∀ (a : K) (x : M), aeval T (X - C (a + 2)) ⁅e, x⁆ = ⁅e, aeval T (X - C a) x⁆ := by
    intro a x
    simp only [T, map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply,
      toEnd_apply_apply, lie_sub, lie_smul, t.lie_e_lie_h (K := K)]
    module
  have hEv'2 : aeval T ((X - C ((m : K) + 2)) ^ 2) ⁅e, v'⁆ = 0 := by
    rw [sq, map_mul, Module.End.mul_apply, hshift, hshift, ← Module.End.mul_apply, ← map_mul,
      ← sq, hv'2, lie_zero]
  have hEv'0 : ⁅e, v'⁆ = 0 := by
    have hcop : IsCoprime ((X - C (m : K)) * s) ((X - C ((m : K) + 2)) ^ 2) := by
      refine IsCoprime.pow_right (IsCoprime.mul_left ?_ (IsCoprime.prod_left fun j _ ↦ ?_))
      · refine isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr fun h2 ↦ ?_).isUnit
        have : (2 : K) = 0 := by linear_combination -h2
        exact two_ne_zero this
      · refine isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr fun h2 ↦ ?_).isUnit
        have : ((2 * j + 4 : ℕ) : K) = 0 := by push_cast at h2 ⊢; linear_combination -h2
        exact absurd (Nat.cast_eq_zero.mp this) (by omega)
    exact (Submodule.disjoint_def.mp (Polynomial.disjoint_ker_aeval_of_isCoprime T hcop)) _
      (LinearMap.mem_ker.mpr (hkill _ hEv'P)) (LinearMap.mem_ker.mpr hEv'2)
  -- `h v' = m v'`
  have hb : ∀ x : L, ∀ y ∈ (⊥ : Submodule K M), ⁅x, y⁆ ∈ (⊥ : Submodule K M) := by simp
  have hp' := t.aeval_prod_apply_mem (hb e) (hb f) (hb h) hN
    (by rw [hEv'0]; exact zero_mem (⊥ : Submodule K M))
  have hm' : aeval T (X - C (m : K)) v' ∈ (⊥ : Submodule K M) :=
    Module.End.aeval_X_sub_C_apply_mem (fun x hx ↦ by simp_all) (w := 1) (r := 2)
      isCoprime_one_right hp' (by rw [mul_one, hv'2]; exact zero_mem _)
  have hv'P : v' ∈ P := by
    have := pow_apply_mem_primitiveSpan (K := K) (M := M) (h := h) (e := e) (f := f) (m : K) 0
      hEv'0 (by
        rw [Submodule.mem_bot, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
          Module.algebraMap_end_apply, sub_eq_zero] at hm'
        exact hm')
    rwa [pow_zero, Module.End.one_apply] at this
  have := add_mem hvv' hv'P
  rwa [sub_add_cancel] at this

variable [FiniteDimensional K M]

/-- In a finite-dimensional module over a field of characteristic zero, `e` acts nilpotently.

Proof: the ranges of the powers of `e` stabilize at some `R = range eⁿ`, on which `e` acts
bijectively; `R` is stable under `h`, and there `h = e h e⁻¹ + 2`, so taking traces
`2 dim R = 0`. -/
theorem isNilpotent_toEnd_e : IsNilpotent (toEnd K L M e) := by
  set E := toEnd K L M e
  set H := toEnd K L M h
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes E.iterateRange
  have hR : LinearMap.range (E ^ (n + 1)) = LinearMap.range (E ^ n) := (hn (n + 1) (by omega)).symm
  set R := LinearMap.range (E ^ n)
  have hER : ∀ x ∈ R, E x ∈ R := by
    rintro _ ⟨y, rfl⟩
    rw [← hR]
    exact ⟨y, by rw [pow_succ', Module.End.mul_apply]⟩
  have hHR : ∀ x ∈ R, H x ∈ R := by
    rintro _ ⟨y, rfl⟩
    rw [← Module.End.mul_apply, t.toEnd_h_mul_e_pow, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply]
    exact add_mem ⟨_, rfl⟩ (Submodule.smul_mem _ _ ⟨_, rfl⟩)
  let E' := E.restrict hER
  let H' := H.restrict hHR
  have hsurj : Function.Surjective E' := by
    rintro ⟨x, hx⟩
    rw [← hR] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨(E ^ n) y, ⟨y, rfl⟩⟩, Subtype.ext (by
      simp [E', LinearMap.restrict_apply, pow_succ', Module.End.mul_apply])⟩
  have hunit : IsUnit E' := (LinearMap.isUnit_iff_range_eq_top E').mpr
    (LinearMap.range_eq_top.mpr hsurj)
  obtain ⟨u, hu⟩ := hunit
  have hrel : H' * E' = E' * H' + (2 : K) • E' := by
    ext x
    simp only [H', E', Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.restrict_apply, Submodule.coe_add, Submodule.coe_smul]
    rw [← Module.End.mul_apply, t.toEnd_h_mul_e]
    rfl
  have hH : H' = E' * (H' * ↑u⁻¹) + (2 : K) • 1 := by
    have := congrArg (· * (↑u⁻¹ : Module.End K R)) hrel
    simp only [add_mul, mul_assoc, smul_mul_assoc] at this
    rw [← hu, u.mul_inv, mul_one] at this
    rw [← hu]; exact this
  have htr := congrArg (LinearMap.trace K R) hH
  rw [map_add, LinearMap.trace_mul_comm, mul_assoc, ← hu, u.inv_mul, mul_one, map_smul,
    LinearMap.trace_one, left_eq_add, smul_eq_mul, mul_eq_zero] at htr
  have h0 : finrank K R = 0 := by exact_mod_cast htr.resolve_left two_ne_zero
  refine ⟨n, LinearMap.range_eq_bot.mp ?_⟩
  exact Submodule.finrank_eq_zero.mp h0

/-- In a finite-dimensional module over a field of characteristic zero, `f` acts nilpotently. -/
theorem isNilpotent_toEnd_f : IsNilpotent (toEnd K L M f) :=
  t.symm.isNilpotent_toEnd_e

/-- In a finite-dimensional module over a field of characteristic zero, `h` acts diagonalizably
with integer eigenvalues.

This is a standard consequence of Weyl's theorem and the classification of irreducible
`𝔰𝔩₂`-modules ([Hum] §7.2); we give a direct argument instead. By nilpotency of `e` and `f`
(`isNilpotent_toEnd_e`), the Casimir operator `Ω` satisfies `∏_{m ≤ N} (Ω - m(m + 2))ⁿ = 0`
(`aeval_casimir_pow_apply_eq_zero`), so `M` is the sum of the generalized eigenspaces of `Ω`.
Each of these lies in the sum of `f`-strings through primitive vectors of some weight `m ∈ ℕ`
(`mem_primitiveSpan`), on which `h` acts diagonally with eigenvalues `m - 2j`. -/
theorem iSup_eigenspace_toEnd_h_eq_top :
    ⨆ k : ℤ, (toEnd K L M h).eigenspace (k : K) = ⊤ := by
  obtain ⟨n, hn⟩ := t.isNilpotent_toEnd_e (K := K) (M := M)
  obtain ⟨N, hN'⟩ := t.symm.isNilpotent_toEnd_e (K := K) (M := M)
  have hN : toEnd K L M f ^ (N + 1) = 0 := by rw [pow_succ, hN', zero_mul]
  set c : ℕ → K := fun m ↦ (m : K) * (m + 2)
  have hQ : aeval (casimir K M h e f) (∏ m ∈ Finset.range (N + 1), (X - C (c m)) ^ n) = 0 := by
    rw [Finset.prod_pow, map_pow]
    ext v
    exact t.aeval_casimir_pow_apply_eq_zero hN n (by rw [hn, LinearMap.zero_apply])
  have hcop : ∀ i ∈ Finset.range (N + 1), ∀ j ∈ Finset.range (N + 1), i ≠ j →
      IsCoprime ((X - C (c i)) ^ n) ((X - C (c j)) ^ n) := by
    intro i _ j _ hij
    refine (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr fun hc ↦ hij ?_).isUnit).pow
    have : ((i * (i + 2) : ℕ) : K) = ((j * (j + 2) : ℕ) : K) := by push_cast; exact hc
    have hij' := Nat.cast_injective this
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij' (Nat.mul_lt_mul'' h (by omega)).ne
    · exact h
    · exact absurd hij' (Nat.mul_lt_mul'' h (by omega)).ne'
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ LinearMap.ker (aeval (casimir K M h e f)
      (∏ m ∈ Finset.range (N + 1), (X - C (c m)) ^ n)) := by
    rw [hQ, LinearMap.ker_zero]; trivial
  refine (iSup₂_le fun m _ ↦ ?_ : _ ≤ ⨆ k : ℤ, (toEnd K L M h).eigenspace (k : K))
    (Module.End.ker_aeval_prod_le_iSup _ _ _ hcop hv)
  intro x hx
  exact t.primitiveSpan_le_iSup_eigenspace m
    (t.mem_primitiveSpan hN m n n (by rw [hn, LinearMap.zero_apply]) hx)

end IsSl2Triple
