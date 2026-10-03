/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic.NoncommRing

/-!
# The Poincaré–Birkhoff–Witt theorem

Let `L` be a Lie algebra over a commutative ring `R` which is free as an `R`-module, with a basis
`b : Basis σ R L` indexed by a linearly ordered type `σ`. For `s : σ →₀ ℕ` let
`pbwMonomial R b s` be the ordered product `b i₁ ⋯ b iₖ` in `U(L)`, where `i₁ ≤ ⋯ ≤ iₖ` are the
elements of the multiset `s` in increasing order. The Poincaré–Birkhoff–Witt theorem states that
these ordered monomials form an `R`-basis of `U(L)`.

## Main definitions

* `UniversalEnvelopingAlgebra.pbwMonomial`: the ordered monomial attached to `s : σ →₀ ℕ`.
* `UniversalEnvelopingAlgebra.pbwEquiv`: the `R`-linear isomorphism `U(L) ≃ₗ[R] R[X_i : i ∈ σ]`
  sending `pbwMonomial R b s` to the monomial `X^s`.
* `UniversalEnvelopingAlgebra.pbwBasis`: the PBW basis of `U(L)`.

## Main results

* `UniversalEnvelopingAlgebra.pbwBasis_apply`: the PBW basis consists of the ordered monomials.
* `UniversalEnvelopingAlgebra.ι_injective`: if `L` is free as an `R`-module then
  `ι : L → U(L)` is injective.

## Proof

We follow Humphreys, *Introduction to Lie algebras and representation theory*, §17.4
(Lemmas A–C; the Notes to §17 say the treatment follows Bourbaki). Humphreys writes `i` for the
canonical map `L → U(L)` and `Ω` for the index set of the basis; here they are `ι` and `σ`.
Let `S = R[z_i : i ∈ σ]`
be the polynomial ring.
We construct a representation `ρ` of `L` on `S` such that, writing `X_i = ρ (b i)`,

* (A) `X_i z^s = z_i z^s` whenever `i ≤ j` for every `j` occurring in `s`;
* (B) `X_i z^s - z_i z^s` has total degree at most `|s|`;
* (C) `X_i X_j - X_j X_i = ρ ⁅b i, b j⁆`.

The operators `X_i` are defined on monomials by recursion on the degree: if `i ≤ s` then
`X_i z^s = z_i z^s`; otherwise write `z^s = z_j z^t` with `j` the least index in `s` (so `j < i`)
and set `X_i z^s = X_j (X_i z^t - z_i z^t) + z_i z^s + ρ ⁅b i, b j⁆ z^t`, as forced by (A) and (C).
Property (C) is then proved by induction on the degree, using the Jacobi identity.

The representation `ρ` extends to `U(L)`, and `u ↦ ρ(u) 1` sends `pbwMonomial R b s` to `z^s`
(by (A)), giving linear independence. For spanning we show that the linear map
`φ : S → U(L)`, `z^s ↦ pbwMonomial R b s`, satisfies `φ (ρ x p) = ι x * φ p`; it follows that
`u ↦ ρ(u) 1` and `φ` are mutually inverse.

## References

* J. E. Humphreys, *Introduction to Lie algebras and representation theory*, GTM 9, §17.3–17.4.
* N. Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.7.
-/

open MvPolynomial Finsupp Module

noncomputable section

namespace UniversalEnvelopingAlgebra

variable (R : Type*) {L σ : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder σ]

/-- The ordered monomial `v i₁ * ⋯ * v iₖ` in the universal enveloping algebra, where
`i₁ ≤ ⋯ ≤ iₖ` enumerates the multiset `s` in increasing order. -/
def pbwMonomial (v : σ → L) (s : σ →₀ ℕ) : UniversalEnvelopingAlgebra R L :=
  (((toMultiset s).sort (· ≤ ·)).map fun i ↦ ι R (v i)).prod

variable {R}

namespace PBW

/-- The index `i` is at most every index occurring in `s`. -/
def LeAll (i : σ) (s : σ →₀ ℕ) : Prop := ∀ j ∈ s.support, i ≤ j

instance (i : σ) (s : σ →₀ ℕ) : Decidable (LeAll i s) :=
  inferInstanceAs (Decidable (∀ j ∈ s.support, i ≤ j))

open Classical in
@[simp] lemma pbwMonomial_zero (v : σ → L) : pbwMonomial R v 0 = 1 := by
  simp [pbwMonomial]

lemma pbwMonomial_add_single {v : σ → L} {i : σ} {s : σ →₀ ℕ} (h : LeAll i s) :
    pbwMonomial R v (s + single i 1) = ι R (v i) * pbwMonomial R v s := by
  have hs : toMultiset (s + single i 1) = i ::ₘ toMultiset s := by
    rw [toMultiset_add, toMultiset_single, one_nsmul, add_comm, Multiset.singleton_add]
  rw [pbwMonomial, hs, Multiset.sort_cons, List.map_cons, List.prod_cons, pbwMonomial]
  intro j hj
  exact h j (by simpa using hj)

lemma leAll_zero (i : σ) : LeAll i 0 := by simp [LeAll]

lemma support_nonempty_of_not_leAll {i : σ} {s : σ →₀ ℕ} (h : ¬ LeAll i s) :
    s.support.Nonempty := by
  by_contra h'
  rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at h'
  exact h (h' ▸ leAll_zero i)

/-- The least index occurring in `s` (junk if `s = 0`). -/
def minIdx (s : σ →₀ ℕ) (h : s.support.Nonempty) : σ := s.support.min' h

lemma minIdx_lt {i : σ} {s : σ →₀ ℕ} (h : ¬ LeAll i s) :
    minIdx s (support_nonempty_of_not_leAll h) < i := by
  simp only [LeAll, not_forall, not_le] at h
  obtain ⟨j, hj, hji⟩ := h
  exact lt_of_le_of_lt (Finset.min'_le _ _ hj) hji

lemma single_minIdx_le (s : σ →₀ ℕ) (h : s.support.Nonempty) :
    single (minIdx s h) 1 ≤ s := by
  intro k
  by_cases hk : k = minIdx s h
  · subst hk
    have := Finset.min'_mem s.support h
    rw [Finsupp.mem_support_iff] at this
    simp only [single_eq_same]
    exact Nat.one_le_iff_ne_zero.mpr this
  · simp [Ne.symm hk]

lemma sub_add_single_minIdx (s : σ →₀ ℕ) (h : s.support.Nonempty) :
    s - single (minIdx s h) 1 + single (minIdx s h) 1 = s :=
  tsub_add_cancel_of_le (single_minIdx_le s h)

lemma leAll_minIdx (s : σ →₀ ℕ) (h : s.support.Nonempty) :
    LeAll (minIdx s h) (s - single (minIdx s h) 1) := by
  intro j hj
  apply Finset.min'_le
  rw [Finsupp.mem_support_iff] at hj ⊢
  intro h0
  apply hj
  simp [h0]

lemma degree_sub_single_minIdx (s : σ →₀ ℕ) (h : s.support.Nonempty) :
    (s - single (minIdx s h) 1).degree + 1 = s.degree := by
  conv_rhs => rw [← sub_add_single_minIdx s h]
  rw [map_add, degree_single]

lemma leAll_add_single {i j : σ} {s : σ →₀ ℕ} (h : LeAll i s) (hij : i ≤ j) :
    LeAll i (s + single j 1) := by
  intro k hk
  rcases Finset.mem_union.mp (support_add hk) with hk | hk
  · exact h k hk
  · rw [support_single _ one_ne_zero, Finset.mem_singleton] at hk
    exact hk ▸ hij

lemma leAll_of_le {i j : σ} {s : σ →₀ ℕ} (h : LeAll j s) (hij : i ≤ j) : LeAll i s :=
  fun k hk ↦ hij.trans (h k hk)

/-- If `j ≤ s` and `j < i`, then the least index of `s + single j 1` is `j`. -/
lemma minIdx_add_single {j : σ} {t : σ →₀ ℕ} (h : LeAll j t)
    (hne : (t + single j 1).support.Nonempty) :
    minIdx (t + single j 1) hne = j := by
  apply le_antisymm
  · apply Finset.min'_le
    rw [Finsupp.mem_support_iff]
    simp
  · apply Finset.le_min'
    intro k hk
    rcases Finset.mem_union.mp (support_add hk) with hk | hk
    · exact h k hk
    · rw [support_single _ one_ne_zero, Finset.mem_singleton] at hk
      exact hk ▸ le_rfl

lemma not_leAll_add_single {i j : σ} {t : σ →₀ ℕ} (hji : j < i) :
    ¬ LeAll i (t + single j 1) := by
  intro h
  have : j ∈ (t + single j 1).support := by rw [Finsupp.mem_support_iff]; simp
  exact absurd (h j this) (not_le.mpr hji)

variable (R σ) in
/-- The monomial `z^s`. -/
abbrev z (s : σ →₀ ℕ) : MvPolynomial σ R := monomial s 1

/-- The linear extension of a function on monomials. -/
def extend {M : Type*} [AddCommGroup M] [Module R M] (f : (σ →₀ ℕ) → M) :
    MvPolynomial σ R →ₗ[R] M :=
  (basisMonomials σ R).constr R f

omit [LinearOrder σ] in
@[simp] lemma extend_z {M : Type*} [AddCommGroup M] [Module R M] (f : (σ →₀ ℕ) → M)
    (s : σ →₀ ℕ) : extend f (z R σ s) = f s := by
  have := (basisMonomials σ R).constr_basis R f s
  rwa [coe_basisMonomials] at this

omit [LinearOrder σ] in
/-- Two linear maps out of `R[X]` agreeing on monomials of degree `≤ n` agree on polynomials of
total degree `≤ n`. -/
lemma eq_of_mem_restrictTotalDegree {M : Type*} [AddCommGroup M] [Module R M]
    {f g : MvPolynomial σ R →ₗ[R] M} {n : ℕ}
    (h : ∀ s : σ →₀ ℕ, s.degree ≤ n → f (z R σ s) = g (z R σ s))
    {p : MvPolynomial σ R} (hp : p ∈ restrictTotalDegree σ R n) : f p = g p := by
  rw [p.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hdeg : s.degree ≤ n :=
    (le_totalDegree hs).trans ((mem_restrictTotalDegree σ n p).mp hp)
  rw [← mul_one (p.coeff s), ← smul_eq_mul, ← smul_monomial, map_smul, map_smul, h s hdeg]

omit [LinearOrder σ] in
lemma z_mem_restrictTotalDegree {s : σ →₀ ℕ} {n : ℕ} (h : s.degree ≤ n) :
    z R σ s ∈ restrictTotalDegree σ R n := by
  rw [mem_restrictTotalDegree]
  exact (totalDegree_monomial_le s 1).trans h

omit [LinearOrder σ] in
lemma restrictTotalDegree_mono {m n : ℕ} (h : m ≤ n) :
    restrictTotalDegree σ R m ≤ restrictTotalDegree σ R n := by
  intro p hp
  rw [mem_restrictTotalDegree] at hp ⊢
  exact hp.trans h

variable (b : Basis σ R L)

/-- Auxiliary operators on monomials; `actAux b n i s` is the correct value of `X_i z^s` when
`s` has degree `≤ n`. -/
def actAux : ℕ → σ → (σ →₀ ℕ) → MvPolynomial σ R
  | 0, i, s => z R σ (s + single i 1)
  | n + 1, i, s =>
    if h : LeAll i s then z R σ (s + single i 1) else
      let h' := support_nonempty_of_not_leAll h
      let j := minIdx s h'
      let t := s - single j 1
      let op : L →ₗ[R] Module.End R (MvPolynomial σ R) :=
        b.constr R fun k ↦ extend (actAux n k)
      op (b j) (op (b i) (z R σ t) - z R σ (t + single i 1)) + z R σ (s + single i 1) +
        op ⁅b i, b j⁆ (z R σ t)

/-- The operators built from `actAux b n`. -/
def opAux (n : ℕ) : L →ₗ[R] Module.End R (MvPolynomial σ R) :=
  b.constr R fun k ↦ extend (actAux b n k)

lemma actAux_succ (n : ℕ) (i : σ) (s : σ →₀ ℕ) :
    actAux b (n + 1) i s =
      if h : LeAll i s then z R σ (s + single i 1) else
        opAux b n (b (minIdx s (support_nonempty_of_not_leAll h)))
          (opAux b n (b i) (z R σ (s - single (minIdx s (support_nonempty_of_not_leAll h)) 1)) -
            z R σ (s - single (minIdx s (support_nonempty_of_not_leAll h)) 1 + single i 1)) +
          z R σ (s + single i 1) +
          opAux b n ⁅b i, b (minIdx s (support_nonempty_of_not_leAll h))⁆
            (z R σ (s - single (minIdx s (support_nonempty_of_not_leAll h)) 1)) := by
  rw [actAux]; rfl

/-- The representation `ρ` of `L` on `R[X_i : i ∈ σ]` used in the proof of PBW. -/
def rho : L →ₗ[R] Module.End R (MvPolynomial σ R) :=
  b.constr R fun i ↦ extend fun s ↦ actAux b s.degree i s

lemma rho_basis_z (i : σ) (s : σ →₀ ℕ) : rho b (b i) (z R σ s) = actAux b s.degree i s := by
  simp [rho]

omit [LinearOrder σ] in
lemma constr_apply_apply_eq {F G : σ → Module.End R (MvPolynomial σ R)}
    {p : MvPolynomial σ R} (h : ∀ k, F k p = G k p) (x : L) :
    b.constr R F x p = b.constr R G x p := by
  simp only [Basis.constr_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, h]

/-- Joint induction: stability of `actAux` in the fuel parameter, and property (B). -/
lemma actAux_spec (m : ℕ) : ∀ s : σ →₀ ℕ, s.degree = m → ∀ i : σ,
    (∀ n, m ≤ n → actAux b n i s = rho b (b i) (z R σ s)) ∧
      rho b (b i) (z R σ s) - z R σ (s + single i 1) ∈ restrictTotalDegree σ R m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro s hs i
  -- consequences of the induction hypothesis
  have hop : ∀ k, k < m → ∀ n, k ≤ n → ∀ x : L, ∀ p ∈ restrictTotalDegree σ R k,
      opAux b n x p = rho b x p := by
    intro k hk n hkn x p hp
    refine constr_apply_apply_eq b (fun l ↦ ?_) x
    refine eq_of_mem_restrictTotalDegree (fun u hu ↦ ?_) hp
    rw [extend_z, extend_z]
    rw [(ih u.degree (lt_of_le_of_lt hu hk) u rfl l).1 n (hu.trans hkn), rho_basis_z]
  have hmem : ∀ k, k < m → ∀ x : L, ∀ p ∈ restrictTotalDegree σ R k,
      rho b x p ∈ restrictTotalDegree σ R (k + 1) := by
    intro k hk x p hp
    have : ∀ l, ∀ u : σ →₀ ℕ, u.degree ≤ k →
        rho b (b l) (z R σ u) ∈ restrictTotalDegree σ R (k + 1) := by
      intro l u hu
      have h1 := (ih u.degree (lt_of_le_of_lt hu hk) u rfl l).2
      have h2 : z R σ (u + single l 1) ∈ restrictTotalDegree σ R (k + 1) :=
        z_mem_restrictTotalDegree (by rw [map_add, degree_single]; omega)
      have := add_mem (restrictTotalDegree_mono (by omega) h1) h2
      rwa [sub_add_cancel] at this
    rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun l _ ↦ ?_
    rw [map_smul, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun u hu ↦ ?_
    rw [← mul_one (p.coeff u), ← smul_eq_mul, ← smul_monomial, map_smul]
    exact Submodule.smul_mem _ _
      (this l u ((le_totalDegree hu).trans ((mem_restrictTotalDegree σ k p).mp hp)))
  by_cases hle : LeAll i s
  · have hval : ∀ n, actAux b n i s = z R σ (s + single i 1) := by
      intro n; cases n with
      | zero => rfl
      | succ n => rw [actAux_succ, dite_eq_left hle]
    refine ⟨fun n _ ↦ ?_, ?_⟩
    · rw [rho_basis_z, hval, hval]
    · rw [rho_basis_z, hval, sub_self]; exact Submodule.zero_mem _
  · have hne := support_nonempty_of_not_leAll hle
    set j := minIdx s hne
    set t := s - single j 1
    have htdeg : t.degree + 1 = m := hs ▸ degree_sub_single_minIdx s hne
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨t.degree, htdeg.symm⟩
    have htk : t.degree = k := by omega
    have ht := ih k (by omega) t htk i
    have hzt : z R σ t ∈ restrictTotalDegree σ R k := z_mem_restrictTotalDegree htk.le
    -- the value of `actAux b (n + 1) i s` for `k ≤ n`
    have hval : ∀ n, k ≤ n → actAux b (n + 1) i s =
        rho b (b j) (rho b (b i) (z R σ t) - z R σ (t + single i 1)) + z R σ (s + single i 1) +
          rho b ⁅b i, b j⁆ (z R σ t) := by
      intro n hn
      rw [actAux_succ, dite_eq_right hle]
      change opAux b n (b j) (opAux b n (b i) (z R σ t) - z R σ (t + single i 1)) +
        z R σ (s + single i 1) + opAux b n ⁅b i, b j⁆ (z R σ t) = _
      rw [hop k (by omega) n hn _ _ hzt, hop k (by omega) n hn _ _ ht.2,
        hop k (by omega) n hn _ _ hzt]
    have hrho : rho b (b i) (z R σ s) = rho b (b j) (rho b (b i) (z R σ t) -
        z R σ (t + single i 1)) + z R σ (s + single i 1) + rho b ⁅b i, b j⁆ (z R σ t) := by
      rw [rho_basis_z, hs, hval k le_rfl]
    refine ⟨fun n hn ↦ ?_, ?_⟩
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [hval n (by omega), hrho]
    · have := add_mem (hmem k (by omega) (b j) _ ht.2) (hmem k (by omega) ⁅b i, b j⁆ _ hzt)
      rw [hrho, show ∀ a c d : MvPolynomial σ R, a + c + d - c = a + d from fun a c d ↦ by abel]
      exact this

/-- Property (A). -/
lemma rho_of_leAll {i : σ} {s : σ →₀ ℕ} (h : LeAll i s) :
    rho b (b i) (z R σ s) = z R σ (s + single i 1) := by
  rw [rho_basis_z]
  cases hs : s.degree with
  | zero => rfl
  | succ n => rw [actAux_succ, dite_eq_left h]

/-- Property (B). -/
lemma rho_sub_mem (i : σ) (s : σ →₀ ℕ) :
    rho b (b i) (z R σ s) - z R σ (s + single i 1) ∈ restrictTotalDegree σ R s.degree :=
  (actAux_spec b s.degree s rfl i).2

/-- `ρ x` raises the total degree by at most one. -/
lemma rho_mem (k : ℕ) (x : L) {p : MvPolynomial σ R} (hp : p ∈ restrictTotalDegree σ R k) :
    rho b x p ∈ restrictTotalDegree σ R (k + 1) := by
  have : ∀ l, ∀ u : σ →₀ ℕ, u.degree ≤ k →
      rho b (b l) (z R σ u) ∈ restrictTotalDegree σ R (k + 1) := by
    intro l u hu
    have h2 : z R σ (u + single l 1) ∈ restrictTotalDegree σ R (k + 1) :=
      z_mem_restrictTotalDegree (by rw [map_add, degree_single]; omega)
    have := add_mem (restrictTotalDegree_mono (by omega) (rho_sub_mem b l u)) h2
    rwa [sub_add_cancel] at this
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu ↦ ?_
  rw [← mul_one (p.coeff u), ← smul_eq_mul, ← smul_monomial, map_smul]
  exact Submodule.smul_mem _ _
    (this l u ((le_totalDegree hu).trans ((mem_restrictTotalDegree σ k p).mp hp)))

/-- The defining recursion for `ρ`. -/
lemma rho_of_not_leAll {i : σ} {s : σ →₀ ℕ} (h : ¬ LeAll i s) :
    rho b (b i) (z R σ s) =
      rho b (b (minIdx s (support_nonempty_of_not_leAll h)))
          (rho b (b i) (z R σ (s - single (minIdx s (support_nonempty_of_not_leAll h)) 1)) -
            z R σ (s - single (minIdx s (support_nonempty_of_not_leAll h)) 1 + single i 1)) +
        z R σ (s + single i 1) +
        rho b ⁅b i, b (minIdx s (support_nonempty_of_not_leAll h))⁆
          (z R σ (s - single (minIdx s (support_nonempty_of_not_leAll h)) 1)) := by
  have hne := support_nonempty_of_not_leAll h
  set j := minIdx s hne
  set t := s - single j 1
  have htdeg : t.degree + 1 = s.degree := degree_sub_single_minIdx s hne
  have hzt : z R σ t ∈ restrictTotalDegree σ R t.degree := z_mem_restrictTotalDegree le_rfl
  have hop : ∀ x : L, ∀ p ∈ restrictTotalDegree σ R t.degree,
      opAux b t.degree x p = rho b x p := by
    intro x p hp
    refine constr_apply_apply_eq b (fun l ↦ ?_) x
    refine eq_of_mem_restrictTotalDegree (fun u hu ↦ ?_) hp
    rw [extend_z, extend_z, (actAux_spec b u.degree u rfl l).1 _ hu, rho_basis_z]
  rw [rho_basis_z, ← htdeg, actAux_succ, dite_eq_right h]
  change opAux b t.degree (b j) (opAux b t.degree (b i) (z R σ t) - z R σ (t + single i 1)) +
    z R σ (s + single i 1) + opAux b t.degree ⁅b i, b j⁆ (z R σ t) = _
  rw [hop _ _ hzt, hop _ _ (rho_sub_mem b i t), hop _ _ hzt]

/-- The recursion in the form used in the proof of property (C). -/
lemma rho_add_single_of_lt {i j : σ} {t : σ →₀ ℕ} (ht : LeAll j t) (hji : j < i) :
    rho b (b i) (z R σ (t + single j 1)) =
      rho b (b j) (rho b (b i) (z R σ t) - z R σ (t + single i 1)) +
        z R σ (t + single j 1 + single i 1) + rho b ⁅b i, b j⁆ (z R σ t) := by
  have h := not_leAll_add_single (t := t) hji
  rw [rho_of_not_leAll b h]
  have hj : minIdx (t + single j 1) (support_nonempty_of_not_leAll h) = j :=
    minIdx_add_single ht _
  simp only [hj, add_tsub_cancel_right]

/-- Property (C) in the base case `j ≤ t`, `j < i`. -/
lemma comm_of_leAll {i j : σ} {t : σ →₀ ℕ} (ht : LeAll j t) (hji : j < i) :
    rho b (b i) (rho b (b j) (z R σ t)) - rho b (b j) (rho b (b i) (z R σ t)) =
      rho b ⁅b i, b j⁆ (z R σ t) := by
  rw [rho_of_leAll b ht, rho_add_single_of_lt b ht hji, map_sub,
    rho_of_leAll b (leAll_add_single ht hji.le), add_right_comm t (single i 1)]
  abel

/-- Bilinear extension of the commutator identity from basis vectors. -/
lemma comm_of_basis {p : MvPolynomial σ R}
    (h : ∀ i j, rho b (b i) (rho b (b j) p) - rho b (b j) (rho b (b i) p) =
      rho b ⁅b i, b j⁆ p) (x y : L) :
    rho b x (rho b y p) - rho b y (rho b x p) = rho b ⁅x, y⁆ p := by
  let F : L →ₗ[R] L →ₗ[R] MvPolynomial σ R := LinearMap.mk₂ R
    (fun x y ↦ rho b x (rho b y p) - rho b y (rho b x p) - rho b ⁅x, y⁆ p)
    (fun x₁ x₂ y ↦ by simp only [map_add, LinearMap.add_apply, add_lie]; abel)
    (fun c x y ↦ by simp only [map_smul, LinearMap.smul_apply, smul_lie, smul_sub])
    (fun x y₁ y₂ ↦ by simp only [map_add, LinearMap.add_apply, lie_add]; abel)
    (fun c x y ↦ by simp only [map_smul, LinearMap.smul_apply, lie_smul, smul_sub])
  have : F = 0 := b.ext fun i ↦ b.ext fun j ↦ by simp [F, h i j]
  have := LinearMap.congr_fun₂ this x y
  simpa [F, sub_eq_zero] using this

/-- Property (C): `ρ` is a Lie algebra morphism. -/
lemma rho_comm (m : ℕ) : ∀ t : σ →₀ ℕ, t.degree = m → ∀ x y : L,
    rho b x (rho b y (z R σ t)) - rho b y (rho b x (z R σ t)) = rho b ⁅x, y⁆ (z R σ t) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro t htm
  -- the induction hypothesis, for polynomials of lower degree
  have ih' : ∀ k, k < m → ∀ p ∈ restrictTotalDegree σ R k, ∀ x y : L,
      rho b x (rho b y p) - rho b y (rho b x p) = rho b ⁅x, y⁆ p := by
    intro k hk p hp x y
    have := eq_of_mem_restrictTotalDegree (n := k)
      (f := (rho b x).comp (rho b y) - (rho b y).comp (rho b x)) (g := rho b ⁅x, y⁆)
      (fun u hu ↦ by simpa using ih u.degree (lt_of_le_of_lt hu hk) u rfl x y) hp
    simpa using this
  refine comm_of_basis b fun i j ↦ ?_
  -- the cases where `i ≤ t` or `j ≤ t`
  have hcase : ∀ i j : σ, LeAll j t →
      rho b (b i) (rho b (b j) (z R σ t)) - rho b (b j) (rho b (b i) (z R σ t)) =
        rho b ⁅b i, b j⁆ (z R σ t) := by
    intro i j hj
    rcases lt_trichotomy j i with hji | rfl | hij
    · exact comm_of_leAll b hj hji
    · simp
    · have := comm_of_leAll b (leAll_of_le hj hij.le) hij
      rw [← lie_skew, map_neg, LinearMap.neg_apply, ← this]
      abel
  by_cases hj : LeAll j t
  · exact hcase i j hj
  by_cases hi : LeAll i t
  · have := hcase j i hi
    rw [← lie_skew, map_neg, LinearMap.neg_apply, ← this]
    abel
  -- the general case: write `z^t = z_ν z^ψ` with `ν` the least index of `t`
  have hne := support_nonempty_of_not_leAll hi
  set ν := minIdx t hne
  set ψ := t - single ν 1
  have hνi : ν < i := minIdx_lt hi
  have hνj : ν < j := by
    have := minIdx_lt hj
    exact this
  have hψ : LeAll ν ψ := leAll_minIdx t hne
  have htψ : ψ + single ν 1 = t := sub_add_single_minIdx t hne
  have hψdeg : ψ.degree + 1 = m := htm ▸ degree_sub_single_minIdx t hne
  have hzt : z R σ t = rho b (b ν) (z R σ ψ) := by rw [rho_of_leAll b hψ, htψ]
  have hzψ : z R σ ψ ∈ restrictTotalDegree σ R ψ.degree := z_mem_restrictTotalDegree le_rfl
  have ihψ := ih' ψ.degree (by omega)
  -- `X_a X_ν (X_c z^ψ) = X_ν X_a (X_c z^ψ) + ρ⁅b a, b ν⁆ (X_c z^ψ)` for `ν < a`, `ν < c`
  have key : ∀ a c : σ, ν < a → ν < c →
      rho b (b a) (rho b (b ν) (rho b (b c) (z R σ ψ))) =
        rho b (b ν) (rho b (b a) (rho b (b c) (z R σ ψ))) +
          rho b ⁅b a, b ν⁆ (rho b (b c) (z R σ ψ)) := by
    intro a c hνa hνc
    set w := rho b (b c) (z R σ ψ) - z R σ (ψ + single c 1)
    have hw : w ∈ restrictTotalDegree σ R ψ.degree := rho_sub_mem b c ψ
    have hsplit : rho b (b c) (z R σ ψ) = z R σ (ψ + single c 1) + w := by
      simp [w]
    have h1 := comm_of_leAll b (leAll_add_single hψ hνc.le) hνa
    have h2 := ihψ w hw (b a) (b ν)
    rw [hsplit, map_add, map_add, map_add, map_add, map_add]
    rw [sub_eq_iff_eq_add] at h1 h2
    rw [h1, h2]
    abel
  -- `X_a z^t = X_ν X_a z^ψ + ρ⁅b a, b ν⁆ z^ψ` for `ν < a`
  have hX : ∀ a : σ, ν < a → rho b (b a) (z R σ t) =
      rho b (b ν) (rho b (b a) (z R σ ψ)) + rho b ⁅b a, b ν⁆ (z R σ ψ) := by
    intro a hνa
    have := comm_of_leAll b hψ hνa
    rw [sub_eq_iff_eq_add] at this
    rw [hzt, this, add_comm]
  have e1 : rho b (b i) (rho b (b j) (z R σ t)) =
      rho b (b ν) (rho b (b i) (rho b (b j) (z R σ ψ))) +
        rho b ⁅b i, b ν⁆ (rho b (b j) (z R σ ψ)) +
        rho b (b i) (rho b ⁅b j, b ν⁆ (z R σ ψ)) := by
    rw [hX j hνj, map_add, key i j hνi hνj]
  have e2 : rho b (b j) (rho b (b i) (z R σ t)) =
      rho b (b ν) (rho b (b j) (rho b (b i) (z R σ ψ))) +
        rho b ⁅b j, b ν⁆ (rho b (b i) (z R σ ψ)) +
        rho b (b j) (rho b ⁅b i, b ν⁆ (z R σ ψ)) := by
    rw [hX i hνi, map_add, key j i hνj hνi]
  have c1 := ihψ _ hzψ (b i) (b j)
  have c2 := ihψ _ hzψ ⁅b i, b ν⁆ (b j)
  have c3 := ihψ _ hzψ (b i) ⁅b j, b ν⁆
  have c4 := ihψ _ hzψ (b ν) ⁅b i, b j⁆
  have jac : ⁅b ν, ⁅b i, b j⁆⁆ + ⁅⁅b i, b ν⁆, b j⁆ + ⁅b i, ⁅b j, b ν⁆⁆ = 0 := by
    rw [lie_lie, ← lie_skew (b ν) (b j), lie_neg]
    abel
  have jac' : rho b ⁅b ν, ⁅b i, b j⁆⁆ (z R σ ψ) + rho b ⁅⁅b i, b ν⁆, b j⁆ (z R σ ψ) +
      rho b ⁅b i, ⁅b j, b ν⁆⁆ (z R σ ψ) = 0 := by
    rw [← LinearMap.add_apply, ← LinearMap.add_apply, ← map_add, ← map_add, jac]
    simp
  have c5 : rho b (b ν) (rho b (b i) (rho b (b j) (z R σ ψ))) =
      rho b (b ν) (rho b ⁅b i, b j⁆ (z R σ ψ)) +
        rho b (b ν) (rho b (b j) (rho b (b i) (z R σ ψ))) := by
    rw [← c1, map_sub]; abel
  rw [sub_eq_iff_eq_add] at c2 c3 c4
  rw [e1, e2, hzt, c5, c4, c2, c3]
  calc _ = rho b ⁅b i, b j⁆ (rho b (b ν) (z R σ ψ)) +
        (rho b ⁅b ν, ⁅b i, b j⁆⁆ (z R σ ψ) + rho b ⁅⁅b i, b ν⁆, b j⁆ (z R σ ψ) +
          rho b ⁅b i, ⁅b j, b ν⁆⁆ (z R σ ψ)) := by abel
    _ = _ := by rw [jac', add_zero]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The representation `ρ` as a morphism of Lie algebras. -/
def rhoHom : L →ₗ⁅R⁆ Module.End R (MvPolynomial σ R) :=
  { rho b with
    map_lie' := fun {x y} ↦ by
      apply (basisMonomials σ R).ext
      intro t
      rw [coe_basisMonomials]
      simp only [LinearMap.toFun_eq_coe, LieRing.of_associative_ring_bracket,
        LinearMap.sub_apply, Module.End.mul_apply]
      exact (rho_comm b t.degree t rfl x y).symm }

@[simp] lemma rhoHom_apply (x : L) : rhoHom b x = rho b x := rfl

/-- The linear map `R[X] → U(L)` sending `X^s` to the ordered monomial `pbwMonomial R b s`. -/
def phi : MvPolynomial σ R →ₗ[R] UniversalEnvelopingAlgebra R L :=
  extend fun s ↦ pbwMonomial R b s

@[simp] lemma phi_z (s : σ →₀ ℕ) : phi b (z R σ s) = pbwMonomial R b s := extend_z _ s

/-- Property (D): `φ` intertwines `ρ` with left multiplication. -/
lemma phi_rho (m : ℕ) : ∀ s : σ →₀ ℕ, s.degree = m → ∀ x : L,
    phi b (rho b x (z R σ s)) = ι R x * phi b (z R σ s) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro s hsm
  have ih' : ∀ k, k < m → ∀ p ∈ restrictTotalDegree σ R k, ∀ x : L,
      phi b (rho b x p) = ι R x * phi b p := by
    intro k hk p hp x
    have := eq_of_mem_restrictTotalDegree (n := k)
      (f := phi b ∘ₗ rho b x) (g := LinearMap.mulLeft R (ι R x) ∘ₗ phi b)
      (fun u hu ↦ by simpa using ih u.degree (lt_of_le_of_lt hu hk) u rfl x) hp
    simpa using this
  -- reduce to basis vectors
  suffices h : ∀ i, phi b (rho b (b i) (z R σ s)) = ι R (b i) * phi b (z R σ s) by
    intro x
    have := b.ext (f₁ := phi b ∘ₗ (LinearMap.applyₗ (z R σ s) ∘ₗ rho b))
      (f₂ := LinearMap.mulRight R (phi b (z R σ s)) ∘ₗ (ι R : L →ₗ⁅R⁆ _).toLinearMap)
      (fun i ↦ by simpa using h i)
    simpa using LinearMap.congr_fun this x
  intro i
  by_cases hle : LeAll i s
  · rw [rho_of_leAll b hle, phi_z, phi_z, pbwMonomial_add_single hle]
  · have hne := support_nonempty_of_not_leAll hle
    have hrec := rho_of_not_leAll b hle
    obtain ⟨j, hj⟩ : ∃ j, minIdx s hne = j := ⟨_, rfl⟩
    obtain ⟨t, htdef⟩ : ∃ t, s - single j 1 = t := ⟨_, rfl⟩
    rw [hj, htdef] at hrec
    have hts : t + single j 1 = s := by rw [← htdef, ← hj]; exact sub_add_single_minIdx s hne
    have ht : LeAll j t := by rw [← htdef, ← hj]; exact leAll_minIdx s hne
    have htdeg : t.degree + 1 = m := by
      rw [← hsm, ← htdef, ← hj]; exact degree_sub_single_minIdx s hne
    have hji : j < i := hj ▸ minIdx_lt hle
    have ih'' := ih' t.degree (by omega)
    have hzt : z R σ t ∈ restrictTotalDegree σ R t.degree := z_mem_restrictTotalDegree le_rfl
    rw [hrec]
    simp only [map_add]
    rw [ih'' _ (rho_sub_mem b i t), map_sub, ih'' _ hzt (b i), ih'' _ hzt ⁅b i, b j⁆]
    rw [← hts]
    simp only [phi_z]
    rw [pbwMonomial_add_single ht,
      add_right_comm t (single j 1), pbwMonomial_add_single (leAll_add_single ht hji.le),
      LieHom.map_lie, LieRing.of_associative_ring_bracket]
    noncomm_ring

/-- `φ` is a morphism of `U(L)`-modules. -/
lemma phi_lift (u : UniversalEnvelopingAlgebra R L) (p : MvPolynomial σ R) :
    phi b (lift R (rhoHom b) u p) = u * phi b p := by
  have hsurj : Function.Surjective (mkAlgHom R L) := by
    intro u
    induction u using Quotient.inductionOn' with
    | h a => exact ⟨a, rfl⟩
  obtain ⟨a, rfl⟩ := hsurj u
  induction a using TensorAlgebra.induction generalizing p with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_one_mul, LinearMap.smul_apply, Module.End.one_apply,
      map_smul]
  | ι x =>
    have : mkAlgHom R L (TensorAlgebra.ι R x) = ι R x := rfl
    rw [this, lift_ι_apply, rhoHom_apply]
    refine eq_of_mem_restrictTotalDegree (n := p.totalDegree)
      (f := phi b ∘ₗ rho b x) (g := LinearMap.mulLeft R (ι R x) ∘ₗ phi b)
      (fun u _ ↦ by simpa using phi_rho b u.degree u rfl x)
      ((mem_restrictTotalDegree σ _ p).mpr le_rfl)
  | add a₁ a₂ h₁ h₂ =>
    rw [map_add, map_add, LinearMap.add_apply, map_add, h₁, h₂, add_mul]
  | mul a₁ a₂ h₁ h₂ =>
    rw [map_mul, map_mul, Module.End.mul_apply, h₁, h₂, mul_assoc]

/-- `u ↦ ρ(u) 1` sends ordered monomials to monomials. -/
lemma lift_pbwMonomial (m : ℕ) : ∀ s : σ →₀ ℕ, s.degree = m →
    lift R (rhoHom b) (pbwMonomial R b s) 1 = z R σ s := by
  induction m with
  | zero =>
    intro s hs
    rw [degree_eq_zero_iff] at hs
    subst hs
    simp only [pbwMonomial_zero, map_one, Module.End.one_apply]
    rfl
  | succ m ih =>
    intro s hs
    have hne : s.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
      rintro rfl; simp at hs
    have hts := sub_add_single_minIdx s hne
    have ht := leAll_minIdx s hne
    have htdeg := degree_sub_single_minIdx s hne
    rw [← hts, pbwMonomial_add_single ht, map_mul, Module.End.mul_apply, ih _ (by omega),
      lift_ι_apply, rhoHom_apply, rho_of_leAll b ht]

end PBW

open PBW

attribute [local instance 100] LieRing.ofAssociativeRing

variable (b : Basis σ R L)

/-- The Poincaré–Birkhoff–Witt isomorphism `U(L) ≃ₗ[R] R[X_i : i ∈ σ]`, sending the ordered
monomial `pbwMonomial R b s` to `X^s`. -/
def pbwEquiv : UniversalEnvelopingAlgebra R L ≃ₗ[R] MvPolynomial σ R :=
  LinearEquiv.ofLinearMap
    (LinearMap.applyₗ (1 : MvPolynomial σ R) ∘ₗ (lift R (rhoHom b)).toLinearMap)
    (phi b)
    ((basisMonomials σ R).ext fun s ↦ by
      rw [coe_basisMonomials]
      simpa using lift_pbwMonomial b s.degree s rfl)
    (LinearMap.ext fun u ↦ by
      have h1 : phi b 1 = 1 := by
        rw [show (1 : MvPolynomial σ R) = z R σ 0 from rfl, phi_z, pbwMonomial_zero]
      simpa [h1] using phi_lift b u 1)

@[simp] lemma pbwEquiv_symm_monomial (s : σ →₀ ℕ) :
    (pbwEquiv b).symm (monomial s 1) = pbwMonomial R b s :=
  phi_z b s

@[simp] lemma pbwEquiv_pbwMonomial (s : σ →₀ ℕ) :
    pbwEquiv b (pbwMonomial R b s) = monomial s 1 := by
  rw [← pbwEquiv_symm_monomial, LinearEquiv.apply_symm_apply]

/-- **Poincaré–Birkhoff–Witt theorem**: if `L` is a Lie algebra over a commutative ring `R` with a
basis `b` indexed by a linearly ordered type `σ`, then the ordered monomials `pbwMonomial R b s`
form an `R`-basis of the universal enveloping algebra.

See Humphreys, *Introduction to Lie algebras and representation theory*, §17.3, Theorem and
Corollary C, proved in §17.4 (stated there over a field; the proof works over any
commutative ring for free modules), and Bourbaki, *Lie groups and Lie algebras*, Ch. I, §2.7,
Theorem 1 and Corollary 3. -/
def pbwBasis : Basis (σ →₀ ℕ) R (UniversalEnvelopingAlgebra R L) :=
  (basisMonomials σ R).map (pbwEquiv b).symm

@[simp] theorem pbwBasis_apply (s : σ →₀ ℕ) : pbwBasis b s = pbwMonomial R b s := by
  simp [pbwBasis]

lemma pbwMonomial_single (i : σ) : pbwMonomial R b (single i 1) = ι R (b i) := by
  simpa using pbwMonomial_add_single (R := R) (v := b) (leAll_zero i)

theorem pbwEquiv_ι_basis (i : σ) : pbwEquiv b (ι R (b i)) = X i := by
  rw [← pbwMonomial_single, pbwEquiv_pbwMonomial, X]

/-- If `L` has a basis then `ι : L → U(L)` is injective. -/
theorem ι_injective_of_basis (b : Basis σ R L) :
    Function.Injective (ι R : L → UniversalEnvelopingAlgebra R L) := by
  intro x y h
  have hF : ∀ i, (MvPolynomial.lcoeff R (single i 1)).comp
      ((pbwEquiv b).toLinearMap.comp (ι R : L →ₗ⁅R⁆ _).toLinearMap) = b.coord i := fun i ↦
    b.ext fun j ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap,
        LinearEquiv.coe_coe, pbwEquiv_ι_basis, lcoeff_apply, coeff_X, Basis.coord_apply,
        Basis.repr_self, Finsupp.single_apply, Finsupp.single_left_inj one_ne_zero]
  apply b.repr.injective
  ext i
  have := congr_arg (fun u ↦ (pbwEquiv b u).coeff (single i 1)) h
  rw [← Basis.coord_apply, ← Basis.coord_apply, ← hF i]
  simpa using this

variable (R L) in
/-- **Corollary of PBW**: if `L` is free as an `R`-module then the canonical map `ι : L → U(L)`
is injective. See Humphreys, §17.3, Corollary B. -/
theorem ι_injective [Module.Free R L] :
    Function.Injective (ι R : L → UniversalEnvelopingAlgebra R L) := by
  let b := Module.Free.chooseBasis R L
  let : LinearOrder (Module.Free.ChooseBasisIndex R L) :=
    IsWellOrder.linearOrder WellOrderingRel
  exact ι_injective_of_basis b

end UniversalEnvelopingAlgebra
