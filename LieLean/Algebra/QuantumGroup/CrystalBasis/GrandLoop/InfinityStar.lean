/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityForm
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# `L(∞)* = L(∞)`

Let `*` be the anti-automorphism of `U⁻` fixing the `Fᵢ` (`GrandLoop.starU`, induced by `σ` on
`'f`). Assume that `A/ϖA` is formally real (`IsFormallyReal`; for `k = ℚ(v)` and the valuation
ring at `v = ∞` it is `ℚ`, which is Kashiwara's setting). Then:

* `L(∞) ∩ U⁻_{-ν} = {u ∈ U⁻_{-ν} | (u, u) ∈ A}` (`GrandLoop.mem_latInf_iff_formU_mem`;
  [Kas91] Prop. 5.1.3, stated there on all of `U⁻`, whose weight spaces are orthogonal; from the
  orthonormality of `B(∞)` modulo `ϖ`);
* `L(∞)* = L(∞)` (`GrandLoop.starU_mem_latInf`; [Kas91] Prop. 5.2.4), since `(u*, w*) = (u, w)`.

## References

* [Kas91] M. Kashiwara, *On crystal bases of the q-analogue of universal enveloping algebras*,
  Duke Math. J. 63 (1991), §5.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

/-! ### The anti-automorphism `*` of `U⁻` -/

variable (D v) in
/-- `*` on `U⁻ = 'f/J`. -/
def starU : Module.End k (Um D v) :=
  (serreSubmodule D v).mapQ (serreSubmodule D v) (rev k I) fun x hx ↦ by
    rw [Submodule.mem_comap, mem_serreSubmodule]
    exact rev_mem_serreIdeal D v (mem_serreSubmodule.1 hx)

omit [CharZero k] [NeZero v] [DecidableEq I] in
lemma starU_mk (x : LusztigF k I) :
    starU D v (Submodule.Quotient.mk x) = Submodule.Quotient.mk (rev k I x) := rfl

omit [CharZero k] in
lemma formU_starU (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (u w : Um D v) :
    formU hv' (starU D v u) (starU D v w) = formU hv' u w := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact form_rev D v x y

omit [CharZero k] [NeZero v] [DecidableEq I] in
@[simp] lemma starU_starU (u : Um D v) : starU D v (starU D v u) = u := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [starU_mk, starU_mk, rev_rev]

omit [CharZero k] [NeZero v] [DecidableEq I] in
lemma starU_mem_Uw {ν : I →₀ ℕ} {u : Um D v}
    (hu : u ∈ Uw D v ν) : starU D v u ∈ Uw D v ν := by
  obtain ⟨y, hy, rfl⟩ := hu
  exact ⟨rev k I y, rev_mem_weightSpace hy, rfl⟩

/-! ### Generic lemmas -/

omit [DecidableEq I] in
/-- Representatives of a finite family modulo a submodule. -/
lemma exists_reps_mod {M : Type*} [AddCommGroup M] [Module A M] (P : Submodule A M)
    (f : List I → M) (W : Finset (List I)) :
    ∃ S ⊆ W, (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → f s₁ - f s₂ ∉ P) ∧
      ∀ w ∈ W, ∃ s ∈ S, f w - f s ∈ P := by
  classical
  induction W using Finset.induction_on with
  | empty => exact ⟨∅, le_rfl, by simp, by simp⟩
  | insert w W _ ih =>
    obtain ⟨S, hSW, hSd, hcov⟩ := ih
    by_cases h : ∃ s ∈ S, f w - f s ∈ P
    · refine ⟨S, hSW.trans (Finset.subset_insert _ _), hSd, fun x hx ↦ ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hcov x hx
    push Not at h
    refine ⟨insert w S, Finset.insert_subset_insert _ hSW, fun s₁ h₁ s₂ h₂ hne ↦ ?_,
      fun x hx ↦ ?_⟩
    · by_cases e₁ : s₁ = w
      · subst e₁
        exact h s₂ (Finset.mem_of_mem_insert_of_ne h₂ (Ne.symm hne))
      by_cases e₂ : s₂ = w
      · subst e₂
        intro hm
        exact h s₁ (Finset.mem_of_mem_insert_of_ne h₁ e₁)
          (by have := neg_mem hm; rwa [neg_sub] at this)
      exact hSd s₁ (Finset.mem_of_mem_insert_of_ne h₁ e₁) s₂
        (Finset.mem_of_mem_insert_of_ne h₂ e₂) hne
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨x, Finset.mem_insert_self _ _, by rw [sub_self]; exact zero_mem _⟩
      · obtain ⟨s, hs, h'⟩ := hcov x hx
        exact ⟨s, Finset.mem_insert_of_mem hs, h'⟩

/-- In a formally real commutative ring, a vanishing sum of squares has vanishing terms. -/
lemma eq_zero_of_sum_sq_eq_zero {S : Type*} [CommRing S] [IsFormallyReal S] {ι : Type*}
    (T : Finset ι) (a : ι → S) (h : ∑ t ∈ T, a t ^ 2 = 0) : ∀ t ∈ T, a t = 0 := by
  classical
  intro t ht
  rw [← Finset.add_sum_erase T _ ht] at h
  have h2 : a t ^ 2 = 0 := IsFormallyReal.eq_zero_of_add_right
    (by rw [sq]; exact IsSumSq.mul_self _) (IsSumSq.sum_sq _ _) h
  exact IsReduced.eq_zero _ ⟨2, h2⟩

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

include hR in
/-- Every `u ∈ U⁻_{-ν}` has `ϖⁿ u ∈ L(∞)` for some `n`. -/
lemma exists_pow_smul_mem_latInf {ν : I →₀ ℕ} {u : Um D v} (hu : u ∈ Uw D v ν) :
    ∃ n : ℕ, ϖ ^ n • u ∈ latInf hvt A := by
  obtain ⟨y, hy, rfl⟩ := hu
  obtain ⟨n, hn⟩ := exists_pow_smul_ev_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund y
  obtain ⟨Λ, hΛ⟩ := exists_dom_ge hfund ν.degree
  refine ⟨n, ?_⟩
  have hsw : ϖ ^ n • (Submodule.Quotient.mk y : Um D v) ∈ Uw D v ν := by
    rw [← algebraMap_smul k]; exact Submodule.smul_mem _ _ ⟨y, hy, rfl⟩
  rw [show (Submodule.mkQ (serreSubmodule D v) y : Um D v) = Submodule.Quotient.mk y from rfl,
    mem_latticeInf_iff (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund hΛ hsw]
  rw [← algebraMap_smul k, map_smul, algebraMap_smul]
  exact hn Λ

include hR in
/-- If `A/ϖA` is formally real, `x ∈ L(∞)` and `(x, x) ∈ ϖA`, then `x ∈ ϖL(∞)`: the form induced
on `L(∞)/ϖL(∞)` is positive definite, `B(∞)` being orthonormal ([Kas91] Prop. 5.1.2 (iii)). -/
theorem mem_smul_latInf_of_formU_mem [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {x : Um D v}
    (hxL : x ∈ latInf hvt A) {b₀ : A}
    (hxx : formU (pow_ne_one_of_transcendental' hvt) x x = algebraMap A k (ϖ * b₀)) :
    x ∈ ϖ • latInf hvt A := by
  classical
  set hv' := pow_ne_one_of_transcendental' hvt
  -- expansion of `x` in the `f̃_w 1`
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hxL
  set W := c.support
  obtain ⟨S, -, hSd, hcov⟩ := exists_reps_mod (ϖ • latInf hvt A) (fWi (D := D) hvt) W
  choose! r hrS hr using hcov
  obtain ⟨a, ha⟩ : ∃ a : List I → A, ∀ s, a s = ∑ w ∈ W with r w = s, c w := ⟨_, fun _ ↦ rfl⟩
  set y : Um D v := ∑ s ∈ S, algebraMap A k (a s) • fWi hvt s with hy
  have hy' : y = ∑ w ∈ W, algebraMap A k (c w) • fWi (D := D) hvt (r w) := by
    rw [hy, ← Finset.sum_fiberwise_of_maps_to (g := r) (t := S) hrS]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ha, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [(Finset.mem_filter.1 hw).2]
  have hxy : x - y ∈ ϖ • latInf hvt A := by
    rw [hy', ← hc, Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun w hw ↦ ?_
    rw [← algebraMap_smul k, ← smul_sub, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hr w hw)
  have hyL : y ∈ latInf hvt A := by
    rw [hy]
    exact Submodule.sum_mem _ fun s _ ↦ by
      rw [algebraMap_smul]; exact Submodule.smul_mem _ _ (NegativePart.fWord_mem_latticeInf _ _ s)
  -- `(x, x) ≡ (y, y)`
  obtain ⟨t₁, ht₁⟩ := formU_mem_smul (hR := hR) hinj hϖ hϖv hk hfund hxL hxy
  obtain ⟨t₂, ht₂⟩ := formU_mem_smul (hR := hR) hinj hϖ hϖv hk hfund hyL hxy
  have hxy' : formU hv' x x - formU hv' y y = algebraMap A k (ϖ * (t₁ + t₂)) := by
    have : formU hv' x x - formU hv' y y = formU hv' x (x - y) + formU hv' y (x - y) := by
      rw [map_sub, map_sub, formU_comm hv' y x]; ring
    rw [this, ht₁, ht₂, ← map_add, mul_add]
  -- `(y, y) ≡ ∑ a_s²`
  choose e he using fun s s' ↦
    formU_fWi_fWi (hR := hR) (A := A) (D := D) hinj hϖ hϖv hk hfund s s'
  have hexp : formU hv' y y = ∑ s ∈ S, ∑ s' ∈ S, algebraMap A k (a s) *
      (algebraMap A k (a s') * formU hv' (fWi (D := D) hvt s) (fWi hvt s')) := by
    rw [hy]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [formU_comm hv']
  have key : ∀ s ∈ S, ∀ s' ∈ S, algebraMap A k (a s) *
      (algebraMap A k (a s') * formU hv' (fWi (D := D) hvt s) (fWi hvt s')) =
      (if s = s' then algebraMap A k (a s ^ 2) else 0) +
        algebraMap A k (ϖ * (a s * a s' * e s s')) := by
    intro s hs s' hs'
    rw [he]
    by_cases h : s = s'
    · subst h
      simp only [sub_self, zero_mem, ↓reduceIte, map_mul, map_pow]
      ring
    · rw [ite_eq_right_iff.2 (fun h' ↦ absurd h' (hSd s hs s' hs' h))]
      simp only [h, ↓reduceIte, map_mul]
      ring
  have hyy : formU hv' y y = algebraMap A k (∑ s ∈ S, a s ^ 2) +
      algebraMap A k (ϖ * ∑ s ∈ S, ∑ s' ∈ S, a s * a s' * e s s') := by
    rw [hexp, Finset.sum_congr rfl fun s hs ↦ Finset.sum_congr rfl fun s' hs' ↦ key s hs s' hs']
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, map_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s hs ↦ by simp [hs]
  -- conclusion
  have hsum : ∑ s ∈ S, a s ^ 2 ∈ Ideal.span {ϖ} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨b₀ - (t₁ + t₂) - ∑ s ∈ S, ∑ s' ∈ S, a s * a s' * e s s', ?_⟩
    apply hinj
    have h1 := hxy'
    rw [hxx, hyy] at h1
    simp only [map_mul, map_sub, map_add] at h1 ⊢
    linear_combination h1
  have hall : ∀ s ∈ S, a s ∈ Ideal.span {ϖ} := by
    intro s hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine eq_zero_of_sum_sq_eq_zero S (fun s ↦ Ideal.Quotient.mk _ (a s)) ?_ s hs
    simp only [← map_pow, ← map_sum]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hsum
  have hyS : y ∈ ϖ • latInf hvt A := by
    rw [hy]
    refine Submodule.sum_mem _ fun s hs ↦ ?_
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hall s hs)
    rw [← hb, algebraMap_smul, mul_comm, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (Submodule.smul_mem _ _ (NegativePart.fWord_mem_latticeInf _ _ s))
  simpa using add_mem hxy hyS

include hR in
/-- **[Kas91] Prop. 5.1.3**: if the residue ring `A/ϖA` is formally real, then
`L(∞) ∩ U⁻_{-ν} = {u ∈ U⁻_{-ν} | (u, u) ∈ A}`. Kashiwara states this for `A` the local ring of
`ℚ(q)` at `q = 0` (residue field `ℚ`); the proof uses only the orthonormality of `B(∞)` modulo
`ϖ` ([Kas91] Prop. 5.1.2) and formal reality. -/
theorem mem_latInf_iff_formU_mem [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {ν : I →₀ ℕ}
    {u : Um D v} (hu : u ∈ Uw D v ν) :
    u ∈ latInf hvt A ↔
      ∃ a : A, formU (pow_ne_one_of_transcendental' hvt) u u = algebraMap A k a := by
  classical
  refine ⟨fun h ↦ formU_mem (hR := hR) hinj hϖ hϖv hk hfund h h, fun ⟨a₀, ha₀⟩ ↦ ?_⟩
  by_contra hnot
  set hv' := pow_ne_one_of_transcendental' hvt
  have hex : ∃ n : ℕ, ϖ ^ n • u ∈ latInf hvt A :=
    exists_pow_smul_mem_latInf (hR := hR) hinj hϖ hϖv hk hfund hu
  set n := Nat.find hex with hn
  have hxL : ϖ ^ n • u ∈ latInf hvt A := Nat.find_spec hex
  have hn0 : n ≠ 0 := fun h ↦ hnot (by simpa [h] using hxL)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmL : ϖ ^ m • u ∉ latInf hvt A := Nat.find_min hex (by omega)
  have hϖ0 : algebraMap A k ϖ ≠ 0 := by rw [hϖv]; exact inv_ne_zero (NeZero.ne v)
  set x := ϖ ^ n • u with hx
  -- `x ∉ ϖ L(∞)`
  have hxS : x ∉ ϖ • latInf hvt A := by
    intro h
    obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    refine hmL ?_
    have : y = ϖ ^ m • u := by
      have e : (algebraMap A k ϖ) • y = (algebraMap A k ϖ) • (ϖ ^ m • u) := by
        rw [algebraMap_smul, algebraMap_smul, hyx, hx, hm, pow_succ', mul_smul]
      exact smul_right_injective _ hϖ0 e
    exact this ▸ hy
  -- `(x, x) ∈ ϖ A`
  have hxx : formU hv' x x = algebraMap A k (ϖ * (ϖ ^ (2 * n - 1) * a₀)) := by
    simp only [hx, ← algebraMap_smul k (ϖ ^ n) u, map_smul, LinearMap.smul_apply, ha₀,
      smul_eq_mul]
    have e2 : n + n = 2 * n - 1 + 1 := by omega
    rw [← map_mul, ← map_mul, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_succ', e2]
  exact hxS (mem_smul_latInf_of_formU_mem (hR := hR) hinj hϖ hϖv hk hfund hxL hxx)

include hR in
/-- **[Kas91] Prop. 5.2.4**: `L(∞)* = L(∞)`, when `A/ϖA` is formally real. -/
theorem starU_mem_latInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {u : Um D v}
    (hu : u ∈ latInf hvt A) : starU D v u ∈ latInf hvt A := by
  induction hu using Submodule.span_induction with
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [← algebraMap_smul k, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ ha
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    have hw := fWi_mem_Uw (D := D) (hvt := hvt) w
    rw [mem_latInf_iff_formU_mem (hR := hR) hinj hϖ hϖv hk hfund (starU_mem_Uw hw),
      formU_starU (pow_ne_one_of_transcendental' hvt)]
    exact formU_mem (hvt := hvt) (hR := hR) hinj hϖ hϖv hk hfund
      (NegativePart.fWord_mem_latticeInf _ _ w)
      (NegativePart.fWord_mem_latticeInf _ _ w)

end Base

end GrandLoop

end LieLean.QuantumGroup
