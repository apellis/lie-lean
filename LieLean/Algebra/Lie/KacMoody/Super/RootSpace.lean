/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.InvariantForm

/-!
# Root spaces of `G̃(A, τ)`

For `k ∈ Q₊ \ {0}` the root space `G̃_{α}` of `G̃ = G̃(A, τ)` at `α = ∑ kᵢ αᵢ` is spanned by the
iterated super commutators `[e_{j₁}, [e_{j₂}, ⋯ [e_{jₙ}, eᵢ] ⋯ ]]` whose letters add up to `k`
([Kac78] §1.2, cf. [Kac] Thm. 1.2 (d)). In particular `G̃_{αᵢ} = K eᵢ`, `G̃_{2αᵢ} = K [eᵢ, eᵢ]`
(which is `0` for `i` even) and `G̃_{mαᵢ} = 0` for `m ≥ 3`; the corresponding statements hold for
the negative roots, through the Chevalley involution.

## Main results

* `Matrix.Realization.SuperEnveloping.gTilde_inf_weightSpace_rootOf`: `G̃_{α}` for `α ∈ Q₊ \ {0}`.
* `Matrix.Realization.SuperEnveloping.mem_weightSpace_root`: `G̃_{αᵢ} = K eᵢ`.
* `Matrix.Realization.SuperEnveloping.mem_weightSpace_two_root`: `G̃_{2αᵢ} = K [eᵢ, eᵢ]`.
* `Matrix.Realization.SuperEnveloping.eq_zero_of_mem_weightSpace_nsmul_root`: `G̃_{mαᵢ} = 0` for
  `m ≥ 3`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.2.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

namespace SuperEnveloping

/-! ### Words -/

omit [Fintype ι] in
lemma wordVec_eq_zero_iff {w : List ι} : wordVec w = 0 ↔ w = [] := by
  refine ⟨fun hw ↦ ?_, fun hw ↦ hw ▸ wordVec_nil⟩
  cases w with
  | nil => rfl
  | cons j w =>
    have := congrFun hw j
    have hj := wordVec_nonneg w j
    simp only [wordVec_cons, Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at this hj
    omega

omit [Fintype ι] in
lemma wordVec_cons_eq_nsmul_single {j i : ι} {w : List ι} {n : ℕ}
    (hw : wordVec (j :: w) = (n + 1 : ℕ) • Pi.single i (1 : ℤ)) :
    j = i ∧ wordVec w = n • Pi.single i (1 : ℤ) := by
  have hji : j = i := by
    by_contra hji
    have := congrFun hw j
    have hj := wordVec_nonneg w j
    simp only [wordVec_cons, Pi.add_apply, Pi.single_eq_same, Pi.smul_apply,
      Pi.single_eq_of_ne hji, smul_zero, Pi.zero_apply] at this hj
    omega
  subst hji
  refine ⟨rfl, ?_⟩
  rw [wordVec_cons, add_smul, one_smul, add_comm] at hw
  exact add_right_cancel hw

omit [Fintype ι] in
/-- A word whose letters add up to `n αᵢ` is `[i, …, i]`. -/
lemma eq_replicate_of_wordVec {i : ι} {w : List ι} {n : ℕ}
    (hw : wordVec w = n • Pi.single i (1 : ℤ)) : w = List.replicate n i := by
  induction w generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n =>
      have := congrFun hw i
      simp at this
      omega
  | cons j w ih =>
    cases n with
    | zero =>
      rw [zero_smul] at hw
      exact absurd ((wordVec_eq_zero_iff).1 hw) (List.cons_ne_nil _ _)
    | succ n =>
      obtain ⟨rfl, hw'⟩ := wordVec_cons_eq_nsmul_single hw
      rw [ih hw', List.replicate_succ]

/-! ### Root spaces of `ñ₊` -/

open Classical in
/-- The weight indicator of `μ`, i.e. the projection of `U` onto `U_μ`. -/
def wProj (μ : Dual K H) : Module.End K (P.SuperEnveloping p) :=
  wScale P p fun ν ↦ if ν = μ then 1 else 0

lemma wProj_of_mem {μ : Dual K H} {x : P.SuperEnveloping p} (hx : x ∈ weightSpace P p μ) :
    wProj P p μ x = x := by
  rw [wProj, wScale_of_mem P p _ hx]; simp

lemma wProj_of_mem_ne {μ ν : Dual K H} (hν : ν ≠ μ) {x : P.SuperEnveloping p}
    (hx : x ∈ weightSpace P p ν) : wProj P p μ x = 0 := by
  rw [wProj, wScale_of_mem P p _ hx]; simp [hν]

/-- The span of the iterated super commutators of the `eⱼ` with letters adding up to `k`. -/
def nPlusRoot (k : ι → ℤ) : Submodule K (P.SuperEnveloping p) :=
  Submodule.span K {x | ∃ i w, wordVec (i :: w) = k ∧ eLie P p i w = x}

lemma eLie_mem_weightSpace_rootOf (i : ι) (w : List ι) :
    eLie P p i w ∈ weightSpace P p (P.rootOf (wordVec (i :: w))) := by
  rw [rootOf_wordVec, List.map_cons, List.sum_cons, add_comm]
  exact eLie_mem_weightSpace P p i w

lemma nPlusRoot_le_weightSpace (k : ι → ℤ) :
    nPlusRoot P p k ≤ weightSpace P p (P.rootOf k) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, w, hk, rfl⟩
  exact hk ▸ eLie_mem_weightSpace_rootOf P p i w

variable [CharZero K]

/-- The projection of `ñ₊` onto `U_α` lies in the span of the matching iterated commutators. -/
lemma wProj_mem_nPlusRoot (k : ι → ℤ) {x : P.SuperEnveloping p} (hx : x ∈ nPlus P p) :
    wProj P p (P.rootOf k) x ∈ nPlusRoot P p k := by
  suffices nPlus P p ≤ (nPlusRoot P p k).comap (wProj P p (P.rootOf k)) from this hx
  refine (nPlus_le_iff P p).2 fun i w ↦ ?_
  rw [Submodule.mem_comap]
  by_cases hk : wordVec (i :: w) = k
  · rw [wProj_of_mem P p (hk ▸ eLie_mem_weightSpace_rootOf P p i w)]
    exact Submodule.subset_span ⟨i, w, hk, rfl⟩
  · rw [wProj_of_mem_ne P p (fun h ↦ hk (P.rootOf_injective h))
      (eLie_mem_weightSpace_rootOf P p i w)]
    exact zero_mem _

/-- The projection onto `U_α`, `α ∈ Q₊ \ {0}`, kills `ñ₋`. -/
lemma wProj_nMinus {k : ι → ℤ} (hk : k ∈ posCone ι) {x : P.SuperEnveloping p}
    (hx : x ∈ nMinus P p) : wProj P p (P.rootOf k) x = 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  suffices nPlus P p ≤ (LinearMap.ker (wProj P p (P.rootOf k))).comap (omega P p).toLinearMap
    from this hy
  refine (nPlus_le_iff P p).2 fun i w ↦ ?_
  refine wProj_of_mem_ne P p (fun h ↦ ?_)
    (omega_mem_weightSpace P p (eLie_mem_weightSpace_rootOf P p i w))
  have hsum : wordVec (i :: w) + k ∈ posCone ι :=
    ⟨add_nonneg (wordVec_nonneg _) hk.1, fun h0 ↦ hk.2 <| le_antisymm
      (by have := wordVec_nonneg (i :: w); rw [← h0]; exact le_add_of_nonneg_left this) hk.1⟩
  refine P.rootOf_ne_zero hsum.2 ?_
  rw [map_add, ← h, add_neg_cancel]

/-- `G̃_α` for `α = ∑ kᵢ αᵢ ∈ Q₊ \ {0}` is spanned by the iterated super commutators
`[e_{j₁}, ⋯ [e_{jₙ}, eᵢ] ⋯ ]` with `αᵢ + ∑ α_{jₗ} = α` ([Kac78] §1.2). -/
theorem gTilde_inf_weightSpace_rootOf {k : ι → ℤ} (hk : k ∈ posCone ι) :
    gTilde P p ⊓ weightSpace P p (P.rootOf k) = nPlusRoot P p k := by
  refine le_antisymm ?_ (le_inf ?_ (nPlusRoot_le_weightSpace P p k))
  · rintro x ⟨hx, hxk⟩
    obtain ⟨n, hn, a, m, hm, rfl⟩ := (mem_gTilde_iff P p).1 hx
    rw [← wProj_of_mem P p hxk, map_add, map_add, wProj_nMinus P p hk hn,
      wProj_of_mem_ne P p (Ne.symm (P.rootOf_ne_zero hk.2)) (h_mem_weightSpace P p a), zero_add,
      zero_add]
    exact wProj_mem_nPlusRoot P p k hm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, w, -, rfl⟩
    exact nPlus_le_gTilde P p (eLie_mem_nPlus P p i w)

/-! ### Multiples of a simple root -/

omit [CharZero K] in
lemma rootOf_nsmul_single (i : ι) (n : ℕ) :
    P.rootOf (n • Pi.single i (1 : ℤ)) = n • P.root i := by
  rw [map_nsmul]
  congr 1
  simp

omit [Fintype ι] [CharZero K] in
lemma nsmul_single_mem_posCone (i : ι) {n : ℕ} (hn : n ≠ 0) :
    n • Pi.single i (1 : ℤ) ∈ posCone ι := by
  refine ⟨fun j ↦ ?_, fun h0 ↦ hn ?_⟩
  · by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  · have := congrFun h0 i
    simpa using this

omit [CharZero K] in
lemma mem_nPlusRoot_nsmul {i : ι} {n : ℕ} {x : P.SuperEnveloping p}
    (hx : x ∈ nPlusRoot P p ((n + 1 : ℕ) • Pi.single i (1 : ℤ))) :
    x ∈ K ∙ eLie P p i (List.replicate n i) := by
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨j, w, hw, rfl⟩
  obtain ⟨rfl, hw'⟩ := wordVec_cons_eq_nsmul_single hw
  rw [eq_replicate_of_wordVec hw']
  exact Submodule.mem_span_singleton_self _

lemma mem_weightSpace_nsmul_root {i : ι} {n : ℕ} {x : P.SuperEnveloping p}
    (hx : x ∈ gTilde P p) (hxn : x ∈ weightSpace P p ((n + 1) • P.root i)) :
    x ∈ K ∙ eLie P p i (List.replicate n i) := by
  have hk := nsmul_single_mem_posCone (i := i) (Nat.succ_ne_zero n)
  rw [← rootOf_nsmul_single] at hxn
  have : x ∈ gTilde P p ⊓ weightSpace P p (P.rootOf ((n + 1 : ℕ) • Pi.single i (1 : ℤ))) :=
    ⟨hx, hxn⟩
  rw [gTilde_inf_weightSpace_rootOf P p hk] at this
  exact mem_nPlusRoot_nsmul P p this

/-- `G̃_{αᵢ} = K eᵢ`. -/
theorem mem_weightSpace_root {i : ι} {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxi : x ∈ weightSpace P p (P.root i)) : ∃ c : K, x = c • e P p i := by
  have := mem_weightSpace_nsmul_root P p (n := 0) hx (by rwa [zero_add, one_smul])
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  exact ⟨c, by simpa using hc.symm⟩

/-- `G̃_{2αᵢ} = K [eᵢ, eᵢ]`. -/
theorem mem_weightSpace_two_root {i : ι} {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p)
    (hxi : x ∈ weightSpace P p (2 • P.root i)) :
    ∃ c : K, x = c • superBracket P p (e P p i) (e P p i) := by
  have := mem_weightSpace_nsmul_root P p (n := 1) hx hxi
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  exact ⟨c, by simpa using hc.symm⟩

/-- `[eᵢ, [eᵢ, eᵢ]] = 0`: for `i` even `[eᵢ, eᵢ] = 0`, and for `i` odd this is the super Jacobi
identity. -/
lemma superBracket_e_superBracket_e_e (i : ι) :
    superBracket P p (e P p i) (superBracket P p (e P p i) (e P p i)) = 0 := by
  have hJ := superBracket_jacobi (isHomog_e P p i) (isHomog_e P p i) (isHomog_e P p i)
  have hS := superBracket_swap ((isHomog_e P p i).superBracket (isHomog_e P p i))
    (isHomog_e P p i)
  rw [show p i + p i = 0 by rcases zmod_two_cases (p i) with h | h <;> rw [h] <;> rfl, zero_mul,
    zSign_zero, one_smul] at hS
  rw [show superBracket P p (superBracket P p (e P p i) (e P p i)) (e P p i) =
    -superBracket P p (e P p i) (superBracket P p (e P p i) (e P p i)) by rw [hS, neg_neg]] at hJ
  set X := superBracket P p (e P p i) (superBracket P p (e P p i) (e P p i))
  rcases zmod_two_cases (p i) with h0 | h1
  · rw [h0, mul_zero, zSign_zero] at hJ
    linear_combination (norm := module) hJ
  · rw [h1, mul_one, zSign_one] at hJ
    have h3 : (3 : K) • X = 0 := by linear_combination (norm := module) hJ
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)

lemma eLie_replicate_eq_zero (i : ι) {n : ℕ} (hn : 2 ≤ n) :
    eLie P p i (List.replicate n i) = 0 := by
  induction n, hn using Nat.le_induction with
  | base => simpa using superBracket_e_superBracket_e_e P p i
  | succ n _ ih =>
    rw [List.replicate_succ, eLie_cons, ih]
    exact (superBracketRight P p (e P p i)).map_zero

/-- `G̃_{mαᵢ} = 0` for `m ≥ 3`. -/
theorem eq_zero_of_mem_weightSpace_nsmul_root {i : ι} {m : ℕ} (hm : 3 ≤ m)
    {x : P.SuperEnveloping p} (hx : x ∈ gTilde P p) (hxi : x ∈ weightSpace P p (m • P.root i)) :
    x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have := mem_weightSpace_nsmul_root P p hx hxi
  rwa [eLie_replicate_eq_zero P p i (by omega), Submodule.span_singleton_eq_bot.2 rfl,
    Submodule.mem_bot] at this

end SuperEnveloping

end Matrix.Realization
