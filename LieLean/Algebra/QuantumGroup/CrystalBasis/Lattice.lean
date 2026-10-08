/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.KashiwaraOperators
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Lattices stable under the Kashiwara operators

Let `M` be an integrable `U_q(𝔰𝔩₂)`-module (`QuantumGroup.IntegrableSl2`) over a field `k`, `A` a
commutative ring with `k` an `A`-algebra and `M` an `A`-module compatibly (`IsScalarTower A k M`).
Typically `A = A₀ ⊆ k = F(q)` is the ring of rational functions regular at `q = 0`, but nothing
about `A` is needed here. An `A`-submodule `L ⊆ M` is *Kashiwara-stable*
(`IntegrableSl2.IsKashiwaraStable`) if it is graded (`L = ⊕ₙ L ∩ Mⁿ`) and `ẽ L ⊆ L`, `f̃ L ⊆ L`;
these are the conditions (2), (3) of a crystal lattice ([HK] Def. 4.2.2).

## Main results

* `IntegrableSl2.IsKashiwaraStable.mem_of_sum_mem`: if `u = Σⱼ F^{(j)} ηⱼ ∈ L ∩ Mⁿ` is the string
  decomposition, every `ηⱼ` lies in `L` ([HK] Prop. 4.2.11 (1));
* `IntegrableSl2.IsKashiwaraStable.mem_smul_of_eTilde_mem`: if moreover `ẽ u ∈ c L`, then `ηⱼ ∈ c L`
  for `j ≥ 1` ([HK] Prop. 4.2.11 (2));
* `IntegrableSl2.IsKashiwaraStable.exists_of_mk_mem`: if `B ⊆ L / cL` is a set of nonzero
  vectors with `ẽ B, f̃ B ⊆ B ∪ {0}` and `f̃ b = b' ↔ ẽ b' = b` on `B`, and the class of `u` lies
  in `B`, then exactly one `ηₖ` is nonzero modulo `cL`, its class lies in `B`, and `u ≡ F^{(k)} ηₖ`
  ([HK] Prop. 4.2.11 (3)).

The induced operators on `L / cL` are `IntegrableSl2.eTildeQ`, `IntegrableSl2.fTildeQ`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.2.
-/

open Finset Pointwise

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M} (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]

/-! ### Iterates of the Kashiwara operators on strings -/

include hq0 hq in
/-- `f̃ʲ η = F^{(j)} η` for `η` primitive. -/
lemma fTilde_pow_apply {p : ℤ} {η : M} (hη : η ∈ V.prim p) (j : ℕ) :
    (V.fTilde hq0 hq ^ j) η = V.dF j η := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, fTilde_dF hq0 hq hη.2 hη.1]

include hq0 hq in
/-- `ẽ (Σ_{j ≤ N} F^{(j)} ηⱼ) = Σ_{j < N} F^{(j)} η_{j+1}` for a string decomposition. -/
lemma eTilde_sum {n : ℤ} {η : ℕ → M} (h1 : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j))
    (h2 : ∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) (N : ℕ) :
    V.eTilde hq0 hq (∑ j ∈ range (N + 1), V.dF j (η j)) =
      ∑ j ∈ range N, V.dF j (η (j + 1)) := by
  rw [map_sum, sum_range_succ', dF_zero, eTilde_of_primitive hq0 hq (h1 0).2 (h1 0).1,
    add_zero]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases h0 : η (j + 1) = 0
  · simp [h0]
  · have := h2 _ h0
    exact eTilde_dF_succ hq0 hq (h1 (j + 1)).2 (h1 (j + 1)).1 (by push_cast at this ⊢; omega)

lemma prim_shift {n : ℤ} {η : ℕ → M} (h1 : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j)) (j : ℕ) :
    η (j + 1) ∈ V.prim (n + 2 + 2 * j) := by
  convert h1 (j + 1) using 2; push_cast; ring

lemma norm_shift {n : ℤ} {η : ℕ → M} (h2 : ∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) (j : ℕ)
    (h : η (j + 1) ≠ 0) : 0 ≤ n + 2 + j := by
  have := h2 _ h; push_cast at this; omega

/-! ### Kashiwara-stable submodules -/

variable (V) in
/-- An `A`-submodule `L` of `M` is Kashiwara-stable if it is graded and stable under `ẽ`, `f̃`
(conditions (2), (3) of [HK] Def. 4.2.2). -/
structure IsKashiwaraStable (L : Submodule A M) : Prop where
  wtProj_mem : ∀ m ∈ L, ∀ n, V.wtProj n m ∈ L
  eTilde_mem : ∀ m ∈ L, V.eTilde hq0 hq m ∈ L
  fTilde_mem : ∀ m ∈ L, V.fTilde hq0 hq m ∈ L

variable {hq0 hq} {L : Submodule A M}

lemma _root_.LinearMap.map_mem_smul_of_mem {f : Module.End k M} (c : A)
    (hf : ∀ m ∈ L, f m ∈ L) {m : M} (hm : m ∈ c • L) : f m ∈ c • L := by
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (hf x hx)

/-- If `L` is Kashiwara-stable then so is `c L`. -/
lemma IsKashiwaraStable.smul (hL : V.IsKashiwaraStable hq0 hq L) (c : A) :
    V.IsKashiwaraStable hq0 hq (c • L) where
  wtProj_mem _ hm n := LinearMap.map_mem_smul_of_mem c (fun m hm ↦ hL.wtProj_mem m hm n) hm
  eTilde_mem _ hm := LinearMap.map_mem_smul_of_mem c hL.eTilde_mem hm
  fTilde_mem _ hm := LinearMap.map_mem_smul_of_mem c hL.fTilde_mem hm

omit [Algebra A k] [IsScalarTower A k M] in
lemma IsKashiwaraStable.fTilde_pow_mem (hL : V.IsKashiwaraStable hq0 hq L) (j : ℕ) {m : M}
    (hm : m ∈ L) : (V.fTilde hq0 hq ^ j) m ∈ L := by
  induction j with
  | zero => simpa using hm
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact hL.fTilde_mem _ ih

omit [Algebra A k] [IsScalarTower A k M] in
lemma IsKashiwaraStable.dF_mem (hL : V.IsKashiwaraStable hq0 hq L) {p : ℤ} {η : M}
    (hη : η ∈ V.prim p) (hηL : η ∈ L) (j : ℕ) : V.dF j η ∈ L := by
  rw [← fTilde_pow_apply hq0 hq hη]
  exact hL.fTilde_pow_mem j hηL

omit [Algebra A k] [IsScalarTower A k M] in
/-- [HK] Prop. 4.2.11 (1): the vectors of the string decomposition of an element of `L` lie in
`L`. -/
theorem IsKashiwaraStable.mem_of_sum_mem (hL : V.IsKashiwaraStable hq0 hq L) (N : ℕ) :
    ∀ (n : ℤ) (η : ℕ → M), (∀ j : ℕ, η j ∈ V.prim (n + 2 * j)) →
      (∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) → ∑ j ∈ range N, V.dF j (η j) ∈ L →
      ∀ j < N, η j ∈ L := by
  induction N with
  | zero => intro _ _ _ _ _ j hj; omega
  | succ N ih =>
    intro n η h1 h2 hu
    have he := hL.eTilde_mem _ hu
    rw [eTilde_sum hq0 hq h1 h2] at he
    have hsucc := ih (n + 2) (fun j ↦ η (j + 1)) (prim_shift h1) (norm_shift h2) he
    intro j hj
    rcases j with _ | j
    · rw [sum_range_succ'] at hu
      have hrest : ∑ j ∈ range N, V.dF (j + 1) (η (j + 1)) ∈ L :=
        Submodule.sum_mem _ fun j hj ↦ hL.dF_mem (h1 (j + 1)) (hsucc j (mem_range.1 hj)) _
      simpa using sub_mem hu hrest
    · exact hsucc j (by omega)

/-- [HK] Prop. 4.2.11 (2): if `ẽ u ∈ c L` then `ηⱼ ∈ c L` for `j ≥ 1`. -/
theorem IsKashiwaraStable.mem_smul_of_eTilde_mem (hL : V.IsKashiwaraStable hq0 hq L) (c : A)
    {n : ℤ} {η : ℕ → M} (h1 : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j))
    (h2 : ∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) {N : ℕ}
    (he : V.eTilde hq0 hq (∑ j ∈ range (N + 1), V.dF j (η j)) ∈ c • L) :
    ∀ j < N, η (j + 1) ∈ c • L := by
  rw [eTilde_sum hq0 hq h1 h2] at he
  exact (hL.smul c).mem_of_sum_mem N (n + 2) _ (prim_shift h1) (norm_shift h2) he

/-! ### The operators on `L / c L` -/

variable (V hq0 hq) in
/-- `ẽ` on `L / c L`, for `L` stable under `ẽ`. -/
noncomputable def eTildeQ (hL : ∀ m ∈ L, V.eTilde hq0 hq m ∈ L) (c : A) :
    (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) →ₗ[A] (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) :=
  Submodule.mapQ _ _ (((V.eTilde hq0 hq).restrictScalars A).restrict hL) fun x hx ↦ by
    rw [Submodule.ideal_span_singleton_smul] at hx ⊢
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

variable (V hq0 hq) in
/-- `f̃` on `L / c L`, for `L` stable under `f̃`. -/
noncomputable def fTildeQ (hL : ∀ m ∈ L, V.fTilde hq0 hq m ∈ L) (c : A) :
    (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) →ₗ[A] (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) :=
  Submodule.mapQ _ _ (((V.fTilde hq0 hq).restrictScalars A).restrict hL) fun x hx ↦ by
    rw [Submodule.ideal_span_singleton_smul] at hx ⊢
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

lemma eTildeQ_mk (hL : ∀ m ∈ L, V.eTilde hq0 hq m ∈ L) (c : A) (x : L) :
    V.eTildeQ hq0 hq hL c (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨V.eTilde hq0 hq x, hL x x.2⟩ := rfl

lemma fTildeQ_mk (hL : ∀ m ∈ L, V.fTilde hq0 hq m ∈ L) (c : A) (x : L) :
    V.fTildeQ hq0 hq hL c (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨V.fTilde hq0 hq x, hL x x.2⟩ := rfl

/-- Membership in `c L`, seen in `L`. -/
lemma mem_span_smul_top_iff (c : A) (x : L) :
    x ∈ (Ideal.span {c} • ⊤ : Submodule A L) ↔ (x : M) ∈ c • L := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, y.2, rfl⟩
  · rintro ⟨y, hy, h⟩; exact ⟨⟨y, hy⟩, Submodule.mem_top, Subtype.ext h⟩

lemma mk_eq_mk_iff (c : A) (x y : L) :
    (Submodule.Quotient.mk x : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) =
      Submodule.Quotient.mk y ↔ (x : M) - y ∈ c • L := by
  rw [Submodule.Quotient.eq, mem_span_smul_top_iff, Submodule.coe_sub]

lemma mk_eq_zero_iff (c : A) (x : L) :
    (Submodule.Quotient.mk x : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) = 0 ↔
      (x : M) ∈ c • L := by
  rw [Submodule.Quotient.mk_eq_zero, mem_span_smul_top_iff]

lemma smul_le (c : A) : c • L ≤ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  exact L.smul_mem c hy

/-- [HK] Prop. 4.2.11 (3): let `B ⊆ L / c L` be a set of nonzero vectors with
`ẽ B, f̃ B ⊆ B ∪ {0}` and `f̃ b = b' ↔ ẽ b' = b` for `b, b' ∈ B`. If `u = Σ_{j<N} F^{(j)} ηⱼ ∈ L`
is a string decomposition and the class of `u` lies in `B`, then there is `k` with `ηₖ ∈ L`, the
class of `ηₖ` in `B`, `ηⱼ ∈ c L` for `j ≠ k` and `u ≡ F^{(k)} ηₖ` modulo `c L`. -/
theorem IsKashiwaraStable.exists_of_mk_mem (hL : V.IsKashiwaraStable hq0 hq L) (c : A)
    (B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))) (hB0 : 0 ∉ B)
    (hBe : ∀ b ∈ B, V.eTildeQ hq0 hq hL.eTilde_mem c b ∈ B ∨
      V.eTildeQ hq0 hq hL.eTilde_mem c b = 0)
    (hBef : ∀ b ∈ B, ∀ b' ∈ B, V.fTildeQ hq0 hq hL.fTilde_mem c b = b' ↔
      V.eTildeQ hq0 hq hL.eTilde_mem c b' = b) (N : ℕ) :
    ∀ (n : ℤ) (η : ℕ → M) (_ : ∀ j : ℕ, η j ∈ V.prim (n + 2 * j))
      (_ : ∀ j : ℕ, η j ≠ 0 → 0 ≤ n + j) (hu : ∑ j ∈ range N, V.dF j (η j) ∈ L),
      Submodule.Quotient.mk ⟨_, hu⟩ ∈ B →
      ∃ k < N, ∃ hk : η k ∈ L, Submodule.Quotient.mk ⟨η k, hk⟩ ∈ B ∧
        (∀ j < N, j ≠ k → η j ∈ c • L) ∧
        ∑ j ∈ range N, V.dF j (η j) - V.dF k (η k) ∈ c • L := by
  induction N with
  | zero =>
    intro n η _ _ hu hB
    simp only [range_zero, sum_empty] at hu hB
    exact (hB0 hB).elim
  | succ N ih =>
    intro n η h1 h2 hu hB
    set u := ∑ j ∈ range (N + 1), V.dF j (η j)
    have hηL := hL.mem_of_sum_mem (N + 1) n η h1 h2 hu
    have heu := hL.eTilde_mem u hu
    have heq : V.eTilde hq0 hq u = ∑ j ∈ range N, V.dF j (η (j + 1)) :=
      eTilde_sum hq0 hq h1 h2 N
    by_cases hc : V.eTilde hq0 hq u ∈ c • L
    · -- `k = 0`
      have hη1 := hL.mem_smul_of_eTilde_mem c h1 h2 hc
      have hrest : ∑ j ∈ range N, V.dF (j + 1) (η (j + 1)) ∈ c • L :=
        Submodule.sum_mem _ fun j hj ↦
          (hL.smul c).dF_mem (h1 (j + 1)) (hη1 j (mem_range.1 hj)) _
      have hu0 : u - V.dF 0 (η 0) ∈ c • L := by
        simp only [u, sum_range_succ', dF_zero, add_sub_cancel_right]
        exact hrest
      refine ⟨0, Nat.succ_pos N, hηL 0 (Nat.succ_pos N), ?_, fun j hj hj0 ↦ ?_, hu0⟩
      · convert hB using 1
        refine ((mk_eq_mk_iff c _ _).2 ?_).symm
        simpa using hu0
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        exact hη1 j (by omega)
    · -- `ẽ u ≢ 0`: apply the induction hypothesis to `ẽ u`
      have hb' : Submodule.Quotient.mk ⟨_, heu⟩ ∈ B := by
        rcases hBe _ hB with h | h
        · exact h
        · exact absurd ((mk_eq_zero_iff c _).1 h) hc
      have hu' : ∑ j ∈ range N, V.dF j (η (j + 1)) ∈ L := heq ▸ heu
      have hb'' : Submodule.Quotient.mk ⟨_, hu'⟩ ∈ B := by
        convert hb' using 3; exact heq.symm
      obtain ⟨k, hkN, hk, hkB, hkc, hkmod⟩ :=
        ih (n + 2) (fun j ↦ η (j + 1)) (prim_shift h1) (norm_shift h2) hu' hb''
      -- `u ≡ f̃ ẽ u ≡ F^{(k+1)} η_{k+1}`
      have hfe : V.fTildeQ hq0 hq hL.fTilde_mem c
          (Submodule.Quotient.mk ⟨_, heu⟩) = Submodule.Quotient.mk ⟨u, hu⟩ :=
        (hBef _ hb' _ hB).2 rfl
      rw [fTildeQ_mk] at hfe
      have h3 : V.fTilde hq0 hq (V.eTilde hq0 hq u) - u ∈ c • L :=
        (mk_eq_mk_iff c _ _).1 hfe
      have h4 : V.fTilde hq0 hq (V.eTilde hq0 hq u) - V.dF (k + 1) (η (k + 1)) ∈ c • L := by
        have := LinearMap.map_mem_smul_of_mem c hL.fTilde_mem hkmod
        rwa [map_sub, fTilde_dF hq0 hq (h1 (k + 1)).2 (h1 (k + 1)).1, ← heq] at this
      have hmod : u - V.dF (k + 1) (η (k + 1)) ∈ c • L := by
        have := sub_mem h4 h3
        rwa [sub_sub_sub_cancel_left] at this
      refine ⟨k + 1, by omega, hk, hkB, fun j hj hjk ↦ ?_, hmod⟩
      rcases j with _ | j
      · -- `η₀ = u - Σ_{j ≥ 1} F^{(j)} ηⱼ`
        have hη0 : η 0 = (u - V.dF (k + 1) (η (k + 1))) -
            ∑ j ∈ (range N).erase k, V.dF (j + 1) (η (j + 1)) := by
          simp only [u, sum_range_succ', dF_zero]
          rw [← add_sum_erase _ _ (mem_range.2 hkN)]
          abel
        rw [hη0]
        refine sub_mem hmod (Submodule.sum_mem _ fun j hj ↦ ?_)
        obtain ⟨hjk, hjN⟩ := mem_erase.1 hj
        exact (hL.smul c).dF_mem (h1 (j + 1)) (hkc j (mem_range.1 hjN) hjk) _
      · exact hkc j (by omega) (by omega)

end IntegrableSl2

end LieLean.QuantumGroup
