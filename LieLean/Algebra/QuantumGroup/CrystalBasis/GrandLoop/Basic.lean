/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.LocalTensorRule

/-!
# Kashiwara's grand loop: setting and the string lemma

We set up the inductive statements of Kashiwara's grand-loop argument ([HK] §5.3) for the
irreducible modules `V(λ) = L_q(λ)` (`λ` dominant) of `U = U_q(𝔤)`, with `v` transcendental over
`ℚ`, and their lattices `L(λ) = Σ A f̃_{i₁} ⋯ f̃_{iᵣ} v_λ`. The *depth* of a weight `λ - Σ νᵢ αᵢ` is
`Σ νᵢ`; the statements are indexed by the depth `r`:

* `PropA r`: `ẽᵢ L(λ)_{λ-ν} ⊆ L(λ)` for `|ν| = r`;
* `PropB r`: `ẽᵢ` maps the class of `f̃_{i₁} ⋯ f̃_{iᵣ} v_λ` modulo `ϖ L(λ)` to `0` or to the
  class of some `f̃_{j₁} ⋯ f̃_{j_s} v_λ`;
* `PropC r`: for `b`, `b'` in `B(λ)` of depths `r - 1`, `r`: `f̃ᵢ b = b' ↔ b = ẽᵢ b'`.

The main result here is the string lemma ([HK] Lemma 5.3.1 (2)) in the form needed later: if `A`,
`B`, `C` hold up to depth `d`, then every `x ∈ L(λ)` of depth `d` congruent modulo `ϖ L(λ)` to
some `f̃_{i₁} ⋯ f̃_{i_d} v_λ` and not in `ϖ L(λ)` is congruent to `Fᵢ^{(k)} u` with `u ∈ L(λ)`
killed by `Eᵢ` (`QuantumGroup.GrandLoop.exists_string`).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §5.3.
-/

open Finset Pointwise

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]

variable (R) in
/-- Dominant weights. -/
abbrev Dom : Type _ := {Λ : Y →+ ℤ // ∀ i, 0 ≤ Λ (R.coroot i)}

instance : Add (Dom R) :=
  ⟨fun a b ↦ ⟨a.1 + b.1, fun i ↦ by rw [AddMonoidHom.add_apply]; exact add_nonneg (a.2 i) (b.2 i)⟩⟩

omit [DecidableEq I] in
@[simp] lemma Dom.add_val (a b : Dom R) : (a + b).1 = a.1 + b.1 := rfl

variable (hvt : Transcendental ℚ v) (hR : R.IsXRegular) (A : Type*) [CommRing A] [Algebra A k]
  (ϖ : A)

section Defs

include hvt hR

/-- `L(λ)`. -/
abbrev lat (Λ : Dom R) : Submodule A (IrreducibleModule R v Λ.1) :=
  IrreducibleModule.lattice hR (pow_ne_one_of_transcendental' hvt) Λ.2 A

/-- `f̃_{i₁} ⋯ f̃_{iᵣ} v_λ`. -/
abbrev fW (Λ : Dom R) (w : List I) : IrreducibleModule R v Λ.1 :=
  IrreducibleModule.fWord hR (pow_ne_one_of_transcendental' hvt) Λ.2 w

/-- `V(λ)` is integrable. -/
lemma isInt (Λ : Dom R) : IsIntegrable R v (IrreducibleModule R v Λ.1) :=
  IrreducibleModule.isIntegrable hR (pow_ne_one_of_transcendental' hvt) Λ.2

/-- `ẽᵢ` on `V(λ)`. -/
abbrev eK (Λ : Dom R) (i : I) : Module.End k (IrreducibleModule R v Λ.1) :=
  kashiwaraE R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i

/-- `f̃ᵢ` on `V(λ)`. -/
abbrev fK (Λ : Dom R) (i : I) : Module.End k (IrreducibleModule R v Λ.1) :=
  kashiwaraF R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i

end Defs

/-- The weight space of depth `ν`. -/
abbrev wsp (Λ : Dom R) (ν : I →₀ ℕ) : Submodule k (IrreducibleModule R v Λ.1) :=
  weightSpace R v (IrreducibleModule R v Λ.1) (Λ.1 - R.rootSum ν)

/-- `A(r)`: `ẽᵢ L(λ)_{λ-ν} ⊆ L(λ)` for `|ν| = r`. -/
def PropA (r : ℕ) : Prop :=
  ∀ (Λ : Dom R) (ν : I →₀ ℕ), ν.degree = r → ∀ i, ∀ x ∈ lat hvt hR A Λ, x ∈ wsp Λ ν →
    eK hvt hR Λ i x ∈ lat hvt hR A Λ

/-- `B(r)`: `ẽᵢ B(λ) ⊆ B(λ) ∪ {0}` in depth `r`. -/
def PropB (r : ℕ) : Prop :=
  ∀ (Λ : Dom R) (w : List I), w.length = r → ∀ i,
    eK hvt hR Λ i (fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ ∨
      ∃ w' : List I, eK hvt hR Λ i (fW hvt hR Λ w) - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ

/-- `C(r)`: `f̃ᵢ b = b' ↔ b = ẽᵢ b'` for `b, b' ∈ B(λ)` of depths `r - 1`, `r`. -/
def PropC (r : ℕ) : Prop :=
  ∀ (Λ : Dom R) (i : I) (w w' : List I), w.length + 1 = r → w'.length = r →
    fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ → fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ →
    (fK hvt hR Λ i (fW hvt hR Λ w) - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ ↔
      fW hvt hR Λ w - eK hvt hR Λ i (fW hvt hR Λ w') ∈ ϖ • lat hvt hR A Λ)

/-! ### Weights and depths -/

omit [CharZero k] [DecidableEq I] in
lemma degree_wordWeight (w : List I) : (LusztigF.wordWeight w).degree = w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [LusztigF.wordWeight_cons, map_add, Finsupp.degree_single, ih, List.length_cons, add_comm]

lemma fW_mem_wsp (Λ : Dom R) (w : List I) : fW hvt hR Λ w ∈ wsp Λ (LusztigF.wordWeight w) :=
  IrreducibleModule.fWord_mem_weightSpace hR _ Λ.2 w

omit [CharZero k] in
include hR in
/-- A nonzero vector of `V(λ)` of weight `λ - ν + j αᵢ` has `ν = ν' + j i` for some `ν'`. -/
lemma exists_eq_add_single (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (Λ : Dom R) {ν : I →₀ ℕ} {i : I}
    {j : ℕ} {x : IrreducibleModule R v Λ.1}
    (hx : x ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + j • R.root i)) (hx0 : x ≠ 0) :
    ∃ ν', ν = ν' + Finsupp.single i j := by
  obtain ⟨ν', hν'⟩ := IrreducibleModule.exists_eq_sub_rootSum hv' hx hx0
  refine ⟨ν', LusztigCartanDatum.RootDatum.rootSum_injective hR ?_⟩
  rw [R.rootSum_add, R.rootSum_single]
  calc R.rootSum ν = Λ.1 - (Λ.1 - R.rootSum ν + j • R.root i) + j • R.root i := by abel
    _ = Λ.1 - (Λ.1 - R.rootSum ν') + j • R.root i := by rw [hν']
    _ = R.rootSum ν' + j • R.root i := by abel

/-! ### Gradedness -/

lemma weightSetProj_mem_lat (Λ : Dom R) (S : Set (Y →+ ℤ)) {x : IrreducibleModule R v Λ.1}
    (hx : x ∈ lat hvt hR A Λ) :
    weightSetProj (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) S x ∈ lat hvt hR A Λ :=
  IrreducibleModule.weightSetProj_mem_lattice hR _ Λ.2 A S hx

lemma weightSetProj_mem_smul_lat (Λ : Dom R) (S : Set (Y →+ ℤ)) {x : IrreducibleModule R v Λ.1}
    (hx : x ∈ ϖ • lat hvt hR A Λ) :
    weightSetProj (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) S x ∈
      ϖ • lat hvt hR A Λ :=
  LinearMap.map_mem_smul_of_mem ϖ (fun _ hm ↦ weightSetProj_mem_lat hvt hR A Λ S hm) hx

/-- If a weight vector `y ∉ ϖ L(λ)` is congruent to `f̃_w v_λ` modulo `ϖ L(λ)`, then `f̃_w v_λ` has
the same weight. -/
lemma wordWeight_eq_of_sub_mem (Λ : Dom R) {ν : I →₀ ℕ} {y : IrreducibleModule R v Λ.1}
    (hyw : y ∈ wsp Λ ν) (hy0 : y ∉ ϖ • lat hvt hR A Λ) {w : List I}
    (hyw' : y - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ) : LusztigF.wordWeight w = ν := by
  classical
  by_contra hne
  have hP := weightSetProj_mem_smul_lat hvt hR A ϖ Λ {Λ.1 - R.rootSum ν} hyw'
  rw [map_sub, weightSetProj_of_mem _ _ _ hyw, weightSetProj_of_mem _ _ _ (fW_mem_wsp hvt hR Λ w)]
  at hP
  have hne' : Λ.1 - R.rootSum (LusztigF.wordWeight w) ≠ Λ.1 - R.rootSum ν := fun h ↦
    hne (LusztigCartanDatum.RootDatum.rootSum_injective hR (sub_right_injective h))
  simp only [Set.mem_singleton_iff, ↓reduceIte, hne', sub_zero] at hP
  exact hy0 hP

/-! ### Local `ẽᵢ`-stability from `A` -/

variable {hvt hR A}

/-- From `A(s)` for `s ≤ d`: `ẽᵢ` preserves `L(λ)` on the weights `λ - ν + j αᵢ`, `|ν| = d`. -/
lemma localE {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) (Λ : Dom R) {ν : I →₀ ℕ}
    (hν : ν.degree = d) (i : I) (j : ℕ) {y : IrreducibleModule R v Λ.1}
    (hy : y ∈ lat hvt hR A Λ)
    (hyw : y ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + j • R.root i)) :
    eK hvt hR Λ i y ∈ lat hvt hR A Λ := by
  by_cases hy0 : y = 0
  · rw [hy0, map_zero]; exact zero_mem _
  obtain ⟨ν', rfl⟩ := exists_eq_add_single hR (pow_ne_one_of_transcendental' hvt) Λ hyw hy0
  have hyw' : y ∈ wsp Λ ν' := by
    convert hyw using 2
    rw [R.rootSum_add, R.rootSum_single]
    abel
  refine hA ν'.degree ?_ Λ ν' rfl i y hy hyw'
  rw [← hν, map_add, Finsupp.degree_single]
  omega

/-- From `A(s)` for `s ≤ d`: `ẽᵢ` preserves `ϖ L(λ)` on the weights `λ - ν + j αᵢ`, `|ν| = d`. -/
lemma localE_smul {d : ℕ} (hA : ∀ s ≤ d, PropA hvt hR A s) (Λ : Dom R) {ν : I →₀ ℕ}
    (hν : ν.degree = d) (i : I) (j : ℕ) {ϖ : A} (hϖv : algebraMap A k ϖ ≠ 0)
    {y : IrreducibleModule R v Λ.1} (hy : y ∈ ϖ • lat hvt hR A Λ)
    (hyw : y ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + j • R.root i)) :
    eK hvt hR Λ i y ∈ ϖ • lat hvt hR A Λ := by
  obtain ⟨y₀, hy₀, hy₀w, rfl⟩ := TensorModule.exists_smul_weight hϖv hy hyw
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (localE hA Λ hν i j hy₀ hy₀w)

lemma kashiwaraF_mem_lat (Λ : Dom R) (i : I) {y : IrreducibleModule R v Λ.1}
    (hy : y ∈ lat hvt hR A Λ) : fK hvt hR Λ i y ∈ lat hvt hR A Λ :=
  IrreducibleModule.kashiwaraF_mem_lattice hR _ Λ.2 A i hy

lemma kashiwaraF_mem_smul_lat (Λ : Dom R) (i : I) {ϖ : A} {y : IrreducibleModule R v Λ.1}
    (hy : y ∈ ϖ • lat hvt hR A Λ) : fK hvt hR Λ i y ∈ ϖ • lat hvt hR A Λ :=
  LinearMap.map_mem_smul_of_mem ϖ (fun _ hm ↦ kashiwaraF_mem_lat Λ i hm) hy

lemma kashiwaraF_dF {Λ : Dom R} {i : I} {u : IrreducibleModule R v Λ.1} {p : ℤ}
    (hu : u ∈ nodeWt R v _ i p) (huE : E R v i • u = 0) (j : ℕ) :
    fK hvt hR Λ i ((nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF j u) =
      (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF (j + 1) u := by
  rw [← kashiwaraF_pow_of_primitive _ _ i huE hu, ← kashiwaraF_pow_of_primitive _ _ i huE hu,
    pow_succ', Module.End.mul_apply]

/-- **String lemma** ([HK] Lemma 5.3.1 (2), in the form needed later): if `A`, `B`, `C` hold up to
depth `d`, then every `x ∈ L(λ)` of depth `d` with `x ≡ f̃_w v_λ` and `x ∉ ϖ L(λ)` is congruent
to `Fᵢ^{(j)} u` modulo `ϖ L(λ)`, with `u ∈ L(λ)` of weight `wt x + j αᵢ` killed by `Eᵢ`. -/
theorem exists_string (hϖv : algebraMap A k ϖ ≠ 0) (Λ : Dom R) (i : I) (d : ℕ) :
    (∀ s ≤ d, PropA hvt hR A s) → (∀ s ≤ d, PropB hvt hR A ϖ s) →
    (∀ s ≤ d, PropC hvt hR A ϖ s) → ∀ {ν : I →₀ ℕ}, ν.degree = d →
    ∀ {x : IrreducibleModule R v Λ.1}, x ∈ lat hvt hR A Λ → x ∈ wsp Λ ν → ∀ {w : List I},
      x - fW hvt hR Λ w ∈ ϖ • lat hvt hR A Λ → x ∉ ϖ • lat hvt hR A Λ →
      ∃ (j : ℕ) (u : IrreducibleModule R v Λ.1), u ∈ lat hvt hR A Λ ∧
        u ∈ weightSpace R v _ (Λ.1 - R.rootSum ν + j • R.root i) ∧ E R v i • u = 0 ∧
        x - (nodeSl2 R v _ (pow_ne_one_of_transcendental' hvt) (isInt hvt hR Λ) i).dF j u ∈
          ϖ • lat hvt hR A Λ := by
  set hv' := pow_ne_one_of_transcendental' hvt
  set V := nodeSl2 R v _ hv' (isInt hvt hR Λ) i
  induction d with
  | zero => ?_
  | succ d ih => ?_
  all_goals
    intro hA hB hC ν hν x hx hxw w hxw' hx0
    obtain ⟨N, η, hηw, hηE, hη2, -, hxe⟩ := exists_sum_dF_weight hv' (isInt hvt hR Λ) i hxw
    have hηL := mem_of_sum_mem_weight hv' (isInt hvt hR Λ) i
      (fun _ hy ↦ kashiwaraF_mem_lat Λ i hy) N _ η hηw hηE hη2 (localE hA Λ hν i)
      (hxe ▸ hx)
    have hex0 : ¬ eK hvt hR Λ i x ∈ ϖ • lat hvt hR A Λ → ∃ ν', ν = ν' + Finsupp.single i 1 := by
      intro h
      refine exists_eq_add_single hR hv' Λ (j := 1) (x := eK hvt hR Λ i x) ?_
        fun h0 ↦ h (by rw [h0]; exact zero_mem _)
      rw [one_smul]
      exact kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i hxw
    by_cases hex : eK hvt hR Λ i x ∈ ϖ • lat hvt hR A Λ
    · -- `ẽᵢ x ∈ ϖ L`: then `x ≡ η₀`
      rcases N with _ | N
      · exact absurd (by rw [hxe, sum_range_zero]; exact zero_mem _) hx0
      have he := hex
      rw [hxe, kashiwaraE_sum hv' (isInt hvt hR Λ) i hηw hηE hη2] at he
      have hηs := mem_of_sum_mem_weight hv' (isInt hvt hR Λ) i (L := ϖ • lat hvt hR A Λ)
        (fun _ hy ↦ kashiwaraF_mem_smul_lat Λ i hy) N _ (fun j ↦ η (j + 1))
        (fun j ↦ by rw [add_assoc, ← succ_nsmul']; exact hηw (j + 1)) (fun j ↦ hηE (j + 1))
        (fun j h ↦ by
          have := hη2 _ h
          rw [AddMonoidHom.add_apply, R.root_coroot, D.cartanMatrix_self]
          push_cast at this ⊢; omega)
        (fun j y hy hyw ↦ localE_smul hA Λ hν i (j + 1) hϖv hy
          (by rwa [succ_nsmul', ← add_assoc]))
        he
      refine ⟨0, η 0, hηL 0 (by omega), by simpa using hηw 0, hηE 0, ?_⟩
      rw [hxe, sum_range_succ', IntegrableSl2.dF_zero, add_sub_cancel_right]
      refine Submodule.sum_mem _ fun j hj ↦ ?_
      rw [← kashiwaraF_pow_of_primitive hv' (isInt hvt hR Λ) i (hηE (j + 1))
        (mem_nodeWt_of_mem_add_nsmul i (hηw (j + 1)))]
      exact kashiwaraF_pow_mem hv' (isInt hvt hR Λ) i
        (fun _ hy ↦ kashiwaraF_mem_smul_lat Λ i hy) _ (hηs j (mem_range.1 hj))
    obtain ⟨ν', rfl⟩ := hex0 hex
    have hν' := hν
    rw [map_add, Finsupp.degree_single] at hν'
    first
    | omega
    | skip
  -- remaining goal: the case `ẽᵢ x ∉ ϖ L` in depth `d + 1`
  have hd : ν'.degree = d := by omega
  have hwν := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ hxw hx0 hxw'
  have hwlen : w.length = d + 1 := by rw [← degree_wordWeight, hwν, map_add,
    Finsupp.degree_single, hd]
  have hdiff : eK hvt hR Λ i x - eK hvt hR Λ i (fW hvt hR Λ w) ∈ ϖ • lat hvt hR A Λ := by
    rw [← map_sub]
    exact localE_smul hA Λ hν i 0 hϖv hxw'
      (by simpa using sub_mem hxw (hwν ▸ fW_mem_wsp hvt hR Λ w))
  obtain ⟨w', hw'⟩ := (hB (d + 1) le_rfl Λ w hwlen i).resolve_left fun h ↦
    hex (by simpa using add_mem hdiff h)
  have hex' : eK hvt hR Λ i x - fW hvt hR Λ w' ∈ ϖ • lat hvt hR A Λ := by
    simpa using add_mem hdiff hw'
  have hexw : eK hvt hR Λ i x ∈ wsp Λ ν' := by
    have := kashiwaraE_mem_weightSpace hv' (isInt hvt hR Λ) i hxw
    convert this using 2
    rw [R.rootSum_add, R.rootSum_single]
    abel
  have hexL : eK hvt hR Λ i x ∈ lat hvt hR A Λ := localE hA Λ hν i 0 hx (by simpa using hxw)
  obtain ⟨j, u, huL, huw, huE, hsub⟩ := ih (fun s hs ↦ hA s (by omega))
    (fun s hs ↦ hB s (by omega)) (fun s hs ↦ hC s (by omega)) hd hexL hexw hex' hex
  have hw'ν := wordWeight_eq_of_sub_mem hvt hR A ϖ Λ hexw hex hex'
  have hw'len : w'.length = d := by rw [← degree_wordWeight, hw'ν, hd]
  have hw'0 : fW hvt hR Λ w' ∉ ϖ • lat hvt hR A Λ := fun h ↦ hex (by simpa using add_mem hex' h)
  have hw0 : fW hvt hR Λ w ∉ ϖ • lat hvt hR A Λ := fun h ↦ hx0 (by simpa using add_mem hxw' h)
  have hCw := (hC (d + 1) le_rfl Λ i w' w (by omega) hwlen hw'0 hw0).2
    (by simpa using sub_mem hdiff hex')
  refine ⟨j + 1, u, huL, ?_, huE, ?_⟩
  · convert huw using 2
    rw [R.rootSum_add, R.rootSum_single, add_nsmul, one_nsmul]
    abel
  · have hu' := mem_nodeWt_of_mem_add_nsmul i huw
    have h1 := kashiwaraF_mem_smul_lat Λ i hsub
    have h2 := kashiwaraF_mem_smul_lat Λ i (neg_mem hex')
    rw [map_sub, kashiwaraF_dF hu' huE] at h1
    have := add_mem (add_mem (add_mem hxw' (neg_mem hCw)) h2) h1
    convert this using 1
    rw [map_neg, map_sub]
    abel

end GrandLoop

end LieLean.QuantumGroup

end
