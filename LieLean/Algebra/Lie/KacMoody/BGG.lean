/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.Uniqueness
import LieLean.Algebra.Lie.KacMoody.BGG.LowDegree
import LieLean.Algebra.Lie.KacMoody.BGG.Character

/-!
# The BGG complex

Let `𝔤 = 𝔤(A)` be the Kac–Moody algebra of a generalized Cartan matrix `A` over a field `K` of
characteristic zero, `W` its Weyl group with length function `ℓ`, and `Λ` a dominant integral
weight. The **BGG complex** ([BGG] §10–11; [HumO] §6.1–6.3 (check); [Kum] §9.1 (check)) is
`⋯ → C₂ → C₁ → C₀ → 0`, `C_k = ⊕_{ℓ(w) = k} M(w · Λ)`, with differential
`d(x_{w'}) = ∑_{w ⋖ w'} ε(w, w') i_{w', w}(x_{w'})`, where `i_{w', w} : M(w' · Λ) ↪ M(w · Λ)` are
the embeddings of Verma's theorem, normalized compatibly, and `ε` are the BGG signs.

## Construction

For every `w` we choose an embedding `M(w · Λ) ↪ M(Λ)` (`bggEmb`). Since
`dim Hom(M(w' · Λ), M(Λ)) = 1` (`VermaModule.finrank_hom_weylDot_self`), the images satisfy
`M(w' · Λ) ⊆ M(w · Λ)` inside `M(Λ)` whenever `w ≤ w'` (Verma's theorem), and `i_{w', w}` is the
inclusion (`bggMap`). Hence `i_{b, w} ∘ i_{w', b} = i_{w', w}` (`bggMap_comp`), and `d² = 0`
follows from the squares lemma and the anticommutativity of the signs
(`CoxeterSystem.neg_one_pow_bruhatSign_square`).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.bggEmb`, `Matrix.Realization.KacMoodyAlgebra.bggMap`: the
  embeddings `M(w · Λ) ↪ M(Λ)` and `i_{w', w} : M(w' · Λ) ↪ M(w · Λ)` (`0` unless `w ≤ w'`).
* `Matrix.Realization.KacMoodyAlgebra.BGGTerm`: `C_k = ⊕_{ℓ(w) = k} M(w · Λ)`.
* `Matrix.Realization.KacMoodyAlgebra.bggDiff`: the differential `C_{k+1} → C_k`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.bggMap_comp`: `i_{b, w} ∘ i_{w', b} = i_{w', w}`.
* `Matrix.Realization.KacMoodyAlgebra.bggDiff_comp_bggDiff`: **`d² = 0`**.

## What is not proved

The exactness of the BGG complex (the BGG theorem, [HumO] Thm. 6.3 (check), [Kum] Thm. 9.1.3
(check)) is not proved here. Proved: exactness at `C₀` (`range_bggDiffOne` in
`LieLean.Algebra.Lie.KacMoody.BGG.LowDegree`, for the presentation of `C₁` indexed by simple
roots), and the Euler characteristic identity `∑_w (-1)^{ℓ(w)} ch M(w · Λ) = ch L(Λ)`
(`hsum_vermaAltFamily`). The standard proof of exactness uses the relative Chevalley–Eilenberg
resolution `U(𝔤) ⊗_{U(𝔟)} ⋀ᵏ(𝔤/𝔟) ⊗ L(Λ)` of `L(Λ)`, its filtration by Verma modules, and the
Casimir operator to split off the block of `Λ`.

## References

* [BGG] I. N. Bernstein, I. M. Gelfand, S. I. Gelfand, *Differential operators on the base
  affine space and a study of 𝔤-modules*, Lie groups and their representations (Budapest, 1971),
  Halsted 1975, 21–64.
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Ch. 6.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §9.1 (check).
-/

open Module LieModule CoxeterSystem DirectSum

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsGeneralizedCartan)
  {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

local notation "W" => P.weylGroup hA
local notation "cs" => P.coxeterSystem hA

/-! ### Compatible embeddings -/

include hΛ in
lemma exists_injective_weylDot_self (w : W) :
    ∃ φ : VermaModule P (P.weylDot hA w Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ,
      Function.Injective φ := by
  have := exists_injective_of_bruhatLE hA hΛ ((cs).one_bruhatLE w)
  rwa [weylDot_one] at this

/-- A chosen embedding `M(w · Λ) ↪ M(Λ)` (unique up to a scalar,
`VermaModule.finrank_hom_weylDot_self`). -/
def bggEmb (w : W) : VermaModule P (P.weylDot hA w Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ :=
  (exists_injective_weylDot_self P hA hΛ w).choose

lemma bggEmb_injective (w : W) : Function.Injective (bggEmb P hA hΛ w) :=
  (exists_injective_weylDot_self P hA hΛ w).choose_spec

/-- For `w ≤ w'`, the image of `M(w' · Λ)` in `M(Λ)` lies in the image of `M(w · Λ)`. -/
lemma bggEmb_mem_range {w w' : W} (h : (cs).BruhatLE w w') (m : VermaModule P (P.weylDot hA w' Λ)) :
    bggEmb P hA hΛ w' m ∈ (bggEmb P hA hΛ w).range := by
  obtain ⟨ψ, hψ⟩ := exists_injective_of_bruhatLE hA hΛ h
  have hne : bggEmb P hA hΛ w' ≠ 0 := fun h0 ↦ hwv_ne_zero P _
    (bggEmb_injective P hA hΛ w' (by rw [h0, map_zero, _root_.zero_apply]))
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp
    (finrank_hom_weylDot_self hA hΛ w') ((bggEmb P hA hΛ w).comp ψ)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hwv_ne_zero P _ (hψ (bggEmb_injective P hA hΛ w (by
      rw [← LieModuleHom.comp_apply, ← hc, map_zero, _root_.zero_apply, map_zero])))
  refine ⟨c⁻¹ • ψ m, ?_⟩
  rw [map_smul, ← LieModuleHom.comp_apply, ← hc, _root_.smul_apply, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]

open Classical in
/-- The embeddings `i_{w', w} : M(w' · Λ) ↪ M(w · Λ)` of the BGG complex, compatible with the
chosen embeddings into `M(Λ)` (`bggEmb_comp_bggMap`); `0` unless `w ≤ w'`. -/
def bggMap (w' w : W) :
    VermaModule P (P.weylDot hA w' Λ) →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P (P.weylDot hA w Λ) :=
  if h : (cs).BruhatLE w w' then
    (homEquiv P _ _).symm ⟨(bggEmb_mem_range P hA hΛ h (hwv P _)).choose,
      mem_primitiveVectors_of_injective _ (bggEmb_injective P hA hΛ w) (by
        rw [(bggEmb_mem_range P hA hΛ h (hwv P _)).choose_spec]
        exact map_hwv_mem_primitiveVectors P _)⟩
  else 0

open Classical in
lemma bggEmb_comp_bggMap {w w' : W} (h : (cs).BruhatLE w w') :
    (bggEmb P hA hΛ w).comp (bggMap P hA hΛ w' w) = bggEmb P hA hΛ w' := by
  refine hom_ext P _ ?_
  rw [LieModuleHom.comp_apply, bggMap, dite_eq_left h, ← homEquiv_apply,
    LinearEquiv.apply_symm_apply]
  exact (bggEmb_mem_range P hA hΛ h (hwv P _)).choose_spec

lemma bggMap_injective {w w' : W} (h : (cs).BruhatLE w w') :
    Function.Injective (bggMap P hA hΛ w' w) := by
  intro m m' hm
  apply bggEmb_injective P hA hΛ w'
  rw [← bggEmb_comp_bggMap P hA hΛ h, LieModuleHom.comp_apply, LieModuleHom.comp_apply, hm]

/-- **Compatibility of the BGG embeddings**: `i_{b, w} ∘ i_{w', b} = i_{w', w}` for
`w ≤ b ≤ w'`. -/
theorem bggMap_comp {w b w' : W} (h₁ : (cs).BruhatLE w b) (h₂ : (cs).BruhatLE b w') :
    (bggMap P hA hΛ b w).comp (bggMap P hA hΛ w' b) = bggMap P hA hΛ w' w := by
  refine LieModuleHom.ext fun m ↦ bggEmb_injective P hA hΛ w ?_
  rw [LieModuleHom.comp_apply, ← LieModuleHom.comp_apply (bggEmb P hA hΛ w),
    bggEmb_comp_bggMap P hA hΛ h₁, ← LieModuleHom.comp_apply (bggEmb P hA hΛ b),
    bggEmb_comp_bggMap P hA hΛ h₂, ← LieModuleHom.comp_apply (bggEmb P hA hΛ w),
    bggEmb_comp_bggMap P hA hΛ (h₁.trans h₂)]

/-! ### The complex -/

variable (Λ) in
/-- The term `C_k = ⊕_{ℓ(w) = k} M(w · Λ)` of the BGG complex. -/
abbrev BGGTerm (k : ℕ) : Type _ :=
  ⨁ w : {w : W // (cs).length w = k}, VermaModule P (P.weylDot hA w Λ)

/-- The elements `w ⋖ w'` of length `k`. -/
def bggBoundary (w' : W) (k : ℕ) : Finset {w : W // (cs).length w = k} :=
  Set.Finite.toFinset (s := {w | (cs).BruhatCovBy (w : W) w'})
    ((((cs).finite_setOf_bruhatLE w').preimage Subtype.val_injective.injOn).subset
      fun _ hw ↦ hw.1)

lemma mem_bggBoundary {w' : W} {k : ℕ} {w : {w : W // (cs).length w = k}} :
    w ∈ bggBoundary P hA w' k ↔ (cs).BruhatCovBy w w' := by
  rw [bggBoundary, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- The BGG sign `(-1)^{ε(w, w')}`. -/
def bggSign (w w' : W) : K := (-1) ^ ((cs).bruhatSign w w').val

open Classical in
/-- The differential `d : C_{k+1} → C_k`, `d(x_{w'}) = ∑_{w ⋖ w'} ε(w, w') i_{w', w}(x_{w'})`. -/
def bggDiff (k : ℕ) : BGGTerm P hA Λ (k + 1) →ₗ⁅K,P.KacMoodyAlgebra⁆ BGGTerm P hA Λ k :=
  DirectSum.toLieModule fun w' ↦ ∑ w ∈ bggBoundary P hA w' k,
    bggSign P hA w w' • (DirectSum.lieModuleOf K _ P.KacMoodyAlgebra
      (fun w : {w : W // (cs).length w = k} ↦ VermaModule P (P.weylDot hA w Λ)) w).comp
      (bggMap P hA hΛ w' w)

omit [CharZero K] in
lemma _root_.LieModuleHom.finset_sum_apply {R L M N κ : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M] [AddCommGroup N]
    [Module R N] [LieRingModule L N] (s : Finset κ) (φ : κ → M →ₗ⁅R,L⁆ N) (x : M) :
    (∑ i ∈ s, φ i) x = ∑ i ∈ s, φ i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, _root_.add_apply, ih]

open Classical in
lemma bggDiff_of (k : ℕ) (w' : {w : W // (cs).length w = k + 1})
    (x : VermaModule P (P.weylDot hA w' Λ)) :
    bggDiff P hA hΛ k (DirectSum.of _ w' x) = ∑ w ∈ bggBoundary P hA w' k,
      bggSign P hA w w' • DirectSum.of (fun w : {w : W // (cs).length w = k} ↦
        VermaModule P (P.weylDot hA w Λ)) w (bggMap P hA hΛ w' w x) := by
  rw [bggDiff, DirectSum.toLieModule_of, LieModuleHom.finset_sum_apply]
  rfl

open Classical in
/-- The scalar identity behind `d² = 0`: for `ℓ(w'') = ℓ(w) + 2`, the signed count of the
elements `w ⋖ b ⋖ w''` vanishes (the squares lemma). -/
lemma sum_bggSign_mul_bggSign {k : ℕ} (w'' : {w : W // (cs).length w = k + 2})
    (w₀ : {w : W // (cs).length w = k}) :
    ∑ b ∈ (bggBoundary P hA w'' (k + 1)).filter
      (fun b : {w : W // (cs).length w = k + 1} ↦ w₀ ∈ bggBoundary P hA b k),
      bggSign P hA b w'' * bggSign P hA w₀ b = 0 := by
  generalize hTdef : (bggBoundary P hA w'' (k + 1)).filter
    (fun b : {w : W // (cs).length w = k + 1} ↦ w₀ ∈ bggBoundary P hA b k) = T
  have hT : ∀ b ∈ T, (cs).BruhatCovBy w₀ b ∧ (cs).BruhatCovBy b w'' := fun b hb ↦ by
    rw [← hTdef, Finset.mem_filter, mem_bggBoundary, mem_bggBoundary] at hb
    exact ⟨hb.2, hb.1⟩
  rcases T.eq_empty_or_nonempty with hTe | ⟨b, hb⟩
  · rw [hTe, Finset.sum_empty]
  obtain ⟨hb₁, hb₂⟩ := hT b hb
  obtain ⟨c₁, c₂, hc, hmid⟩ := (cs).exists_middle_pair (hb₁.1.trans hb₂.1)
    (by rw [hb₂.2, hb₁.2])
  have hl : ∀ c, (c = c₁ ∨ c = c₂) → (cs).length c = k + 1 := fun c hc' ↦ by
    rw [((hmid c).mpr hc').1.2, w₀.2]
  have hTeq : T = {⟨c₁, hl c₁ (.inl rfl)⟩, ⟨c₂, hl c₂ (.inr rfl)⟩} := by
    ext b'
    rw [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff (a1 := b'),
      Subtype.ext_iff (a1 := b')]
    constructor
    · intro hb'
      exact (hmid b').mp (hT b' hb')
    · intro hb'
      obtain ⟨h₁, h₂⟩ := (hmid b').mpr hb'
      rw [← hTdef, Finset.mem_filter, mem_bggBoundary, mem_bggBoundary]
      exact ⟨h₂, h₁⟩
  rw [hTeq, Finset.sum_pair (fun h ↦ hc (congrArg Subtype.val h))]
  have hsq := (cs).neg_one_pow_bruhatSign_square (R := K) ((hmid c₁).mpr (.inl rfl)).1
    ((hmid c₁).mpr (.inl rfl)).2 ((hmid c₂).mpr (.inr rfl)).1 ((hmid c₂).mpr (.inr rfl)).2 hc
  simp only [bggSign]
  rw [mul_comm, mul_comm ((-1 : K) ^ ((cs).bruhatSign c₂ w'').val), hsq]

/-- **`d² = 0`** for the BGG complex ([BGG] §11 (check), [HumO] §6.2 (check)). -/
theorem bggDiff_comp_bggDiff (k : ℕ) :
    (bggDiff P hA hΛ k).comp (bggDiff P hA hΛ (k + 1)) = 0 := by
  classical
  ext1 m
  induction m using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | add m m' hm hm' => rw [map_add, hm, hm', map_add]
  | of w'' x =>
  rw [LieModuleHom.comp_apply, bggDiff_of, map_sum, _root_.zero_apply]
  simp_rw [map_smul, bggDiff_of, Finset.smul_sum, smul_smul]
  -- use `i_{b, w} ∘ i_{w'', b} = i_{w'', w}`
  have hcomp : ∀ b ∈ bggBoundary P hA w'' (k + 1), ∀ w ∈ bggBoundary P hA b k,
      bggMap P hA hΛ b w (bggMap P hA hΛ w'' b x) = bggMap P hA hΛ w'' w x := by
    intro b hb w hw
    rw [mem_bggBoundary] at hb hw
    rw [← LieModuleHom.comp_apply, bggMap_comp P hA hΛ hw.1 hb.1]
  rw [Finset.sum_congr rfl fun b hb ↦ Finset.sum_congr rfl fun w hw ↦ by rw [hcomp b hb w hw]]
  -- exchange the sums
  rw [Finset.sum_comm' (t' := (bggBoundary P hA w'' (k + 1)).biUnion
      fun b : {w : W // (cs).length w = k + 1} ↦ bggBoundary P hA b k)
    (s' := fun w ↦ (bggBoundary P hA w'' (k + 1)).filter
      fun b : {w : W // (cs).length w = k + 1} ↦ w ∈ bggBoundary P hA b k)
    (fun b w ↦ by
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      exact ⟨fun ⟨hb, hw⟩ ↦ ⟨⟨hb, hw⟩, b, hb, hw⟩, fun ⟨⟨hb, hw⟩, _⟩ ↦ ⟨hb, hw⟩⟩)]
  refine Finset.sum_eq_zero fun w₀ _ ↦ ?_
  rw [← Finset.sum_smul]
  rw [sum_bggSign_mul_bggSign P hA w'' w₀]
  exact zero_smul K _

end Matrix.Realization.KacMoodyAlgebra
