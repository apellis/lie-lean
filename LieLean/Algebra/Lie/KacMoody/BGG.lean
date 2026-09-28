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
* `Matrix.Realization.KacMoodyAlgebra.bggAugmentation`: the augmentation `C₀ ≅ M(Λ) → L(Λ)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.bggMap_comp`: `i_{b, w} ∘ i_{w', b} = i_{w', w}`.
* `Matrix.Realization.KacMoodyAlgebra.bggDiff_comp_bggDiff`: **`d² = 0`**.
* `Matrix.Realization.KacMoodyAlgebra.bggAugmentation_surjective`,
  `Matrix.Realization.KacMoodyAlgebra.ker_bggAugmentation`: `C₁ → C₀ → L(Λ) → 0` is exact
  (symmetrizable `A`).

## Positive-degree exactness

The construction here is supplemented by `BGG/Exactness.lean`: `ker_bggDiff_eq_range`
proves exactness in every positive degree for symmetrizable `A` and finite-dimensional
Cartan space, over characteristic-zero fields. Together with `ker_bggAugmentation` and
`bggAugmentation_surjective`, this gives the augmented BGG resolution in that scope.
The proof follows the lowering-operator argument of Heckenberger–Kolb, arXiv:math/0605460,
§3.1 Proposition 3.4, and a maximal-weight/Casimir variant of their Theorem 3.2 proof.
It does not infer exactness from the Euler characteristic `hsum_vermaAltFamily` or assume
Garland–Lepowsky. Nonsymmetrizable exactness and removal of the finite-dimensional Cartan
hypothesis are not established by that theorem.

## References

* [BGG] I. N. Bernstein, I. M. Gelfand, S. I. Gelfand, *Differential operators on the base
  affine space and a study of 𝔤-modules*, Lie groups and their representations (Budapest, 1971),
  Halsted 1975, 21–64.
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, Ch. 6.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §9.1 (check).
* [GL] H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent.
  Math. 34 (1976), 37–76.
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

/-! ### The augmentation and exactness at `C₀` -/

omit [DecidableEq ι] [CharZero K] in
/-- A nonzero multiple of a morphism of Lie modules has the same image. -/
lemma _root_.LieModuleHom.range_smul_of_ne_zero {L M N : Type*} [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [AddCommGroup N]
    [Module K N] [LieRingModule L N] [LieModule K L N] (φ : M →ₗ⁅K,L⁆ N) {c : K} (hc : c ≠ 0) :
    (c • φ).range = φ.range := by
  ext n
  simp only [LieModuleHom.mem_range, _root_.smul_apply]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨c • m, map_smul φ c m⟩
  · rintro ⟨m, rfl⟩
    refine ⟨c⁻¹ • m, ?_⟩
    rw [map_smul φ c⁻¹ m, smul_smul, mul_inv_cancel₀ hc, one_smul]

omit [CharZero K] in
/-- Two nonzero morphisms `M(μ) → M(ν)` and `M(μ') → M(ν)`, `μ = μ'`, have the same image if
`dim Hom(M(μ), M(ν)) = 1`. -/
lemma range_eq_of_finrank_hom_eq_one {μ μ' ν : Dual K H} (e : μ = μ')
    (hd : finrank K (VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P ν) = 1)
    {φ : VermaModule P μ →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P ν}
    {ψ : VermaModule P μ' →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P ν} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    φ.range = ψ.range := by
  subst e
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hφ).mp hd ψ
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hψ (by rw [← hc, zero_smul])
  rw [← hc, LieModuleHom.range_smul_of_ne_zero _ hc0]

instance : Subsingleton {w : W // (cs).length w = 0} :=
  ⟨fun a b ↦ Subtype.ext (by rw [(cs).length_eq_zero_iff.mp a.2, (cs).length_eq_zero_iff.mp b.2])⟩

/-- The unique element `1` of length `0`. -/
def bggOne : {w : W // (cs).length w = 0} := ⟨1, (cs).length_one⟩

open Classical in
lemma eq_of_bggOne (x : BGGTerm P hA Λ 0) :
    x = DirectSum.of (fun w : {w : W // (cs).length w = 0} ↦ VermaModule P (P.weylDot hA w Λ))
      (bggOne P hA) (x (bggOne P hA)) := by
  ext j
  obtain rfl := Subsingleton.elim j (bggOne P hA)
  rw [DirectSum.of_eq_same]

open Classical in
/-- The map `C₀ → M(Λ)` given by the chosen embedding `M(1 · Λ) ↪ M(Λ)` (an isomorphism). -/
def bggEmbZero : BGGTerm P hA Λ 0 →ₗ⁅K,P.KacMoodyAlgebra⁆ VermaModule P Λ :=
  DirectSum.toLieModule fun w ↦ bggEmb P hA hΛ w

open Classical in
lemma bggEmbZero_of (w : {w : W // (cs).length w = 0}) (x : VermaModule P (P.weylDot hA w Λ)) :
    bggEmbZero P hA hΛ (DirectSum.of _ w x) = bggEmb P hA hΛ w x :=
  DirectSum.toLieModule_of _ _ _

lemma bggEmbZero_injective : Function.Injective (bggEmbZero P hA hΛ) := by
  intro x y hxy
  rw [eq_of_bggOne P hA x, eq_of_bggOne P hA y, bggEmbZero_of, bggEmbZero_of] at hxy
  rw [eq_of_bggOne P hA x, eq_of_bggOne P hA y, bggEmb_injective P hA hΛ _ hxy]

lemma range_bggEmb_bggOne : (bggEmb P hA hΛ (bggOne P hA)).range = ⊤ := by
  have h1 : P.weylDot hA (bggOne P hA : W) Λ = Λ := weylDot_one P hA Λ
  refine (range_eq_of_finrank_hom_eq_one P h1 (finrank_hom_weylDot_self hA hΛ _)
    (φ := bggEmb P hA hΛ (bggOne P hA)) (ψ := LieModuleHom.id) ?_ ?_).trans
    ((LieModuleHom.range_eq_top _).mpr Function.surjective_id)
  · exact fun h ↦ hwv_ne_zero P _ (bggEmb_injective P hA hΛ _ (by
      rw [h, _root_.zero_apply, map_zero]))
  · exact fun h ↦ hwv_ne_zero P Λ (by
      rw [← LieModuleHom.id_apply (R := K) (L := P.KacMoodyAlgebra) (hwv P Λ), h,
        _root_.zero_apply])

open Classical in
lemma bggEmbZero_surjective : Function.Surjective (bggEmbZero P hA hΛ) := by
  intro m
  obtain ⟨x, hx⟩ := (LieModuleHom.mem_range _ m).mp
    ((range_bggEmb_bggOne P hA hΛ).symm ▸ LieSubmodule.mem_top m)
  exact ⟨DirectSum.of _ _ x, by rw [bggEmbZero_of, hx]⟩

open Classical in
/-- The augmentation `C₀ = M(1 · Λ) → M(Λ) → L(Λ)` of the BGG complex. -/
def bggAugmentation : BGGTerm P hA Λ 0 →ₗ⁅K,P.KacMoodyAlgebra⁆ IrreducibleModule P Λ :=
  (bggAug P).comp (bggEmbZero P hA hΛ)

theorem bggAugmentation_surjective : Function.Surjective (bggAugmentation P hA hΛ) :=
  (bggAug_surjective P).comp (bggEmbZero_surjective P hA hΛ)

open Classical in
lemma bggEmbZero_bggDiff_of (w' : {w : W // (cs).length w = 0 + 1})
    (x : VermaModule P (P.weylDot hA w' Λ)) :
    bggEmbZero P hA hΛ (bggDiff P hA hΛ 0 (DirectSum.of _ w' x)) =
      bggSign P hA (bggOne P hA : W) w' • bggEmb P hA hΛ w' x := by
  have hb : bggBoundary P hA w' 0 = {bggOne P hA} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun w _ ↦ Subsingleton.elim _ _⟩
    rw [mem_bggBoundary, CoxeterSystem.BruhatCovBy]
    exact ⟨(cs).one_bruhatLE _, by rw [w'.2, bggOne, (cs).length_one]⟩
  rw [bggDiff_of, hb, Finset.sum_singleton, map_smul, bggEmbZero_of,
    ← LieModuleHom.comp_apply,
    bggEmb_comp_bggMap P hA hΛ (w := (bggOne P hA : W)) ((cs).one_bruhatLE _)]

lemma bggSign_ne_zero (w w' : W) : bggSign P hA w w' ≠ 0 :=
  pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

omit hΛ in
lemma weylDot_simple (i : ι) (μ : Dual K H) :
    P.weylDot hA ((cs).simple i) μ = P.reflection hA i (μ + P.rho) - P.rho := by
  have := weylDot_simple_mul P hA i 1 μ
  rwa [mul_one, weylDot_one] at this

/-- The image of `M(rᵢ · Λ) ↪ M(Λ)` does not depend on the choice of the embedding. -/
lemma range_bggEmb_simple {w : W} {i : ι} (hi : w = (cs).simple i) :
    (bggEmb P hA hΛ w).range =
      (reflectionHom hA (Nat.succ_pos _) (add_rho_coroot_eq P hΛ i)).range :=
  range_eq_of_finrank_hom_eq_one P (by rw [hi, weylDot_simple])
    (finrank_hom_weylDot_self hA hΛ w)
    (fun h ↦ hwv_ne_zero P _ (bggEmb_injective P hA hΛ _ (by
      rw [h, _root_.zero_apply, map_zero])))
    (reflectionHom_ne_zero hA (Nat.succ_pos _) (add_rho_coroot_eq P hΛ i))

variable [FiniteDimensional K H] (hS : A.IsSymmetrizable)
include hS

open Classical in
/-- The image of `C₁ → C₀ ≅ M(Λ)` is the maximal proper submodule of `M(Λ)`. -/
lemma range_bggEmbZero_comp_bggDiff :
    ((bggEmbZero P hA hΛ).comp (bggDiff P hA hΛ 0)).range = maxSubmodule P Λ := by
  rw [← ker_bggAug, ← range_bggDiffOne P hA hΛ hS, bggDiffOne, DirectSum.range_toLieModule]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'
    | of w' x =>
      rw [LieModuleHom.comp_apply, bggEmbZero_bggDiff_of]
      obtain ⟨i, hi⟩ := (cs).length_eq_one_iff.mp w'.2
      refine SMulMemClass.smul_mem _ (LieSubmodule.mem_iSup_of_mem i ?_)
      rw [← range_bggEmb_simple P hA hΛ hi]
      exact (LieModuleHom.mem_range _ _).mpr ⟨x, rfl⟩
  · refine iSup_le fun i ↦ ?_
    let w' : {w : W // (cs).length w = 0 + 1} := ⟨(cs).simple i, (cs).length_simple i⟩
    rw [← range_bggEmb_simple P hA hΛ (w := w') rfl]
    rintro _ ⟨x, rfl⟩
    refine ⟨DirectSum.of _ w' ((bggSign P hA (bggOne P hA : W) w')⁻¹ • x), ?_⟩
    rw [LieModuleHom.comp_apply, bggEmbZero_bggDiff_of, map_smul, smul_smul,
      mul_inv_cancel₀ (bggSign_ne_zero P hA _ _), one_smul]

open Classical in
/-- **Exactness of the BGG complex at `C₀`** ([BGG] (check), [HumO] Thm. 6.3 (check)): for a
symmetrizable generalized Cartan matrix and `Λ` dominant integral, the kernel of the
augmentation `C₀ = M(Λ) → L(Λ)` is the image of `d : C₁ → C₀`. The proof uses
`maxSubmodule_eq_fPowSubmodule` ([Kac] Cor. 10.4). -/
theorem ker_bggAugmentation : (bggAugmentation P hA hΛ).ker = (bggDiff P hA hΛ 0).range := by
  ext x
  rw [LieModuleHom.mem_ker, LieModuleHom.mem_range, bggAugmentation, LieModuleHom.comp_apply,
    ← LieModuleHom.mem_ker, ker_bggAug, ← range_bggEmbZero_comp_bggDiff P hA hΛ hS,
    LieModuleHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, bggEmbZero_injective P hA hΛ hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩

open Classical in
/-- The augmentation composed with `d : C₁ → C₀` vanishes. -/
theorem bggAugmentation_comp_bggDiff :
    (bggAugmentation P hA hΛ).comp (bggDiff P hA hΛ 0) = 0 := by
  ext y
  rw [LieModuleHom.comp_apply, _root_.zero_apply, ← LieModuleHom.mem_ker,
    ker_bggAugmentation P hA hΛ hS]
  exact (LieModuleHom.mem_range _ _).mpr ⟨y, rfl⟩

end Matrix.Realization.KacMoodyAlgebra
