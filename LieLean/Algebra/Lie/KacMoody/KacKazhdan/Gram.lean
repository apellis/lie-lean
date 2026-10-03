/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Leading
import LieLean.Algebra.Lie.KacMoody.CharacterVerma

/-!
# The Shapovalov form in a pair of dual PBW bases

Let `A` be a symmetrizable matrix and `𝔤 = 𝔤(A)` over a field `K` of characteristic zero, with its
invariant form `(·|·)` ([Kac] Thm. 2.2) and the antiinvolution `σ` of the Shapovalov form.
For each positive root `α`, the form `(y, y') ↦ (σ y | y')` on `𝔤_{-α}` is nondegenerate; we take
the basis `(e_x)` of `𝔫₋ = ⊕ 𝔤_{-α}` of `nNegBasis` and its dual basis `(e'_x)` for these forms
(`nNegDualBasis`): `(σ e_x | e'_y) = δ_{xy}` for `x`, `y` of the same root. Then
`[σ e_x, e'_y] = δ_{xy} ν⁻¹(α)` ([Kac] Thm. 2.2 e)), so `(σ e_x, e'_x, ν⁻¹(α))` are paired root
vectors (`pairedRootVectors`), and the Shapovalov pairing `B_λ(e_s v_λ, e'_t v_λ)` of two PBW
monomials is a matrix coefficient `⟨v_λ^*, σ(e_s) e'_t v_λ⟩` of the kind studied in
`Matrix.Realization.KacMoodyAlgebra.PairedRootVectors.hasTop_wordFn`. As a function of `λ` it is a
polynomial of degree `≤ min(|s|, |t|)`, and for `|s| = |t|` its component of degree `|s|` is
`δ_{st} ∏_x s(x)! ∏_x (λ | α_x)^{s(x)}` (`contravariantForm_pbw_hasTop`).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.nNegDualBasis`: the dual basis `(e'_x)`.
* `Matrix.Realization.KacMoodyAlgebra.VermaModule.pbwDualVerma`: the PBW basis of `M(λ)` built
  from `(e'_x)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm_pbw_mem_polyLE`,
  `Matrix.Realization.KacMoodyAlgebra.VermaModule.contravariantForm_pbw_hasTop`: the degree and
  the leading term of `λ ↦ B_λ(e_s v_λ, e'_t v_λ)`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.2, §9.4
  (stated over `ℂ`).
* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §2.3.
-/

open Module LieModule Module.Dual MvPolynomial UniversalEnvelopingAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K
local notation "mapN" => UniversalEnvelopingAlgebra.map (LieSubalgebra.incl (nNeg P))

/-- `σ` maps `𝔤_μ` to `𝔤_{-μ}`. -/
lemma transpose_mem_rootSpace {μ : Dual K H} {x : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P μ) :
    transpose P x ∈ rootSpace P (-μ) := by
  rw [transpose_apply]
  exact neg_mem (chevalleyInvolution_mem_rootSpace P hx)

/-- The root vector of index `x` of the basis `nNegBasis`, as an element of `𝔤`. -/
abbrev nNegVec (x : NegRootIndex P) : P.KacMoodyAlgebra := (nNegBasis P x : nNeg P)

lemma transpose_nNegVec_mem_rootSpace (x : NegRootIndex P) :
    transpose P (nNegVec P x) ∈ rootSpace P x.root := by
  simpa using transpose_mem_rootSpace P (nNegBasis_mem P x)

lemma transpose_nNegVec_mem_nPos (x : NegRootIndex P) : transpose P (nNegVec P x) ∈ nPos P := by
  rw [← LieSubalgebra.mem_toSubmodule, nPos_toSubmodule_eq]
  exact Submodule.mem_iSup_of_mem x.root
    (Submodule.mem_iSup_of_mem x.1.2 (transpose_nNegVec_mem_rootSpace P x))

/-- The inclusion `𝔤_{-α} → 𝔤`. -/
abbrev nNegRootSpaceIncl (α : P.posWeights) : nNegRootSpace P α →ₗ[K] P.KacMoodyAlgebra :=
  nNegIncl P ∘ₗ (nNegRootSpace P α).subtype

omit [CharZero K] in
lemma nNegRootSpaceIncl_mem (α : P.posWeights) (u : nNegRootSpace P α) :
    nNegRootSpaceIncl P α u ∈ rootSpace P (-(α : Dual K H)) := u.2

open Classical in
lemma nNegVec_mk (α : P.posWeights) (i : Fin (finrank K (rootSpace P (-(α : Dual K H))))) :
    nNegVec P ⟨α, i⟩ = nNegRootSpaceIncl P α
      (Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α) i) := by
  have := congrFun ((isInternal_nNegRootSpace P).collectedBasis_coe fun α ↦
    Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α)) ⟨α, i⟩
  exact congrArg (nNegIncl P) this

variable [FiniteDimensional K H] (S : A.Symmetrization)

/-! ### The dual basis -/

/-- The pairing `Φ_α(u, v) = (σ v | u)` on `𝔤_{-α}`. -/
def rootSpacePairingForm (α : P.posWeights) : LinearMap.BilinForm K (nNegRootSpace P α) :=
  ((invForm P S).compl₁₂ (transpose P ∘ₗ nNegRootSpaceIncl P α) (nNegRootSpaceIncl P α)).flip

lemma rootSpacePairingForm_apply (α : P.posWeights) (u v : nNegRootSpace P α) :
    rootSpacePairingForm P S α u v =
      invForm P S (transpose P (nNegRootSpaceIncl P α v)) (nNegRootSpaceIncl P α u) := rfl

lemma nondegenerate_rootSpacePairingForm (α : P.posWeights) :
    (rootSpacePairingForm P S α).Nondegenerate := by
  have hinj : Function.Injective (nNegRootSpaceIncl P α) :=
    (nNegIncl_injective P).comp Subtype.val_injective
  refine ⟨fun u hu ↦ ?_, fun v hv ↦ ?_⟩
  · -- `u ∈ 𝔤_{-α}` is orthogonal to `σ(𝔤_{-α}) = 𝔤_α`
    refine hinj ?_
    rw [map_zero]
    refine eq_zero_of_invForm_rootSpace_eq_zero P S (nNegRootSpaceIncl_mem P α u) fun y hy ↦ ?_
    rw [neg_neg] at hy
    have hyn : transpose P y ∈ (nNeg P).toSubmodule :=
      rootSpace_neg_le_nNeg P α.2 (transpose_mem_rootSpace P hy)
    have := hu ⟨⟨transpose P y, hyn⟩, transpose_mem_rootSpace P hy⟩
    rw [rootSpacePairingForm_apply] at this
    rw [(isSymm_invForm P S).eq]
    convert this using 3
    exact (transpose_transpose P y).symm
  · -- `σ v ∈ 𝔤_α` is orthogonal to `𝔤_{-α}`
    have hσ : transpose P (nNegRootSpaceIncl P α v) = 0 := by
      refine eq_zero_of_invForm_rootSpace_eq_zero P S
        (by simpa using transpose_mem_rootSpace P (nNegRootSpaceIncl_mem P α v)) fun y hy ↦ ?_
      have hy' : y ∈ LinearMap.range (nNegRootSpaceIncl P α) := by
        have hmem : y ∈ (nNeg P).toSubmodule :=
          rootSpace_neg_le_nNeg P α.2 hy
        exact ⟨⟨⟨y, hmem⟩, hy⟩, rfl⟩
      obtain ⟨u, rfl⟩ := hy'
      exact hv u
    refine hinj ?_
    rw [map_zero, ← transpose_transpose P (nNegRootSpaceIncl P α v), hσ, map_zero]

open Classical in
/-- The basis `(e'_x)` of `𝔫₋` dual to `nNegBasis` for the pairings `(σ y | y')` on the root
spaces `𝔤_{-α}`. -/
def nNegDualBasis : Basis (NegRootIndex P) K (nNeg P) :=
  (isInternal_nNegRootSpace P).collectedBasis fun α ↦
    (rootSpacePairingForm P S α).dualBasis (nondegenerate_rootSpacePairingForm P S α)
      (Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α))

/-- The dual root vector of index `x`, as an element of `𝔤`. -/
abbrev nNegDualVec (x : NegRootIndex P) : P.KacMoodyAlgebra := (nNegDualBasis P S x : nNeg P)

open Classical in
lemma nNegDualVec_mk (α : P.posWeights) (j : Fin (finrank K (rootSpace P (-(α : Dual K H))))) :
    nNegDualVec P S ⟨α, j⟩ = nNegRootSpaceIncl P α
      ((rootSpacePairingForm P S α).dualBasis (nondegenerate_rootSpacePairingForm P S α)
        (Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α)) j) := by
  have := congrFun ((isInternal_nNegRootSpace P).collectedBasis_coe fun α ↦
    (rootSpacePairingForm P S α).dualBasis (nondegenerate_rootSpacePairingForm P S α)
      (Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α))) ⟨α, j⟩
  exact congrArg (nNegIncl P) this

open Classical in
lemma nNegDualVec_mem (x : NegRootIndex P) : nNegDualVec P S x ∈ rootSpace P (-x.root) :=
  (isInternal_nNegRootSpace P).collectedBasis_mem _ x

/-- `(σ e_x | e'_x) = 1`. -/
lemma invForm_transpose_nNegVec_nNegDualVec_self (x : NegRootIndex P) :
    invForm P S (transpose P (nNegVec P x)) (nNegDualVec P S x) = 1 := by
  classical
  obtain ⟨α, i⟩ := x
  have := LinearMap.BilinForm.apply_dualBasis_left (nondegenerate_rootSpacePairingForm P S α)
    (Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α)) i i
  rw [rootSpacePairingForm_apply] at this
  rw [nNegVec_mk, nNegDualVec_mk, this]
  simp

/-- `(σ e_x | e'_y) = 0` for `x ≠ y` of the same root. -/
lemma invForm_transpose_nNegVec_nNegDualVec_of_ne {x y : NegRootIndex P} (hne : x ≠ y)
    (hxy : x.root = y.root) :
    invForm P S (transpose P (nNegVec P x)) (nNegDualVec P S y) = 0 := by
  classical
  obtain ⟨α, i⟩ := x
  obtain ⟨β, j⟩ := y
  obtain rfl : α = β := Subtype.ext hxy
  have hij : j ≠ i := fun h ↦ hne (by rw [h])
  have := LinearMap.BilinForm.apply_dualBasis_left (nondegenerate_rootSpacePairingForm P S α)
    (Module.finBasisOfFinrankEq K _ (finrank_nNegRootSpace P α)) j i
  rw [rootSpacePairingForm_apply] at this
  rw [nNegVec_mk, nNegDualVec_mk, this]
  simp [Ne.symm hij]

/-- The paired root vectors `(σ e_x, e'_x, ν⁻¹(α_x))`. -/
def pairedRootVectors : PairedRootVectors P (NegRootIndex P) where
  root x := x.root
  coroot x := (P.toDual S).symm x.root
  left x := ⟨transpose P (nNegVec P x), transpose_nNegVec_mem_nPos P x⟩
  right x := nNegDualBasis P S x
  root_ne_zero x h := P.zero_notMem_posWeights (h ▸ x.1.2)
  left_mem x := transpose_nNegVec_mem_rootSpace P x
  right_mem x := nNegDualVec_mem P S x
  lie_left_right_self x := by
    rw [lie_eq_invForm_smul P S (transpose_nNegVec_mem_rootSpace P x) (nNegDualVec_mem P S x),
      invForm_transpose_nNegVec_nNegDualVec_self, one_smul]
  lie_left_right_of_ne x y hxy hroot := by
    have hy := nNegDualVec_mem P S y
    rw [← hroot] at hy
    rw [lie_eq_invForm_smul P S (transpose_nNegVec_mem_rootSpace P x) hy,
      invForm_transpose_nNegVec_nNegDualVec_of_ne P S hxy hroot, zero_smul]

/-! ### The Shapovalov pairing of the two PBW bases -/

omit [FiniteDimensional K H] in
/-- `σ(z₁ ⋯ zₘ) = σ(zₘ) ⋯ σ(z₁)`. -/
lemma unop_envTranspose_list_prod (l : List P.KacMoodyAlgebra) :
    (envTranspose P (l.map ιᵤ).prod).unop = (l.reverse.map fun z ↦ ιᵤ (transpose P z)).prod := by
  induction l with
  | nil => simp
  | cons z l ih =>
    rw [List.map_cons, List.prod_cons, unop_envTranspose_mul, ih, envTranspose_ι,
      MulOpposite.unop_op, List.reverse_cons, List.map_append, List.prod_append]
    simp

namespace VermaModule

variable (Λ : Dual K H)

/-- The PBW basis of `M(Λ)` built from the dual root vectors `nNegDualBasis`. -/
def pbwDualVerma : Basis (NegRootIndex P →₀ ℕ) K (VermaModule P Λ) :=
  (pbwBasis (nNegDualBasis P S)).map (equivEnvNNeg P Λ)

omit [FiniteDimensional K H] [CharZero K] in
lemma mapN_pbwMonomial (b : NegRootIndex P → nNeg P) (s : NegRootIndex P →₀ ℕ) :
    mapN (pbwMonomial K b s) =
      ((((Finsupp.toMultiset s).sort (· ≤ ·)).map fun x ↦ (b x : P.KacMoodyAlgebra)).map
        ιᵤ).prod := by
  rw [map_pbwMonomial, pbwMonomial, List.map_map]
  rfl

omit [FiniteDimensional K H] in
lemma pbwBasisVerma_eq (s : NegRootIndex P →₀ ℕ) :
    pbwBasisVerma P Λ s =
      ((((Finsupp.toMultiset s).sort (· ≤ ·)).map (nNegVec P)).map ιᵤ).prod • hwv P Λ := by
  rw [pbwBasisVerma, Basis.map_apply, pbwBasis_apply, equivEnvNNeg_apply, mapN_pbwMonomial]

lemma pbwDualVerma_eq (t : NegRootIndex P →₀ ℕ) :
    pbwDualVerma P S Λ t =
      ((((Finsupp.toMultiset t).sort (· ≤ ·)).map (nNegDualVec P S)).map ιᵤ).prod • hwv P Λ := by
  rw [pbwDualVerma, Basis.map_apply, pbwBasis_apply, equivEnvNNeg_apply, mapN_pbwMonomial]

/-- The word `σ(e_s) e'_t`: the letters `σ e_x` for `x` in the reversed sorted list of `s`,
followed by the letters `e'_y` for `y` in the sorted list of `t`. -/
abbrev pbwWord (s t : NegRootIndex P →₀ ℕ) : List (TriLetter P) :=
  (pairedRootVectors P S).word ((Finsupp.toMultiset s).sort (· ≤ ·)).reverse
    (((Finsupp.toMultiset t).sort (· ≤ ·)).map Sum.inl)

/-- `B_Λ(e_s v_Λ, e'_t v_Λ) = ⟨v_Λ^*, σ(e_s) e'_t v_Λ⟩`. -/
theorem contravariantForm_pbw_eq_wordFn (s t : NegRootIndex P →₀ ℕ) :
    contravariantForm P Λ (pbwBasisVerma P Λ s) (pbwDualVerma P S Λ t) =
      wordFn P ((pbwWord P S s t).map TriLetter.val) Λ := by
  rw [pbwBasisVerma_eq, pbwDualVerma_eq, contravariantForm_smul_hwv, unop_envTranspose_list_prod,
    wordFn_apply]
  congr 2
  simp [PairedRootVectors.word, pairedRootVectors, PairedRootVectors.rightLetter,
    TriLetter.val, List.map_reverse, Function.comp_def]

omit [CharZero K] [FiniteDimensional K H] in
lemma length_sort_toMultiset (s : NegRootIndex P →₀ ℕ) :
    ((Finsupp.toMultiset s).sort (· ≤ ·)).length = s.degree := by
  rw [Multiset.length_sort, Finsupp.card_toMultiset, Finsupp.degree_apply]
  rfl

omit [CharZero K] [FiniteDimensional K H] in
lemma lefts_map_inl (l : List (NegRootIndex P)) :
    PairedRootVectors.lefts (l.map (Sum.inl (β := H))) = l := by
  induction l <;> simp_all

omit [CharZero K] [FiniteDimensional K H] in
lemma rights_map_inl (l : List (NegRootIndex P)) :
    PairedRootVectors.rights (l.map (Sum.inl (β := H))) = [] := by
  induction l <;> simp_all

lemma deg_pbwWord (s t : NegRootIndex P →₀ ℕ) :
    TriLetter.deg (pbwWord P S s t) = min s.degree t.degree := by
  simp only [pbwWord, PairedRootVectors.word, TriLetter.deg, TriLetter.numCart_append,
    TriLetter.numPos_append, TriLetter.numNeg_append, PairedRootVectors.numCart_map_pos,
    PairedRootVectors.numPos_map_pos, PairedRootVectors.numNeg_map_pos,
    PairedRootVectors.numCart_map_rightLetter, PairedRootVectors.numPos_map_rightLetter,
    PairedRootVectors.numNeg_map_rightLetter, lefts_map_inl, rights_map_inl, List.length_nil,
    List.length_reverse, length_sort_toMultiset]
  omega

/-- **The degree estimate for the Shapovalov form** ([KK]; [Kum] Thm. 2.3.4, proof, Step 2 (1)):
`B_λ(e_s v_λ, e'_t v_λ)` is
a polynomial function of `λ` of degree at most `min(|s|, |t|)`. -/
theorem contravariantForm_pbw_mem_polyLE (s t : NegRootIndex P →₀ ℕ) :
    (fun Λ ↦ contravariantForm P Λ (pbwBasisVerma P Λ s) (pbwDualVerma P S Λ t)) ∈
      polyLE K H (min s.degree t.degree) := by
  simp_rw [contravariantForm_pbw_eq_wordFn]
  rw [← deg_pbwWord P S s t]
  exact wordFn_mem_polyLE P _

/-- The polynomial `∏_x s(x)! ∏_x (λ | α_x)^{s(x)}`: the leading term of
`B_λ(e_s v_λ, e'_s v_λ)`. -/
def pbwTopPoly (s : NegRootIndex P →₀ ℕ) : MvPolynomial (PolyIdx K H) K :=
  C (∏ x ∈ s.support, ((s x).factorial : K)) *
    ∏ x ∈ s.support, linPoly K H ((P.toDual S).symm x.root) ^ s x

/-- **The leading term of the Shapovalov form** ([KK]; [Kum] Thm. 2.3.4, proof, Step 2,
(2)–(3)): for `|s| = |t|`, the component
of degree `|s|` of `λ ↦ B_λ(e_s v_λ, e'_t v_λ)` is `δ_{st} ∏_x s(x)! ∏_x (λ | α_x)^{s(x)}`. -/
theorem contravariantForm_pbw_hasTop (s t : NegRootIndex P →₀ ℕ) (hst : s.degree = t.degree) :
    HasTop s.degree (if s = t then pbwTopPoly P S s else 0)
      (fun Λ ↦ contravariantForm P Λ (pbwBasisVerma P Λ s) (pbwDualVerma P S Λ t)) := by
  classical
  simp_rw [contravariantForm_pbw_eq_wordFn]
  have h := (pairedRootVectors P S).hasTop_wordFn ((Finsupp.toMultiset s).sort (· ≤ ·)).reverse
    (((Finsupp.toMultiset t).sort (· ≤ ·)).map Sum.inl) (by
      rw [lefts_map_inl, List.length_reverse, length_sort_toMultiset, length_sort_toMultiset, hst])
  rw [← pbwWord, deg_pbwWord, ← hst, min_self] at h
  convert h using 1
  simp only [PairedRootVectors.topPoly, lefts_map_inl, Multiset.coe_reverse, Multiset.sort_eq]
  have hinj : Function.Injective (Finsupp.toMultiset (α := NegRootIndex P)) :=
    Function.LeftInverse.injective (Finsupp.toMultiset_toFinsupp)
  by_cases h : s = t
  · subst h
    simp only [↓reduceIte]
    rw [pbwTopPoly]
    congr 1
    · simp [Multiset.factorialProd, PairedRootVectors.cartPoly, rights_map_inl]
    · simp only [PairedRootVectors.corootPoly, pairedRootVectors, List.map_reverse,
        List.prod_reverse]
      rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.sort_eq, Finsupp.toMultiset_map,
        Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (fun _ ↦ pow_zero _)
          (fun _ _ _ ↦ pow_add _ _ _)]
      rfl
  · have h' : Finsupp.toMultiset s ≠ Finsupp.toMultiset t := fun h' ↦ h (hinj h')
    simp only [h, h', ↓reduceIte]

end VermaModule

end Matrix.Realization.KacMoodyAlgebra
