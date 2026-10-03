/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.Rank

/-!
# Weight spaces of the classical irreducible modules through the free algebra

Let `(I, ·)` be a Cartan datum with Cartan matrix `A`, `K` a field of characteristic zero,
`(𝔥, Π, Π^∨)` a realization of `A` over `K`, `Λ ∈ 𝔥*` dominant integral with
`⟨Λ, αᵢ^∨⟩ = nᵢ`, and `Y : K⟨θᵢ⟩ → L(Λ)`, `y ↦ y(f) v_Λ` (`LusztigF.toIrreducible`), where `L(Λ)`
is the irreducible highest-weight module of the Kac–Moody algebra `𝔤(A)`.

* `Y` maps the words of weight `ν ∈ ℕ[I]` onto the weight space `L(Λ)_{Λ - ν}`
  (`LusztigF.weightSpace_irreducibleModule_eq_map`), and its kernel on `K⟨θ⟩_ν` is the kernel of
  the classical Shapovalov map `y ↦ (S(w, y))_w` (`LusztigF.toIrreducible_eq_zero_iff`), by the
  nondegeneracy of the contravariant form of `L(Λ)` ([Kac] §9.4). Hence
  `dim L(Λ)_{Λ - ν}` is the rank of the classical Shapovalov pairing on the words of weight `ν`
  (`LusztigF.finrank_weightSpace_irreducibleModule`); this rank does not depend on the field
  (`LusztigF.shapovalovRank_classicalCoeff`), so neither does `dim L(Λ)_{Λ - ν}`.
* The kernel of `Y` on `K⟨θ⟩_ν` lies in the span of the products `a sᵢⱼ b` of weight `ν` with the
  classical Serre elements `sᵢⱼ` and of the words `a θᵢ^{nᵢ+1}` of weight `ν`
  (`LusztigF.mem_tildeSpan_of_toIrreducible_eq_zero`); this is the associative presentation
  `L(Λ) ≅ 𝒮 ⧸ Σᵢ 𝒮 θᵢ^{nᵢ+1}` of `Matrix.Realization.KacMoodyAlgebra.serreAssocQuotientEquiv`
  ([Kac] Thm. 9.11 and Cor. 10.4), taken weight by weight.

## Main definitions

* `LusztigF.powSpan K n ν`: the span of the words `a θᵢ^{nᵢ+1}` of weight `ν`.
* `LusztigF.tildeSpan D q n ν`: `serreSpan D q ν ⊔ powSpan K n ν`.

## Main results

* `LusztigF.weightSpace_irreducibleModule_eq_map`, `LusztigF.toIrreducible_eq_zero_iff`,
  `LusztigF.finrank_weightSpace_irreducibleModule`, `LusztigF.shapovalovRank_classicalCoeff`.
* `LusztigF.mem_tildeSpan_of_toIrreducible_eq_zero`,
  `LusztigF.mem_tildeSpan_of_shapovalovMap_eq_zero`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.4, Thm. 9.11,
  Cor. 10.4.
-/

noncomputable section

open FreeAlgebra QuantumGroup Matrix Matrix.Realization Matrix.Realization.KacMoodyAlgebra Module
  LieModule

namespace LusztigF

/-! ### Spans of Serre products and of words ending in `θᵢ^{nᵢ+1}` -/

section Spans

variable {K I : Type*} [Field K] (D : LusztigCartanDatum I)

/-- The word `a θᵢ^{nᵢ+1}` attached to `g = (a, i)`. -/
def powWord (n : I → ℕ) (g : List I × I) : List I := g.1 ++ List.replicate (n g.2 + 1) g.2

/-- The indices `(a, i)` for which the word `a θᵢ^{nᵢ+1}` has weight `ν`. -/
def powIndices (n : I → ℕ) (ν : I →₀ ℕ) : Set (List I × I) :=
  {g | wordWeight (powWord n g) = ν}

variable (K) in
/-- The span of the words `a θᵢ^{nᵢ+1}` of weight `ν`. -/
def powSpan (n : I → ℕ) (ν : I →₀ ℕ) : Submodule K (LusztigF K I) :=
  Submodule.span K ((fun g ↦ wordBasis K I (powWord n g)) '' powIndices n ν)

/-- The span of the Serre products `a sᵢⱼ b` (with parameters `q`) and of the words `a θᵢ^{nᵢ+1}`
of weight `ν`: the weight-`ν` component of `J + Σᵢ 'f θᵢ^{nᵢ+1}`. -/
def tildeSpan (q : I → K) (n : I → ℕ) (ν : I →₀ ℕ) : Submodule K (LusztigF K I) :=
  serreSpan D q ν ⊔ powSpan K n ν

omit [Field K] in
lemma powSpan_le_weightSpace [Field K] (n : I → ℕ) (ν : I →₀ ℕ) :
    powSpan K n ν ≤ weightSpace K ν := by
  rw [powSpan, Submodule.span_le]
  rintro _ ⟨g, hg, rfl⟩
  exact wordBasis_mem_wordSpan_of_eq hg

lemma tildeSpan_le_weightSpace (q : I → K) (n : I → ℕ) (ν : I →₀ ℕ) :
    tildeSpan D q n ν ≤ weightSpace K ν :=
  sup_le (serreSpan_le_weightSpace D q ν) (powSpan_le_weightSpace n ν)

variable [DecidableEq I]

/-- The weight-`ν` component of `b θᵢ^{nᵢ+1}` is a combination of words `a θᵢ^{nᵢ+1}` of
weight `ν`. -/
lemma weightProj_mul_θ_pow_mem_powSpan (n : I → ℕ) (ν : I →₀ ℕ) (b : LusztigF K I) (i : I) :
    FreeAlgebra.weightProj K ν (b * θ K i ^ (n i + 1)) ∈ powSpan K n ν := by
  have hN : θ K i ^ (n i + 1) = wordBasis K I (List.replicate (n i + 1) i) := by simp
  rw [hN, weightProj_mul_wordBasis]
  split_ifs with hle
  · set μ := ν - wordWeight (List.replicate (n i + 1) i) with hμ
    clear_value μ
    have hb := FreeAlgebra.weightProj_mem (R := K) μ b
    generalize FreeAlgebra.weightProj K μ b = z at hb ⊢
    induction hb using wordSpan_induction with
    | word a ha =>
      rw [← wordBasis_append]
      refine Submodule.subset_span ⟨(a, i), ?_, rfl⟩
      change wordWeight (a ++ List.replicate (n i + 1) i) = ν
      rw [wordWeight_append, ha, hμ, tsub_add_cancel_of_le hle]
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  · exact zero_mem _

end Spans

/-! ### The classical irreducible module -/

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] [FiniteDimensional K H] (D : LusztigCartanDatum I)
  (P : Realization D.cartanMatrix K H) {Λ : Module.Dual K H} {n : I → ℕ}
  (hn : ∀ i, Λ (P.coroot i) = n i)

omit [DecidableEq I] [CharZero K] [FiniteDimensional K H] in
lemma rootOf_wordWeight_cons (j : I) (w : List I) :
    P.rootOf (fun i ↦ (wordWeight (j :: w) i : ℤ)) =
      P.root j + P.rootOf (fun i ↦ (wordWeight w i : ℤ)) := by
  classical
  rw [← rootOf_single, ← map_add]
  congr 1
  funext i
  by_cases h : i = j
  · subst h; simp [wordWeight_cons]
  · simp [wordWeight_cons, h]

/-- `Y(y)` has weight `Λ - ν` for `y` of weight `ν`. -/
lemma toIrreducible_mem_weightSpace {ν : I →₀ ℕ} {y : LusztigF K I}
    (hy : y ∈ weightSpace K ν) :
    toIrreducible D P hn y ∈
      weightSpaceOfMap (IrreducibleModule P Λ) (h P) (Λ - P.rootOf fun i ↦ (ν i : ℤ)) := by
  induction hy using wordSpan_induction with
  | word w hw =>
    subst hw
    induction w with
    | nil =>
      have e : (P.rootOf fun i ↦ ((wordWeight ([] : List I) i : ℕ) : ℤ)) = 0 := by
        rw [← map_zero P.rootOf]; congr 1
      rw [e, sub_zero, wordBasis_nil, toIrreducible_one]
      exact IrreducibleModule.hwv_mem_weightSpace P Λ
    | cons j w ih =>
      rw [← ι_mul_wordBasis, toIrreducible_θ_mul]
      convert lie_mem_weightSpaceOfMap (h P) (f_mem_rootSpace P j) ih using 2
      rw [rootOf_wordWeight_cons]
      abel
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- The weight space `L(Λ)_{Λ - ν}` is the image of the words of weight `ν`. -/
theorem weightSpace_irreducibleModule_eq_map (ν : I →₀ ℕ) :
    weightSpaceOfMap (IrreducibleModule P Λ) (h P) (Λ - P.rootOf fun i ↦ (ν i : ℤ)) =
      (weightSpace K ν).map (toIrreducible D P hn) := by
  refine le_antisymm (fun x hx ↦ ?_)
    (Submodule.map_le_iff_le_comap.2 fun y hy ↦ toIrreducible_mem_weightSpace D P hn hy)
  let N : Module.Dual K H → Submodule K (IrreducibleModule P Λ) := fun μ ↦
    ⨆ (ν' : I →₀ ℕ) (_ : Λ - P.rootOf (fun i ↦ (ν' i : ℤ)) = μ),
      (weightSpace K ν').map (toIrreducible D P hn)
  have hN : ∀ μ, N μ ≤ weightSpaceOfMap (IrreducibleModule P Λ) (h P) μ := fun μ ↦
    iSup₂_le fun ν' hν' ↦ hν' ▸
      Submodule.map_le_iff_le_comap.2 fun y hy ↦ toIrreducible_mem_weightSpace D P hn hy
  have hx' : x ∈ ⨆ μ, N μ := by
    obtain ⟨y, rfl⟩ := toIrreducible_surjective D P hn x
    have hy : y ∈ ⨆ ν', weightSpace K (I := I) ν' := by rw [iSup_weightSpace]; trivial
    have hy' : toIrreducible D P hn y ∈ ⨆ ν', (weightSpace K ν').map (toIrreducible D P hn) := by
      rw [← Submodule.map_iSup]; exact Submodule.mem_map_of_mem hy
    refine (iSup_le fun ν' ↦ ?_ : _ ≤ ⨆ μ, N μ) hy'
    exact le_iSup_of_le (Λ - P.rootOf fun i ↦ (ν' i : ℤ)) (le_iSup₂_of_le ν' rfl le_rfl)
  have hxN := mem_of_mem_iSup_of_le (h P) N hN hx hx'
  refine (iSup₂_le fun ν' hν' ↦ ?_ : N _ ≤ _) hxN
  have hνν : ν' = ν := by
    have h2 := P.rootOf_injective (sub_right_injective hν')
    ext i
    exact_mod_cast congr_fun h2 i
  rw [hνν]

/-- On `K⟨θ⟩_ν`, the kernel of `Y` is the kernel of the classical Shapovalov map. -/
theorem toIrreducible_eq_zero_iff {ν : I →₀ ℕ} {y : LusztigF K I} (hy : y ∈ weightSpace K ν) :
    toIrreducible D P hn y = 0 ↔ shapovalovMap (classicalCoeff K D n) ν y = 0 := by
  rw [shapovalovMap_eq_zero_iff _ hy]
  constructor
  · intro h0 w
    rw [← contravariantForm_toIrreducible D P hn, h0, map_zero]
  · intro h'
    refine (IrreducibleModule.nondegenerate_contravariantForm P Λ).2 _ fun u ↦ ?_
    obtain ⟨x, rfl⟩ := toIrreducible_surjective D P hn u
    induction x using induction_wordBasis with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', add_zero]
    | smul c x hx => simp only [map_smul, LinearMap.smul_apply, hx, smul_zero]
    | word w => rw [contravariantForm_toIrreducible, h' w]

include hn in
/-- `dim L(Λ)_{Λ - ν}` is the rank of the classical Shapovalov pairing on the words of
weight `ν`. -/
theorem finrank_weightSpace_irreducibleModule (ν : I →₀ ℕ) :
    finrank K (weightSpaceOfMap (IrreducibleModule P Λ) (h P) (Λ - P.rootOf fun i ↦ (ν i : ℤ))) =
      shapovalovRank (classicalCoeff K D n) ν := by
  rw [weightSpace_irreducibleModule_eq_map D P hn, ← LinearMap.range_domRestrict, shapovalovRank]
  refine LinearMap.finrank_range_eq_of_ker_eq _ _ ?_
  ext y
  simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply]
  exact toIrreducible_eq_zero_iff D P hn y.2

omit [Fintype I] [FiniteDimensional K H] in
/-- The rank of the classical Shapovalov pairing does not depend on the field of characteristic
zero. -/
theorem shapovalovRank_classicalCoeff (n : I → ℕ) (ν : I →₀ ℕ) :
    shapovalovRank (classicalCoeff K D n) ν = shapovalovRank (classicalCoeff ℚ D n) ν := by
  have hc : (fun i ↦ algebraMap ℚ K ∘ classicalCoeff ℚ D n i) = classicalCoeff K D n := by
    funext i μ
    simp only [Function.comp_apply, classicalCoeff, map_intCast]
  have hmap : ∀ u : Words ν, shapovalovMap (classicalCoeff K D n) ν (wordBasis K I u.1) =
      algebraMap ℚ K ∘ shapovalovMap (classicalCoeff ℚ D n) ν (wordBasis ℚ I u.1) := by
    intro u
    funext w
    rw [Function.comp_apply, shapovalovMap_apply, shapovalovMap_apply, map_vermaForm,
      mapCoeffs_wordBasis, hc]
  rw [shapovalovRank, shapovalovRank, range_shapovalovMap, range_shapovalovMap,
    show (fun u : Words ν ↦ shapovalovMap (classicalCoeff K D n) ν (wordBasis K I u.1)) =
      fun u ↦ algebraMap ℚ K ∘ shapovalovMap (classicalCoeff ℚ D n) ν (wordBasis ℚ I u.1)
      from funext hmap]
  refine le_antisymm (Submodule.finrank_span_algebraMap_comp_le _) ?_
  exact Submodule.finrank_span_le_of_comp_ratHom (RingHom.id ℚ) (algebraMap ℚ K)
    (algebraMap ℚ K).injective _

/-- **The classical kernel, with the relations `θᵢ^{nᵢ+1}`.** If `y ∈ K⟨θ⟩` has weight `ν` and
`Y(y) = 0` in `L(Λ)`, then `y` is a combination of Serre products `a sᵢⱼ b` and words
`a θᵢ^{nᵢ+1}` of weight `ν`. This is the presentation `L(Λ) ≅ 𝒮 ⧸ Σᵢ 𝒮 θᵢ^{nᵢ+1}`
([Kac] Thm. 9.11, Cor. 10.4), weight by weight. -/
theorem mem_tildeSpan_of_toIrreducible_eq_zero {ν : I →₀ ℕ} {y : LusztigF K I}
    (hy : y ∈ weightSpace K ν) (hY : toIrreducible D P hn y = 0) :
    y ∈ tildeSpan D (fun _ ↦ (1 : K)) n ν := by
  have hker : SerreAssocAlgebra.mkAlgHom K D.cartanMatrix y ∈
      SerreAssocAlgebra.thetaPowLeftIdeal K D.cartanMatrix n := by
    have hmem : SerreAssocAlgebra.mkAlgHom K D.cartanMatrix y ∈ LinearMap.ker
        (serreAssocToIrreducibleModule P D.isGeneralizedCartan_cartanMatrix
          D.isSymmetrizable_cartanMatrix hn) := hY
    rw [ker_serreAssocToIrreducibleModule] at hmem
    exact hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hker
  choose b hb using fun i ↦ SerreAssocAlgebra.mkAlgHom_surjective K D.cartanMatrix (c i)
  have hz : y - ∑ i, b i * θ K i ^ (n i + 1) ∈ serreAssocIdeal K D.cartanMatrix := by
    rw [← SerreAssocAlgebra.mkAlgHom_eq_zero_iff, map_sub, map_sum, ← hc, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, hb, smul_eq_mul]
    rfl
  have h1 := weightProj_mem_serreSpan D _ (serreAssocIdeal_le_span_serreWord D hz) ν
  rw [map_sub, map_sum, weightProj_self hy] at h1
  have h2 : ∑ i, FreeAlgebra.weightProj K ν (b i * θ K i ^ (n i + 1)) ∈ powSpan K n ν :=
    Submodule.sum_mem _ fun i _ ↦ weightProj_mul_θ_pow_mem_powSpan n ν (b i) i
  have := add_mem (Submodule.mem_sup_left h1 : _ ∈ tildeSpan D (fun _ ↦ (1 : K)) n ν)
    (Submodule.mem_sup_right h2)
  rwa [sub_add_cancel] at this

end LusztigF

namespace LusztigF

variable {I : Type*} [Finite I] [DecidableEq I] (D : LusztigCartanDatum I)

/-- The classical kernel in terms of the Shapovalov map (over `ℚ`, through the standard
realization): if `y ∈ ℚ⟨θ⟩_ν` pairs to zero with all words for the classical Shapovalov pairing
of highest weight `n`, then `y` is a combination of classical Serre products and words
`a θᵢ^{nᵢ+1}` of weight `ν`. -/
theorem mem_tildeSpan_of_shapovalovMap_eq_zero (n : I → ℕ) {ν : I →₀ ℕ} {y : LusztigF ℚ I}
    (hy : y ∈ weightSpace ℚ ν) (h0 : shapovalovMap (classicalCoeff ℚ D n) ν y = 0) :
    y ∈ tildeSpan D (fun _ ↦ (1 : ℚ)) n ν := by
  have := Fintype.ofFinite I
  have hn := stdWeight_coroot D n
  exact mem_tildeSpan_of_toIrreducible_eq_zero D (Realization.std D.cartanMatrix ℚ) hn hy
    ((toIrreducible_eq_zero_iff D (Realization.std D.cartanMatrix ℚ) hn hy).2 h0)

end LusztigF
