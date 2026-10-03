/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.IrreducibleCharacter.Verma

/-!
# Characters of the simple modules `L_q(Λ)`

Let `(I, ·)` be a Cartan datum with `I` finite (Cartan matrix `A`, symmetrizable), `R` an
`X`-regular root datum of type `(I, ·)` with coweight lattice `Y`, `k` a field of characteristic
zero and `v ∈ k` transcendental over `ℚ` (Lusztig's case is `k = ℚ(v)`), `U = U_q(𝔤)`
(`QuantumGroup R v`) and `Λ ∈ X = Hom(Y, ℤ)` dominant: `⟨i, Λ⟩ = Λ(i) ≥ 0` for all `i`. Let
`L_q(Λ) = M_q(Λ) ⧸ M'_q(Λ)` be the simple quotient of the Verma module
(`QuantumGroup.IrreducibleModule`) and `L̃_q(Λ) = M_q(Λ) ⧸ Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ`
(`QuantumGroup.FPowQuotient`).

**Theorem** ([Lus] 3.5.6, 6.2.3 (a), 33.1.3 (d), for `Y`- and `X`-regular root data over `ℚ(v)`;
[Jan] 5.15).
1. `L̃_q(Λ) = L_q(Λ)`, i.e. `M'_q(Λ) = Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ`
   (`QuantumGroup.VermaModule.maxSubmodule_eq_fPowSubmodule`,
   `QuantumGroup.FPowQuotient.equivIrreducibleModule`).
2. For every `ν ∈ ℕ[I]`, `dim L_q(Λ)^{Λ - ν} = dim L(Λ)_{Λ - ν}`, where `L(Λ)` is the irreducible
   highest-weight module of the Kac–Moody algebra `𝔤(A)` (any realization, over any field of
   characteristic zero) with the same highest weight
   (`QuantumGroup.IrreducibleModule.finrank_weightSpace_eq`).

The [Lus] numbers above were checked against the book; [Jan] treats finite type only.
The following argument is our own
reconstruction, for arbitrary symmetrizable Cartan data, reusing the specialization machinery
of the quantum Gabber–Kac theorem (`LieLean.Algebra.QuantumGroup.GabberKac`).

## Proof

Put `nᵢ = ⟨i, Λ⟩`. Through `y ↦ y⁻ v_Λ`, `'f ⧸ J ≅ M_q(Λ)` (`J` the quantum Serre ideal,
`QuantumGroup.VermaModule.equivSerreQuotient`), and `M_q(Λ)^{Λ - ν}` is the image of `'f_ν`.

* The raising operators act by `Eᵢ (y⁻ v_Λ) = (Eᵢ y)⁻ v_Λ` with the Verma-type operators
  `Eᵢ(θⱼ y) = θⱼ Eᵢ(y) + δᵢⱼ [nᵢ - ⟨μ, αᵢ^∨⟩]_{vᵢ} y` (`y ∈ 'f_μ`) on `'f`, so `y⁻ v_Λ ∈ M'_q(Λ)`
  iff the quantum Shapovalov pairing `S(w, y) = ε(E_w y)` vanishes for all words `w`
  (`QuantumGroup.VermaModule.toVerma_mem_maxSubmodule_iff`). Hence
  `dim L_q(Λ)^{Λ - ν} = rank Φ`, where `Φ : 'f_ν → k^{W_ν}`, `y ↦ (S(w, y))_{w ∈ W_ν}`, `W_ν` the
  words of weight `ν` (`QuantumGroup.VermaModule.finrank_weightSpace_irreducibleModule`).
* Let `Z_ν ⊆ 'f_ν` be the span of the quantum Serre products `a sᵢⱼ b` and of the words
  `a θᵢ^{nᵢ+1}` of weight `ν` (`LusztigF.tildeSpan`). Their images in `M_q(Λ)` lie in
  `Σᵢ U Fᵢ^{nᵢ+1} v_Λ ⊆ M'_q(Λ)`, so `Z_ν ⊆ ker Φ`.
* The coefficients of `S` are Laurent polynomials in `ℚ[T, T⁻¹]` evaluated at `T = v`
  (`LusztigF.vermaCoeff`); at `T = 1` they give the classical Shapovalov pairing `S₀`, the
  contravariant form of the classical `L(Λ)` (`LusztigF.contravariantForm_toIrreducible`). Let
  `Φ₀ : ℚ⟨θ⟩_ν → ℚ^{W_ν}` be the classical map and `Z⁰_ν` the classical analogue of `Z_ν`.
  1. `rank Φ ≥ rank Φ₀`: the specialization lemma (`LinearIndependent.of_comp_ratHom`; `T ↦ v`
     is injective since `v` is transcendental).
  2. `dim Z_ν ≥ dim Z⁰_ν`: a basis of `Z⁰_ν` can be chosen among the spanning vectors, which lift
     to `ℚ[T, T⁻¹]` (`LusztigF.serreProductL`) with quantum analogues in `Z_ν`; specialization.
  3. `ker Φ₀ ⊆ Z⁰_ν`: by nondegeneracy of the contravariant form, `ker Φ₀` is the kernel of
     `ℚ⟨θ⟩_ν → L(Λ)`, which is `Z⁰_ν` by the associative presentation
     `L(Λ) ≅ 𝒮 ⧸ Σᵢ 𝒮 θᵢ^{nᵢ+1}` ([Kac] Thm. 9.11, Cor. 10.4;
     `LusztigF.mem_tildeSpan_of_shapovalovMap_eq_zero`).
  Hence `dim ker Φ = |W_ν| - rank Φ ≤ |W_ν| - rank Φ₀ = dim ker Φ₀ ≤ dim Z⁰_ν ≤ dim Z_ν
  ≤ dim ker Φ`: all are equal, `ker Φ = Z_ν` and `rank Φ = rank Φ₀`
  (`QuantumGroup.VermaModule.shapovalovMap_eq_zero_iff_mem_tildeSpan`,
  `QuantumGroup.VermaModule.shapovalovRank_qCoeff`).
* (1) If `y⁻ v_Λ ∈ M'_q(Λ)`, each weight component of `y` lies in `ker Φ = Z_ν`, so
  `y⁻ v_Λ ∈ Σᵢ U Fᵢ^{nᵢ+1} v_Λ`. (2) `dim L_q(Λ)^{Λ - ν} = rank Φ = rank Φ₀`, and
  `dim L(Λ)_{Λ - ν} = rank Φ₀` for any realization over any field of characteristic zero
  (`LusztigF.finrank_weightSpace_irreducibleModule`, `LusztigF.shapovalovRank_classicalCoeff`).

## Main results

* `QuantumGroup.VermaModule.maxSubmodule_eq_fPowSubmodule`: `M'_q(Λ) = Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ`.
* `QuantumGroup.FPowQuotient.toIrreducibleModule_injective`,
  `QuantumGroup.FPowQuotient.equivIrreducibleModule`: `L̃_q(Λ) ≅ L_q(Λ)`.
* `QuantumGroup.IrreducibleModule.finrank_weightSpace_eq`: the characters of `L_q(Λ)` and
  `L(Λ)` agree.
* `QuantumGroup.VermaModule.maxSubmodule_eq_fPowSubmodule_ratFunc`,
  `QuantumGroup.IrreducibleModule.finrank_weightSpace_eq_ratFunc`: the case `k = ℚ(v)`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.5, §6.2, §33.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, Ch. 5.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.4, Thm. 9.11,
  Cor. 10.4.
-/

noncomputable section

open LusztigF FreeAlgebra Module

namespace LusztigF

variable {I : Type*} [DecidableEq I] (D : LusztigCartanDatum I)

/-- The spanning family of `LusztigF.tildeSpan` over `ℚ[T, T⁻¹]`: the Serre products
`LusztigF.serreProductL` and the words `a θᵢ^{nᵢ+1}` of weight `ν`. -/
def tildeFamily (n : I → ℕ) (ν : I →₀ ℕ) :
    serreIndices D ν ⊕ powIndices n ν → FreeAlgebra (LaurentPolynomial ℚ) I :=
  Sum.elim (fun t ↦ serreProductL D t.1) (fun t ↦ wordBasis _ I (powWord n t.1))

omit [DecidableEq I] in
/-- The specializations of `LusztigF.tildeFamily` span `LusztigF.tildeSpan`. -/
lemma span_mapCoeffs_tildeFamily {F : Type*} [Field F] (φ : LaurentPolynomial ℚ →+* F)
    (n : I → ℕ) (ν : I →₀ ℕ) :
    Submodule.span F (Set.range fun t ↦ mapCoeffs φ (tildeFamily D n ν t)) =
      tildeSpan D (fun i ↦ φ ((laurentT ^ D.d i : (LaurentPolynomial ℚ)ˣ) : _)) n ν := by
  have e : (fun t ↦ mapCoeffs φ (tildeFamily D n ν t)) = Sum.elim
      (fun t : serreIndices D ν ↦
        serreProduct D (fun i ↦ φ ((laurentT ^ D.d i : (LaurentPolynomial ℚ)ˣ) : _)) t.1)
      (fun t : powIndices n ν ↦ wordBasis F I (powWord n t.1)) := by
    funext t
    cases t with
    | inl t => exact mapCoeffs_serreProductL D φ t.1
    | inr t => exact mapCoeffs_wordBasis φ _
  rw [e, Set.Sum.elim_range, Submodule.span_union, tildeSpan, serreSpan, powSpan,
    Set.image_eq_range, Set.image_eq_range]

end LusztigF

namespace QuantumGroup

variable {k I Y : Type*} [Field k] [CharZero k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v] {Λ : Y →+ ℤ}

namespace VermaModule

/-- The comparison of the quantum and classical Shapovalov pairings on `'f_ν` (the dimension
count of the module docstring): the kernel of the quantum pairing on `'f_ν` is spanned by the
quantum Serre products and the words `a θᵢ^{⟨i,Λ⟩+1}` of weight `ν`, and its rank is the rank of
the classical pairing. -/
theorem shapovalov_comparison [Finite I] (hv : Transcendental ℚ v) (hR : R.IsXRegular)
    (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) (ν : I →₀ ℕ) :
    (∀ y ∈ LusztigF.weightSpace k ν, shapovalovMap (qCoeff R v Λ) ν y = 0 →
      y ∈ tildeSpan D (fun i ↦ v ^ D.d i) (fun i ↦ (Λ (R.coroot i)).toNat) ν) ∧
    shapovalovRank (qCoeff R v Λ) ν =
      shapovalovRank (classicalCoeff ℚ D fun i ↦ (Λ (R.coroot i)).toNat) ν := by
  have hv0 : v ≠ 0 := NeZero.ne v
  have hvn : ∀ n : ℕ, 0 < n → v ^ n ≠ 1 := fun n hn ↦ pow_ne_one_of_transcendental hv hn
  have hinj : Function.Injective (evalAt v hv0) :=
    LaurentPolynomial.eval₂_injective_of_transcendental hv hv0
  set n : I → ℕ := fun i ↦ (Λ (R.coroot i)).toNat with hn_def
  have hnZ : ∀ i, ((n i : ℕ) : ℤ) = Λ (R.coroot i) := fun i ↦ Int.toNat_of_nonneg (hΛ i)
  set cL : I → (I →₀ ℕ) → LaurentPolynomial ℚ :=
    fun i μ ↦ vermaCoeff D (fun i ↦ Λ (R.coroot i)) i μ
  have hc₀ : (fun i ↦ (evalAt (1 : ℚ) one_ne_zero) ∘ cL i) = classicalCoeff ℚ D n := by
    funext i μ
    simp only [Function.comp_apply, cL, evalAt_one_vermaCoeff, classicalCoeff, hnZ]
  have hcq : (fun i ↦ (evalAt v hv0) ∘ cL i) = qCoeff R v Λ := rfl
  set Φ := shapovalovMap (qCoeff R v Λ) ν
  set Φ₀ := shapovalovMap (classicalCoeff ℚ D n) ν
  set V := LusztigF.weightSpace k ν
  set V₀ := LusztigF.weightSpace ℚ ν
  set Z := tildeSpan D (fun i ↦ v ^ D.d i) n ν
  set Z₀ := tildeSpan D (fun _ ↦ (1 : ℚ)) n ν
  -- Step 1: `rank Φ₀ ≤ rank Φ`
  set p : Words ν → Words ν → LaurentPolynomial ℚ :=
    fun u w ↦ vermaForm cL w.1 (wordBasis _ I u.1)
  have e₀ : (fun u : Words ν ↦ Φ₀ (wordBasis ℚ I u.1)) = fun u ↦ evalAt 1 one_ne_zero ∘ p u := by
    funext u w
    simp only [Function.comp_apply, p, map_vermaForm, mapCoeffs_wordBasis, hc₀]
    rfl
  have eq : (fun u : Words ν ↦ Φ (wordBasis k I u.1)) = fun u ↦ evalAt v hv0 ∘ p u := by
    funext u w
    simp only [Function.comp_apply, p, map_vermaForm, mapCoeffs_wordBasis, hcq]
    rfl
  have hrank : shapovalovRank (classicalCoeff ℚ D n) ν ≤ shapovalovRank (qCoeff R v Λ) ν := by
    rw [shapovalovRank, shapovalovRank, range_shapovalovMap, range_shapovalovMap]
    change finrank ℚ (Submodule.span ℚ (Set.range fun u : Words ν ↦ Φ₀ (wordBasis ℚ I u.1))) ≤
      finrank k (Submodule.span k (Set.range fun u : Words ν ↦ Φ (wordBasis k I u.1)))
    rw [e₀, eq]
    exact Submodule.finrank_span_le_of_comp_ratHom _ _ hinj p
  -- Step 2: `Z ⊆ ker Φ`
  have hZker : Z ≤ (LinearMap.ker (Φ.domRestrict V)).map V.subtype := by
    intro y hy
    have hyV : y ∈ V := tildeSpan_le_weightSpace D _ n ν hy
    refine ⟨⟨y, hyV⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.domRestrict_apply,
      shapovalovMap_eq_zero_iff _ hyV, ← toVerma_mem_maxSubmodule_iff hvn hR]
    exact fPowSubmodule_le_maxSubmodule hR hvn hΛ (toVerma_mem_fPowSubmodule hvn hy)
  -- Step 3: `dim Z₀ ≤ dim Z`
  have hZZ : finrank ℚ Z₀ ≤ finrank k Z := by
    set g := tildeFamily D n ν
    have hZ₀ : Z₀ =
        Submodule.span ℚ (Set.range fun t ↦ mapCoeffs (evalAt 1 one_ne_zero) (g t)) := by
      rw [span_mapCoeffs_tildeFamily]
      simp only [evalAt_laurentT_pow, one_pow, Z₀]
    have hZ : Z = Submodule.span k (Set.range fun t ↦ mapCoeffs (evalAt v hv0) (g t)) := by
      rw [span_mapCoeffs_tildeFamily]
      simp only [evalAt_laurentT_pow, Z]
    rw [hZ₀, hZ]
    refine finrank_span_mapCoeffs_le _ _ hinj ν g (fun t ↦ ?_) (fun t ↦ ?_)
    · refine tildeSpan_le_weightSpace D (fun _ ↦ (1 : ℚ)) n ν ?_
      rw [← show Z₀ = tildeSpan D (fun _ ↦ (1 : ℚ)) n ν from rfl, hZ₀]
      exact Submodule.subset_span ⟨t, rfl⟩
    · refine tildeSpan_le_weightSpace D (fun i ↦ v ^ D.d i) n ν ?_
      rw [← show Z = tildeSpan D (fun i ↦ v ^ D.d i) n ν from rfl, hZ]
      exact Submodule.subset_span ⟨t, rfl⟩
  -- Step 4: `ker Φ₀ ⊆ Z₀`
  have : FiniteDimensional ℚ Z₀ :=
    Submodule.finiteDimensional_of_le (tildeSpan_le_weightSpace D (fun _ ↦ (1 : ℚ)) n ν)
  have : FiniteDimensional k Z :=
    Submodule.finiteDimensional_of_le (tildeSpan_le_weightSpace D (fun i ↦ v ^ D.d i) n ν)
  have hker₀ : finrank ℚ (LinearMap.ker (Φ₀.domRestrict V₀)) ≤ finrank ℚ Z₀ := by
    rw [← Submodule.finrank_map_subtype_eq]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mem_tildeSpan_of_shapovalovMap_eq_zero D n y.2 hy
  -- the dimension count
  have h1 := LinearMap.finrank_range_add_finrank_ker (Φ.domRestrict V)
  have h2 := LinearMap.finrank_range_add_finrank_ker (Φ₀.domRestrict V₀)
  have hVV₀ : finrank k V = finrank ℚ V₀ := by rw [finrank_weightSpace, finrank_weightSpace]
  have hZk : finrank k Z ≤ finrank k (LinearMap.ker (Φ.domRestrict V)) := by
    rw [← Submodule.finrank_map_subtype_eq]; exact Submodule.finrank_mono hZker
  change finrank ℚ (LinearMap.range (Φ₀.domRestrict V₀)) ≤
    finrank k (LinearMap.range (Φ.domRestrict V)) at hrank
  refine ⟨fun y hy hΦ ↦ ?_, ?_⟩
  swap
  · change finrank k (LinearMap.range (Φ.domRestrict V)) =
      finrank ℚ (LinearMap.range (Φ₀.domRestrict V₀))
    omega
  have hEq : Z = (LinearMap.ker (Φ.domRestrict V)).map V.subtype :=
    Submodule.eq_of_le_of_finrank_le hZker (by rw [Submodule.finrank_map_subtype_eq]; omega)
  rw [hEq]
  exact ⟨⟨y, hy⟩, hΦ, rfl⟩

/-- The kernel of the quantum Shapovalov pairing on `'f_ν`, for `Λ` dominant and `v`
transcendental: `S(w, y) = 0` for all `w` iff `y` is a combination of quantum Serre products and
words `a θᵢ^{⟨i,Λ⟩+1}` of weight `ν`. -/
theorem shapovalovMap_eq_zero_iff_mem_tildeSpan [Finite I] (hv : Transcendental ℚ v)
    (hR : R.IsXRegular) (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) {ν : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ LusztigF.weightSpace k ν) :
    shapovalovMap (qCoeff R v Λ) ν y = 0 ↔
      y ∈ tildeSpan D (fun i ↦ v ^ D.d i) (fun i ↦ (Λ (R.coroot i)).toNat) ν := by
  have hvn : ∀ n : ℕ, 0 < n → v ^ n ≠ 1 := fun n hn ↦ pow_ne_one_of_transcendental hv hn
  refine ⟨(shapovalov_comparison hv hR hΛ ν).1 y hy, fun h ↦ ?_⟩
  rw [shapovalovMap_eq_zero_iff _ hy, ← toVerma_mem_maxSubmodule_iff hvn hR]
  exact fPowSubmodule_le_maxSubmodule hR hvn hΛ (toVerma_mem_fPowSubmodule hvn h)

/-- The rank of the quantum Shapovalov pairing on `'f_ν` equals the rank of the classical one. -/
theorem shapovalovRank_qCoeff [Finite I] (hv : Transcendental ℚ v) (hR : R.IsXRegular)
    (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) (ν : I →₀ ℕ) :
    shapovalovRank (qCoeff R v Λ) ν =
      shapovalovRank (classicalCoeff ℚ D fun i ↦ (Λ (R.coroot i)).toNat) ν :=
  (shapovalov_comparison hv hR hΛ ν).2

/-- **Quantum target 2** ([Lus] 3.5.6, 6.2.3 (a); [Jan] 5.15, finite type). For a Cartan datum
with finitely many simple roots, an `X`-regular root datum, `v` transcendental over `ℚ` and `Λ`
dominant, the maximal submodule of the Verma module `M_q(Λ)` is `Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ`. -/
theorem maxSubmodule_eq_fPowSubmodule [Finite I] (hv : Transcendental ℚ v) (hR : R.IsXRegular)
    (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) : maxSubmodule R v Λ = fPowSubmodule R v Λ := by
  have hvn : ∀ n : ℕ, 0 < n → v ^ n ≠ 1 := fun n hn ↦ pow_ne_one_of_transcendental hv hn
  refine le_antisymm (fun m hm ↦ ?_) (fPowSubmodule_le_maxSubmodule hR hvn hΛ)
  obtain ⟨y, rfl⟩ := toVerma_surjective hvn m
  rw [toVerma_mem_maxSubmodule_iff hvn hR] at hm
  rw [← sum_weightProj y, map_sum]
  refine Submodule.sum_mem _ fun ν _ ↦ toVerma_mem_fPowSubmodule hvn
    ((shapovalovMap_eq_zero_iff_mem_tildeSpan hv hR hΛ (FreeAlgebra.weightProj_mem ν y)).1 ?_)
  rw [shapovalovMap_eq_zero_iff _ (FreeAlgebra.weightProj_mem ν y)]
  intro w
  rw [vermaForm_weightProj, hm w, ite_self]

end VermaModule

/-- **`L̃_q(Λ) ≅ L_q(Λ)`** ([Lus] 3.5.6, 6.2.3 (a); [Jan] 5.15, finite type): for
`v` transcendental
over `ℚ`, an `X`-regular root datum with finitely many simple roots and `Λ` dominant, the
surjection `L̃_q(Λ) = M_q(Λ) ⧸ Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ → L_q(Λ)` is injective. -/
theorem FPowQuotient.toIrreducibleModule_injective [Finite I] (hv : Transcendental ℚ v)
    (hR : R.IsXRegular) (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    Function.Injective (FPowQuotient.toIrreducibleModule hR hv' hΛ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [FPowQuotient.toIrreducibleModule, ← Submodule.mkQ_apply, Submodule.factor_mk,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    VermaModule.maxSubmodule_eq_fPowSubmodule hv hR hΛ] at hx
  exact (Submodule.Quotient.mk_eq_zero _).2 hx

/-- The isomorphism `L̃_q(Λ) ≃ L_q(Λ)` of `U`-modules (quantum target 2, [Lus] 6.2.3 (a)),
for `v` transcendental over `ℚ`, an `X`-regular root datum with finitely many simple
roots and `Λ` dominant. -/
def FPowQuotient.equivIrreducibleModule [Finite I] (hv : Transcendental ℚ v) (hR : R.IsXRegular)
    (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    FPowQuotient R v Λ ≃ₗ[QuantumGroup R v] IrreducibleModule R v Λ :=
  LinearEquiv.ofBijective (FPowQuotient.toIrreducibleModule hR hv' hΛ)
    ⟨FPowQuotient.toIrreducibleModule_injective hv hR hv' hΛ,
      FPowQuotient.toIrreducibleModule_surjective hR hv' hΛ⟩

/-- **The characters of `L_q(Λ)` are classical** ([Lus] 6.2.3 (a), 33.1.3 (d); [Jan] 5.15
(finite type)). Let `(I, ·)` be a Cartan datum with `I` finite, `R` an `X`-regular root
datum, `v ∈ k`
transcendental over `ℚ` (`k` of characteristic zero) and `Λ` dominant. Let `L(Λ')` be the
irreducible highest-weight module of the Kac–Moody algebra `𝔤(A)` of the Cartan matrix `A` of the
datum, for any realization `P` of `A` over any field `K` of characteristic zero, with
`⟨Λ', αᵢ^∨⟩ = ⟨i, Λ⟩`. Then for every `ν ∈ ℕ[I]`,
`dim L_q(Λ)^{Λ - Σ νᵢ i'} = dim L(Λ')_{Λ' - Σ νᵢ αᵢ}`. -/
theorem IrreducibleModule.finrank_weightSpace_eq [Fintype I] (hv : Transcendental ℚ v)
    (hR : R.IsXRegular) (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (P : Matrix.Realization D.cartanMatrix K H) {Λ' : Module.Dual K H}
    (hΛ' : ∀ i, Λ' (P.coroot i) = Λ (R.coroot i)) (ν : I →₀ ℕ) :
    finrank k (weightSpace R v (IrreducibleModule R v Λ) (Λ - R.rootSum ν)) =
      finrank K (LieModule.weightSpaceOfMap
        (Matrix.Realization.KacMoodyAlgebra.IrreducibleModule P Λ')
        (Matrix.Realization.KacMoodyAlgebra.h P) (Λ' - P.rootOf fun i ↦ (ν i : ℤ))) := by
  have hvn : ∀ n : ℕ, 0 < n → v ^ n ≠ 1 := fun n hn ↦ pow_ne_one_of_transcendental hv hn
  have hn : ∀ i, Λ' (P.coroot i) = ((Λ (R.coroot i)).toNat : K) := fun i ↦ by
    rw [hΛ', ← Int.cast_natCast, Int.toNat_of_nonneg (hΛ i)]
  rw [VermaModule.finrank_weightSpace_irreducibleModule hvn hR,
    LusztigF.finrank_weightSpace_irreducibleModule D P hn, shapovalovRank_classicalCoeff,
    VermaModule.shapovalovRank_qCoeff hv hR hΛ]

/-! ### Lusztig's case `k = ℚ(v)` -/

/-- **Quantum target 2 over `ℚ(v)`** ([Lus] 3.5.6, 6.2.3 (a)): for an `X`-regular root datum
with finitely many simple roots and `Λ` dominant, the maximal submodule of the Verma module
`M_q(Λ)` over `ℚ(v)` is `Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ`, i.e. `L̃_q(Λ) = L_q(Λ)`. -/
theorem VermaModule.maxSubmodule_eq_fPowSubmodule_ratFunc [Finite I] (hR : R.IsXRegular)
    (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    maxSubmodule R (RatFunc.X : RatFunc ℚ) Λ = fPowSubmodule R RatFunc.X Λ :=
  haveI : NeZero (RatFunc.X : RatFunc ℚ) := ⟨RatFunc.X_ne_zero⟩
  maxSubmodule_eq_fPowSubmodule transcendental_ratFunc_X hR hΛ

/-- **The characters of `L_q(Λ)` over `ℚ(v)` are classical** ([Lus] 6.2.3 (a), 33.1.3 (d)): for an
`X`-regular root datum with finitely many simple roots and `Λ` dominant,
`dim L_q(Λ)^{Λ - Σ νᵢ i'} = dim L(Λ')_{Λ' - Σ νᵢ αᵢ}` for the classical irreducible module
`L(Λ')` of `𝔤(A)` (any realization over any field of characteristic zero) with
`⟨Λ', αᵢ^∨⟩ = ⟨i, Λ⟩`. -/
theorem IrreducibleModule.finrank_weightSpace_eq_ratFunc [Fintype I] (hR : R.IsXRegular)
    (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) {K H : Type*} [Field K] [CharZero K] [AddCommGroup H]
    [Module K H] [FiniteDimensional K H] (P : Matrix.Realization D.cartanMatrix K H)
    {Λ' : Module.Dual K H} (hΛ' : ∀ i, Λ' (P.coroot i) = Λ (R.coroot i)) (ν : I →₀ ℕ) :
    finrank (RatFunc ℚ)
        (weightSpace R (RatFunc.X : RatFunc ℚ) (IrreducibleModule R (RatFunc.X : RatFunc ℚ) Λ)
          (Λ - R.rootSum ν)) =
      finrank K (LieModule.weightSpaceOfMap
        (Matrix.Realization.KacMoodyAlgebra.IrreducibleModule P Λ')
        (Matrix.Realization.KacMoodyAlgebra.h P) (Λ' - P.rootOf fun i ↦ (ν i : ℤ))) :=
  haveI : NeZero (RatFunc.X : RatFunc ℚ) := ⟨RatFunc.X_ne_zero⟩
  finrank_weightSpace_eq transcendental_ratFunc_X hR hΛ P hΛ' ν

end QuantumGroup
