/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.GabberKac

/-!
# Ranks under specialization

Linear algebra used to compare the characters of the quantum and classical irreducible
highest-weight modules (`LieLean.Algebra.QuantumGroup.Character`).

* `Submodule.finrank_span_le_of_comp_ratHom`: for vectors `p a ∈ Rⁿ` over a commutative ring `R`
  and ring homomorphisms `φ₁ : R → ℚ`, `φ₂ : R → F` with `φ₂` injective (`F` a field), the rank
  of the specialized vectors over `ℚ` is at most their rank over `F` (from the specialization
  lemma `LinearIndependent.of_comp_ratHom`).
* `Submodule.finrank_span_algebraMap_comp_le`: rational vectors have at most their rational rank
  over any field of characteristic zero (and at least it, by the previous item).
* `LusztigF.finrank_span_mapCoeffs_le`: the same comparison for families in a free algebra of a
  fixed weight, through the word coordinates.
* `LinearMap.finrank_range_eq_of_ker_eq`: linear maps with the same kernel have ranges of the
  same dimension.
* `LusztigF.shapovalovMap`, `LusztigF.shapovalovRank`: the Shapovalov-type pairing
  `y ↦ (S(w, y))_{w}` on the words of weight `ν`, and the dimension of its image on `'f_ν`.
-/

noncomputable section

open Module FreeAlgebra

namespace Submodule

/-- **Rank under specialization.** Let `p a ∈ Rⁿ` (`n` finite) for a commutative ring `R`, and
`φ₁ : R → ℚ`, `φ₂ : R → F` ring homomorphisms to `ℚ` and to a field `F`, with `φ₂` injective. Then
the rank over `ℚ` of the vectors `φ₁ ∘ p a` is at most the rank over `F` of the vectors
`φ₂ ∘ p a`. -/
theorem finrank_span_le_of_comp_ratHom {R F κ n : Type*} [CommRing R] [Field F] [Finite n]
    (φ₁ : R →+* ℚ) (φ₂ : R →+* F) (hφ₂ : Function.Injective φ₂) (p : κ → n → R) :
    finrank ℚ (span ℚ (Set.range fun a ↦ φ₁ ∘ p a)) ≤
      finrank F (span F (Set.range fun a ↦ φ₂ ∘ p a)) := by
  obtain ⟨a, ha⟩ := LusztigF.exists_linearIndependent_fin (K := ℚ) fun b ↦ φ₁ ∘ p b
  have h := LinearIndependent.of_comp_ratHom φ₁ φ₂ hφ₂ (fun t ↦ p (a t)) ha
  exact LusztigF.card_le_finrank_of_linearIndependent h fun t ↦ subset_span ⟨a t, rfl⟩

/-- Rational vectors, viewed over a field `K` of characteristic zero, have at most their rational
rank. -/
theorem finrank_span_algebraMap_comp_le {K κ n : Type*} [Field K] [CharZero K] [Finite n]
    (p : κ → n → ℚ) :
    finrank K (span K (Set.range fun a ↦ algebraMap ℚ K ∘ p a)) ≤
      finrank ℚ (span ℚ (Set.range p)) := by
  obtain ⟨κ', a, -, hsp, hli⟩ := exists_linearIndependent' ℚ p
  have := hli.finite_of_isNoetherian
  have := Fintype.ofFinite κ'
  let g : (n → ℚ) →ₗ[ℚ] (n → K) :=
    LinearMap.pi fun x ↦ (Algebra.linearMap ℚ K).comp (LinearMap.proj x)
  have hg : ∀ b, g (p b) = algebraMap ℚ K ∘ p b := fun _ ↦ rfl
  have hle : span K (Set.range fun b ↦ algebraMap ℚ K ∘ p b) ≤
      span K (Set.range fun t ↦ algebraMap ℚ K ∘ p (a t)) := by
    rw [span_le]
    rintro _ ⟨b, rfl⟩
    have hb : p b ∈ span ℚ (Set.range (p ∘ a)) := hsp ▸ subset_span ⟨b, rfl⟩
    have h1 : g (p b) ∈ (span ℚ (Set.range (p ∘ a))).map g := mem_map_of_mem hb
    rw [map_span, ← Set.range_comp] at h1
    change g (p b) ∈ _
    exact span_le_restrictScalars ℚ K _ h1
  calc finrank K (span K (Set.range fun b ↦ algebraMap ℚ K ∘ p b))
      ≤ finrank K (span K (Set.range fun t ↦ algebraMap ℚ K ∘ p (a t))) := finrank_mono hle
    _ ≤ Fintype.card κ' := finrank_range_le_card _
    _ = finrank ℚ (span ℚ (Set.range p)) := by
      rw [linearIndependent_iff_card_eq_finrank_span.1 hli, Set.finrank, hsp]

end Submodule

namespace LinearMap

/-- Two linear maps on a finite-dimensional space with the same kernel have ranges of the same
dimension. -/
theorem finrank_range_eq_of_ker_eq {K V M N : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : V →ₗ[K] M) (g : V →ₗ[K] N) (h : ker f = ker g) :
    finrank K (range f) = finrank K (range g) := by
  have h1 := finrank_range_add_finrank_ker f
  have h2 := finrank_range_add_finrank_ker g
  rw [h] at h1
  omega

end LinearMap

namespace LusztigF

variable {I : Type*}

/-- **Rank under specialization, in a free algebra.** Let `g t` be elements of
`FreeAlgebra R I` for a commutative ring `R`, and `φ₁ : R → ℚ`, `φ₂ : R → F` ring homomorphisms
with `φ₂` injective. If the specializations `mapCoeffs φ₁ (g t)` and `mapCoeffs φ₂ (g t)` all
have weight `ν`, then the dimension of the span of the former is at most that of the span of the
latter. -/
theorem finrank_span_mapCoeffs_le {R F κ : Type*} [CommRing R] [Field F] (φ₁ : R →+* ℚ)
    (φ₂ : R →+* F) (hφ₂ : Function.Injective φ₂) (ν : I →₀ ℕ) (g : κ → FreeAlgebra R I)
    (hg : ∀ t, mapCoeffs φ₁ (g t) ∈ wordSpan ℚ ν) (hg' : ∀ t, mapCoeffs φ₂ (g t) ∈ wordSpan F ν) :
    finrank ℚ (Submodule.span ℚ (Set.range fun t ↦ mapCoeffs φ₁ (g t))) ≤
      finrank F (Submodule.span F (Set.range fun t ↦ mapCoeffs φ₂ (g t))) := by
  have : FiniteDimensional ℚ (Submodule.span ℚ (Set.range fun t ↦ mapCoeffs φ₁ (g t))) :=
    Submodule.finiteDimensional_of_le (S₂ := weightSpace ℚ ν)
      (Submodule.span_le.2 (Set.range_subset_iff.2 hg))
  obtain ⟨b, hb⟩ := exists_linearIndependent_fin (K := ℚ) fun t ↦ mapCoeffs φ₁ (g t)
  have hb' : LinearIndependent ℚ fun s ↦ wordCoord ℚ ν (mapCoeffs φ₁ (g (b s))) := by
    refine hb.map (f := wordCoord ℚ ν) ?_
    rw [Submodule.disjoint_def]
    intro y hy hy0
    refine eq_zero_of_wordCoord_eq_zero ?_ hy0
    have hle : Submodule.span ℚ (Set.range ((fun t ↦ mapCoeffs φ₁ (g t)) ∘ b)) ≤
        wordSpan ℚ ν := by
      rw [Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      exact hg (b s)
    exact hle hy
  have h := LinearIndependent.of_comp_ratHom φ₁ φ₂ hφ₂
    (fun s (w : Words ν) ↦ (wordBasis R I).repr (g (b s)) w.1) (by
      convert hb' using 1
      funext s w
      simp only [Function.comp_apply, wordCoord_apply, wordBasis_repr_mapCoeffs])
  have hF : LinearIndependent F fun s ↦ mapCoeffs φ₂ (g (b s)) := by
    refine LinearIndependent.of_comp (wordCoord F ν) ?_
    convert h using 1
    funext s w
    simp only [Function.comp_apply, wordCoord_apply, wordBasis_repr_mapCoeffs]
  have : FiniteDimensional F (Submodule.span F (Set.range fun t ↦ mapCoeffs φ₂ (g t))) :=
    Submodule.finiteDimensional_of_le (S₂ := weightSpace F ν)
      (Submodule.span_le.2 (Set.range_subset_iff.2 hg'))
  exact card_le_finrank_of_linearIndependent hF fun s ↦ Submodule.subset_span ⟨b s, rfl⟩

/-! ### The Shapovalov map -/

variable {F : Type*} [Field F] [DecidableEq I]

/-- The Shapovalov-type map `y ↦ (S(w, y))_{w}` on the words `w` of weight `ν`, where
`S(w, y) = ε(E_w y)` is the pairing `LusztigF.vermaForm c`. -/
def shapovalovMap (c : I → (I →₀ ℕ) → F) (ν : I →₀ ℕ) : LusztigF F I →ₗ[F] (Words ν → F) :=
  LinearMap.pi fun w ↦ vermaForm c w.1

lemma shapovalovMap_apply (c : I → (I →₀ ℕ) → F) (ν : I →₀ ℕ) (y : LusztigF F I)
    (w : Words ν) : shapovalovMap c ν y w = vermaForm c w.1 y := rfl

/-- The rank of the Shapovalov-type pairing on `'f_ν`: the dimension of the image of `'f_ν`
under `LusztigF.shapovalovMap c ν`. -/
def shapovalovRank (c : I → (I →₀ ℕ) → F) (ν : I →₀ ℕ) : ℕ :=
  finrank F (LinearMap.range ((shapovalovMap c ν).domRestrict (weightSpace F ν)))

lemma range_shapovalovMap (c : I → (I →₀ ℕ) → F) (ν : I →₀ ℕ) :
    LinearMap.range ((shapovalovMap c ν).domRestrict (weightSpace F ν)) =
      Submodule.span F (Set.range fun u : Words ν ↦ shapovalovMap c ν (wordBasis F I u.1)) := by
  rw [LinearMap.range_domRestrict, weightSpace_eq_span, Submodule.map_span, ← Set.range_comp]
  rfl

/-- For `y ∈ 'f_ν`, `Φ(y) = 0` iff `S(w, y) = 0` for all words `w`. -/
lemma shapovalovMap_eq_zero_iff (c : I → (I →₀ ℕ) → F) {ν : I →₀ ℕ} {y : LusztigF F I}
    (hy : y ∈ weightSpace F ν) : shapovalovMap c ν y = 0 ↔ ∀ w, vermaForm c w y = 0 := by
  refine ⟨fun h w ↦ ?_, fun h ↦ funext fun w ↦ h w.1⟩
  by_cases hw : wordWeight w = ν
  · exact congr_fun h ⟨w, hw⟩
  · exact vermaForm_eq_zero_of_ne c w hw hy

/-- The pairing `S(w, ·)` only sees the component of the weight of `w`. -/
lemma vermaForm_weightProj (c : I → (I →₀ ℕ) → F) (w : List I) (ν : I →₀ ℕ)
    (y : LusztigF F I) :
    vermaForm c w (FreeAlgebra.weightProj F ν y) = if wordWeight w = ν then vermaForm c w y
      else 0 := by
  induction y using induction_wordBasis with
  | zero => simp
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]; split_ifs <;> simp
  | smul a y hy => rw [map_smul, map_smul, hy, map_smul]; split_ifs <;> simp
  | word u =>
    rw [FreeAlgebra.weightProj_wordBasis]
    by_cases hu : wordWeight u = ν
    · rw [ite_eq_left hu]
      split_ifs with hw
      · rfl
      · exact vermaForm_eq_zero_of_ne c w (hu ▸ hw) (wordBasis_mem_wordSpan u)
    · rw [ite_eq_right hu, map_zero]
      split_ifs with hw
      · exact (vermaForm_eq_zero_of_ne c w (hw ▸ Ne.symm hu) (wordBasis_mem_wordSpan u)).symm
      · rfl

end LusztigF
