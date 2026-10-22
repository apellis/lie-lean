/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.GVerma
import LieLean.Algebra.QuantumGroup.GabberKac.SerreSpan

/-!
# Gradings used in the syzygy step of the super Gabber–Kac theorem

Let `f : T(V) → U = U(G̃(A, τ))`, `vᵢ ↦ fᵢ`, with `T(V) = FreeAlgebra K ι` graded by `ℕ[ι]`
(`FreeAlgebra.wordSpan`, `FreeAlgebra.weightProj`). This file collects the compatibilities of this
grading with the weight grading of `U`, and the stability properties of the Serre ideal `S`,
used in the syzygy step of the proof of the super Gabber–Kac theorem
(`KacMoody/Super/GabberKac/Syzygy.lean`).

## Main results

* `Matrix.Realization.SuperEnveloping.wProj_fAlg`: `f` intertwines the two weight projections.
* `Matrix.Realization.SuperEnveloping.weightProj_mem_fPre`: `f⁻¹(R)` is graded.
* `Matrix.Realization.SuperEnveloping.fAlg_weightProj_mem_of_mem_gIdeal`: the weight components
  of the left ideal `J = T(V) f⁻¹(R)` are spanned by products `a r` with `r ∈ f⁻¹(R)` of smaller
  weight.
* `Matrix.Realization.SuperEnveloping.exists_eq_sum_mul_ι`: an element of `T(V)` of weight
  `ν ≠ 0` is `∑ᵢ cᵢ vᵢ` with `cᵢ` of weight `ν - αᵢ`.
* `Matrix.Realization.SuperEnveloping.map_mem_serreIdeal`: automorphisms of `U` compatible with the
  super commutator and preserving the Serre elements up to `S` preserve `S`; in particular the
  parity involution (`parity_mem_serreIdeal`) and the Chevalley involution
  (`omega_mem_serreIdeal`) preserve `S`.
* `Matrix.Realization.SuperEnveloping.superBracket_mem_of_mem_left`: a parity-stable ideal `I`
  satisfies `[I, G̃] ⊆ I`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.2–1.4.
-/

open Module

noncomputable section

namespace Matrix.Realization.SuperEnveloping

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

/-- The enveloping superalgebra `U(G̃(A, τ))`. -/
local notation "𝒰" => SuperEnveloping P p

/-! ### Weights of words -/

/-- The root-lattice coordinates of `ν ∈ ℕ[ι]`. -/
def natVec (ν : ι →₀ ℕ) : ι → ℤ := fun i ↦ ν i

omit [Fintype ι] [DecidableEq ι] in
lemma natVec_injective : Function.Injective (natVec (ι := ι)) := fun a b h ↦
  Finsupp.ext fun i ↦ by simpa [natVec] using congrFun h i

omit [Fintype ι] in
lemma wordVec_eq_natVec (w : List ι) : wordVec w = natVec (LusztigF.wordWeight w) := by
  induction w with
  | nil => funext i; simp [natVec]
  | cons j w ih =>
    funext i
    rw [wordVec_cons, LusztigF.wordWeight_cons, Pi.add_apply, ih]
    rcases eq_or_ne i j with rfl | hij
    · simp [natVec]
    · simp [natVec, hij]

omit [Fintype ι] [DecidableEq ι] in
lemma word_eq_wordBasis (w : List ι) :
    FreeAlgebra.word (R := K) w = FreeAlgebra.wordBasis K ι w := by
  induction w with
  | nil => rw [FreeAlgebra.word_nil, FreeAlgebra.wordBasis_nil]
  | cons j w ih => rw [FreeAlgebra.word_cons, ih, FreeAlgebra.ι_mul_wordBasis]

lemma fAlg_wordBasis_mem_weightSpace (w : List ι) :
    fAlg P p (FreeAlgebra.wordBasis K ι w) ∈
      weightSpace P p (-P.rootOf (natVec (LusztigF.wordWeight w))) := by
  rw [← word_eq_wordBasis, ← wordVec_eq_natVec]
  exact fAlg_word_mem_weightSpace P p w

lemma fAlg_mem_weightSpace_of_mem_wordSpan {ν : ι →₀ ℕ} {t : FreeAlgebra K ι}
    (ht : t ∈ FreeAlgebra.wordSpan K ν) :
    fAlg P p t ∈ weightSpace P p (-P.rootOf (natVec ν)) := by
  induction ht using FreeAlgebra.wordSpan_induction with
  | word w hw => rw [← hw]; exact fAlg_wordBasis_mem_weightSpace P p w
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

variable [CharZero K]

/-- `f` intertwines the projections onto weights. -/
lemma wProj_fAlg (ν : ι →₀ ℕ) (t : FreeAlgebra K ι) :
    wProj P p (-P.rootOf (natVec ν)) (fAlg P p t) =
      fAlg P p (FreeAlgebra.weightProj K ν t) := by
  induction t using FreeAlgebra.induction_wordBasis with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul c x hx => rw [map_smul, map_smul, hx, map_smul, map_smul]
  | word w =>
    rw [FreeAlgebra.weightProj_wordBasis]
    split_ifs with hw
    · rw [wProj_of_mem P p]
      rw [← hw]
      exact fAlg_wordBasis_mem_weightSpace P p w
    · rw [map_zero]
      exact wProj_of_mem_ne P p
        (fun h ↦ hw (natVec_injective (P.rootOf_injective (neg_injective h))))
        (fAlg_wordBasis_mem_weightSpace P p w)

variable {P p}

/-- A subspace of `U` stable under `ad 𝔥` is stable under the weight projections. -/
lemma wProj_mem {N : Submodule K 𝒰} (hN : ∀ a, ∀ x ∈ N, superBracket P p (h P p a) x ∈ N)
    {x : 𝒰} (hx : x ∈ N) (μ : Dual K H) : wProj P p μ x ∈ N := by
  refine Submodule.iSup_induction _ (motive := fun x ↦ wProj P p μ x ∈ N)
    (le_iSup_inf_weightSpace P p N hN hx) (fun ν y hy ↦ ?_) (by simp) fun y z hy hz ↦ by
      rw [map_add]; exact add_mem hy hz
  by_cases hνμ : ν = μ
  · subst hνμ
    rw [wProj_of_mem P p hy.2]
    exact hy.1
  · rw [wProj_of_mem_ne P p hνμ hy.2]
    exact zero_mem _

/-- `f⁻¹(R)` is graded. -/
lemma weightProj_mem_fPre {t : FreeAlgebra K ι} (ht : t ∈ fPre P p) (ν : ι →₀ ℕ) :
    FreeAlgebra.weightProj K ν t ∈ fPre P p := by
  rw [mem_fPre, ← wProj_fAlg]
  exact wProj_mem (fun a x hx ↦ (isIdeal_maxIdeal P p).superBracket_mem _ (h_mem_gTilde P p a) x hx)
    ht _

/-- The image under `f` of the weight-`ν` component of `J = T(V) f⁻¹(R)` lies in any left ideal of
`U` containing the images of the elements of `f⁻¹(R)` of weights `μ ≤ ν`. -/
lemma fAlg_weightProj_mem_of_mem_gIdeal {M : Submodule 𝒰 𝒰} {t : FreeAlgebra K ι}
    (ht : t ∈ gIdeal P p) (ν : ι →₀ ℕ)
    (hM : ∀ μ ≤ ν, ∀ r ∈ fPre P p, r ∈ FreeAlgebra.wordSpan K μ → fAlg P p r ∈ M) :
    fAlg P p (FreeAlgebra.weightProj K ν t) ∈ M := by
  induction ht using Submodule.span_induction generalizing ν with
  | mem r hr => exact hM ν le_rfl _ (weightProj_mem_fPre hr ν) (FreeAlgebra.weightProj_mem ν r)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add]; exact add_mem (hy ν hM) (hz ν hM)
  | smul a y _ ih =>
    change fAlg P p (FreeAlgebra.weightProj K ν (a * y)) ∈ M
    induction a using FreeAlgebra.induction_wordBasis with
    | zero => simp
    | add a b ha hb => rw [add_mul, map_add, map_add]; exact add_mem ha hb
    | smul c a ha => rw [smul_mul_assoc, map_smul, map_smul]; exact M.smul_of_tower_mem c ha
    | word w =>
      rw [FreeAlgebra.weightProj_wordBasis_mul]
      split_ifs with hw
      · rw [map_mul]
        exact M.smul_mem _ (ih _ fun μ hμ ↦ hM μ (hμ.trans tsub_le_self))
      · simp

omit [CharZero K] [DecidableEq ι] in
/-- An element of `T(V)` of weight `ν ≠ 0` is `∑ᵢ cᵢ vᵢ` with `cᵢ` of weight `ν - αᵢ`. -/
lemma exists_eq_sum_mul_ι {ν : ι →₀ ℕ} (hν : ν ≠ 0) {t : FreeAlgebra K ι}
    (ht : t ∈ FreeAlgebra.wordSpan K ν) :
    ∃ c : ι → FreeAlgebra K ι, (∀ i, c i ∈ FreeAlgebra.wordSpan K (ν - Finsupp.single i 1)) ∧
      (∀ i, ν i = 0 → c i = 0) ∧ t = ∑ i, c i * FreeAlgebra.ι K i := by
  classical
  induction ht using FreeAlgebra.wordSpan_induction with
  | word w hw =>
    subst hw
    rcases List.eq_nil_or_concat' w with rfl | ⟨w', i, rfl⟩
    · exact absurd rfl hν
    · refine ⟨Pi.single i (FreeAlgebra.wordBasis K ι w'), fun j ↦ ?_, fun j hj ↦ ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Pi.single_eq_same]
          refine FreeAlgebra.wordBasis_mem_wordSpan_of_eq ?_
          simp [LusztigF.wordWeight_append]
        · rw [Pi.single_eq_of_ne hj]
          exact zero_mem _
      · rcases eq_or_ne j i with rfl | hji
        · simp [LusztigF.wordWeight_append] at hj
        · exact Pi.single_eq_of_ne hji _
      · rw [Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul])
          (by simp), Pi.single_eq_same, FreeAlgebra.wordBasis_append]
        simp
  | zero => exact ⟨0, fun _ ↦ zero_mem _, fun _ _ ↦ rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hc0, rfl⟩ := hx
    obtain ⟨d, hd, hd0, rfl⟩ := hy
    exact ⟨c + d, fun i ↦ add_mem (hc i) (hd i), fun i hi ↦ by simp [hc0 i hi, hd0 i hi],
      by simp [add_mul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc, hc0, rfl⟩ := hx
    exact ⟨a • c, fun i ↦ Submodule.smul_mem _ a (hc i), fun i hi ↦ by simp [hc0 i hi],
      by simp [Finset.smul_sum]⟩

/-! ### Stability of the Serre ideal -/

/-- An algebra endomorphism of `U` compatible with the super commutator and preserving `G̃(A, τ)`
intertwines the adjoint action. -/
lemma map_adRep {φ : 𝒰 →ₐ[K] 𝒰}
    (hφ : ∀ x y, φ (superBracket P p x y) = superBracket P p (φ x) (φ y))
    (hgT : ∀ x ∈ gTilde P p, φ x ∈ gTilde P p) (u z : 𝒰) :
    φ (adRep P p u z) = adRep P p (φ u) (φ z) := by
  revert z
  refine induction_on (q := fun u ↦ ∀ z, φ (adRep P p u z) = adRep P p (φ u) (φ z)) u
    (fun c z ↦ ?_) (fun i z ↦ ?_) (fun i z ↦ ?_) (fun a z ↦ ?_) ?_ ?_
  · simp [Algebra.algebraMap_eq_smul_one]
  · rw [adRep_e, hφ, adRep_of_mem_gTilde (hgT _ (e_mem_gTilde P p i))]
  · rw [adRep_f, hφ, adRep_of_mem_gTilde (hgT _ (f_mem_gTilde P p i))]
  · rw [adRep_h, hφ, adRep_of_mem_gTilde (hgT _ (h_mem_gTilde P p a))]
  · intro x y hx hy z
    simp only [map_add, LinearMap.add_apply, hx, hy]
  · intro x y hx hy z
    simp only [map_mul, Module.End.mul_apply, hx, hy]

/-- An algebra endomorphism of `U` compatible with the super commutator, preserving `G̃(A, τ)` and
mapping the Serre elements into `S` preserves `S`. -/
lemma map_mem_serreIdeal {φ : 𝒰 →ₐ[K] 𝒰}
    (hφ : ∀ x y, φ (superBracket P p x y) = superBracket P p (φ x) (φ y))
    (hgT : ∀ x ∈ gTilde P p, φ x ∈ gTilde P p)
    (hS : ∀ i j, i ≠ j → φ (serreE P p i j) ∈ serreIdeal P p ∧ φ (serreF P p i j) ∈ serreIdeal P p)
    {x : 𝒰} (hx : x ∈ serreIdeal P p) : φ x ∈ serreIdeal P p := by
  rw [mem_serreIdeal] at hx
  suffices ∀ y ∈ serreAd P p, φ ((toAd P p).symm y) ∈ serreIdeal P p from this _ hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, ⟨i, j, hij, rfl | rfl⟩, rfl⟩ := hy
    · exact (hS i j hij).1
    · exact (hS i j hij).2
  | zero => simp
  | add y y' _ _ hy hy' => simpa using (serreIdeal P p).add_mem hy hy'
  | smul u y _ hy =>
    change φ (adRep P p u ((toAd P p).symm y)) ∈ serreIdeal P p
    rw [map_adRep hφ hgT]
    exact adRep_mem_serreIdeal _ hy

lemma isHomog_serreE (i j : ι) :
    IsHomog P p (((-A i j).toNat + 1 : ℕ) * p i + p j) (serreE P p i j) :=
  isHomog_adE i _ (isHomog_e P p j)

/-- The parity involution preserves `S`. -/
lemma parity_mem_serreIdeal {x : 𝒰} (hx : x ∈ serreIdeal P p) :
    parity P p x ∈ serreIdeal P p := by
  refine map_mem_serreIdeal (parity_superBracket P p) (fun _ ↦ parity_mem_gTilde P p)
    (fun i j hij ↦ ⟨?_, ?_⟩) hx
  · rw [isHomog_serreE i j]
    exact Submodule.smul_mem _ _ (serreE_mem_serreIdeal P p hij)
  · rw [← omega_serreE, ← omega_parity, isHomog_serreE i j, map_smul, omega_serreE]
    exact Submodule.smul_mem _ _ (serreF_mem_serreIdeal P p hij)

/-- The Chevalley involution preserves `S`. -/
lemma omega_mem_serreIdeal {x : 𝒰} (hx : x ∈ serreIdeal P p) :
    omega P p x ∈ serreIdeal P p := by
  refine map_mem_serreIdeal (omega_superBracket P p) (fun _ ↦ omega_mem_gTilde P p)
    (fun i j hij ↦ ⟨?_, ?_⟩) hx
  · rw [omega_serreE]
    exact serreF_mem_serreIdeal P p hij
  · rw [← omega_serreE, ← AlgHom.comp_apply, omega_comp_omega]
    exact parity_mem_serreIdeal (serreE_mem_serreIdeal P p hij)

/-- A parity-stable ideal `I` of `G̃(A, τ)` satisfies `[I, G̃(A, τ)] ⊆ I`. -/
lemma superBracket_mem_of_mem_left {I : Submodule K 𝒰} (hI : IsIdeal P p I)
    (hσ : ∀ x ∈ I, parity P p x ∈ I) {y x : 𝒰} (hy : y ∈ I) (hx : x ∈ gTilde P p) :
    superBracket P p y x ∈ I := by
  refine induction_parity P p (N := I) (q := fun y ↦ superBracket P p y x ∈ I) hσ
    (fun a y hy hya ↦ ?_) (fun y y' h h' ↦ ?_) hy
  · refine induction_parity P p (N := gTilde P p) (q := fun x ↦ superBracket P p y x ∈ I)
      (fun _ ↦ parity_mem_gTilde P p) (fun b x hx hxb ↦ ?_) (fun x x' h h' ↦ ?_) hx
    · rw [superBracket_swap hxb hya]
      exact I.neg_mem (I.smul_mem _ (hI.superBracket_mem x hx y hy))
    · rw [superBracket_add_right]; exact I.add_mem h h'
  · rw [superBracket_add_left]; exact I.add_mem h h'

end Matrix.Realization.SuperEnveloping

end
