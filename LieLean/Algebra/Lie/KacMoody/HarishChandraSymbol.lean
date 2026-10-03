/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HarishChandraSymmetrization

/-!
# The PBW leading symbol of degreewise symmetrization

## Main definitions

* `SymmetricPower.toSymmetricAlgebra`: the commutative product on symmetric tensors.
* `UniversalEnvelopingAlgebra.symmetrizationPowerFiltered`: the actual filtered lift.

## Main results

* `symmetrizationPower_mem_filtration`: the lift has PBW degree at most `n`.
* `symmetrizationPower_toGr`: its degree `n` symbol is the canonical graded PBW image.

## References

The argument is reconstructed from the permutation average and the production graded
PBW API. It supplies the symbol calculation underlying Etingof, MIT 18.757 (Fall 2023),
Lecture 13, §13.3, proof of Theorem 13.5 (as cited by the imported construction).
The source works over `ℂ`; the calculation here holds for every Lie algebra over a field, in
degree `n` whenever `n! ≠ 0` in the field.
It does not assert Chevalley restriction or the Harish-Chandra isomorphism.
-/

noncomputable section

namespace SymmetricPower

variable {K : Type} {M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Commutative multiplication of the degree-one generators, descended to the existing
symmetric tensor quotient. No basis or finite-dimensionality is needed. -/
def toSymmetricAlgebra (n : ℕ) :
    SymmetricPower K (Fin n) M →ₗ[K] SymmetricAlgebra K M :=
  liftSymmetric
    ((MultilinearMap.mkPiAlgebra K (Fin n) (SymmetricAlgebra K M)).compLinearMap
      (fun _ => SymmetricAlgebra.ι K M)) (by
        intro e v
        simpa only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
          Function.comp_apply] using Equiv.prod_comp e (fun i => SymmetricAlgebra.ι K M (v i)))

@[simp] theorem toSymmetricAlgebra_tprod (n : ℕ) (v : Fin n → M) :
    toSymmetricAlgebra n (tprod K v) = ∏ i, SymmetricAlgebra.ι K M (v i) := by
  simp [toSymmetricAlgebra]

end SymmetricPower

namespace UniversalEnvelopingAlgebra

variable {K : Type} {L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- Ordered words of length `n` lie in filtration `n`, including the empty word. -/
theorem ofFn_prod_mem_filtration (n : ℕ) (v : Fin n → L) :
    (List.ofFn (fun i => ι K (v i))).prod ∈ filtration K L n := by
  simpa only [List.map_ofFn, List.length_ofFn, Function.comp_def] using
    (list_prod_mem_filtration (R := K) (List.ofFn v))

/-- Degreewise symmetrization has PBW degree at most its tensor degree.
This part works over every field, even when the factorial normalization degenerates. -/
theorem symmetrizationPower_mem_filtration (n : ℕ) (s : SymmetricPower K (Fin n) L) :
    symmetrizationPower n s ∈ filtration K L n := by
  have hs : s ∈ Submodule.span K (Set.range (SymmetricPower.tprod K)) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [symmetrizationPower_tprod]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun e _ =>
      ofFn_prod_mem_filtration n (v ∘ e))
  | zero => simpa only [map_zero] using (filtration K L n).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (filtration K L n).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (filtration K L n).smul_mem a hx

/-- The normalized symmetrization, with its actual PBW filtration bound. -/
def symmetrizationPowerFiltered (n : ℕ) :
    SymmetricPower K (Fin n) L →ₗ[K] filtration K L n :=
  (symmetrizationPower n).codRestrict _ (symmetrizationPower_mem_filtration n)

/-- The symbol of any ordered word is the commutative product of its generators.
This is a direct consequence of the production maps `toGr_mul` and graded PBW. -/
theorem ofFn_prod_toGr (n : ℕ) (v : Fin n → L) :
    toGr K L n ⟨_, ofFn_prod_mem_filtration n v⟩ =
      symmetricAlgebraToAssociatedGraded K L (∏ i, SymmetricAlgebra.ι K L (v i)) := by
  induction n with
  | zero => simpa using (toGr_zero_one (R := K) (L := L))
  | succ n ih =>
    rw [Fin.prod_univ_succ, map_mul, symmetricAlgebraToAssociatedGraded_ι, ← ih,
      toGr_mul]
    apply toGr_congr (by omega)
    simp only [List.ofFn_succ, List.prod_cons]

/-- Leading-symbol compatibility assuming exactly the degreewise normalization needed.
In particular it applies in positive characteristic whenever `n!` is nonzero. -/
theorem symmetrizationPower_toGr_of_factorial_ne_zero (n : ℕ)
    (hn : (n.factorial : K) ≠ 0) (s : SymmetricPower K (Fin n) L) :
    toGr K L n (symmetrizationPowerFiltered n s) =
      symmetricAlgebraToAssociatedGraded K L (SymmetricPower.toSymmetricAlgebra n s) := by
  have hm : (toGr K L n).comp (symmetrizationPowerFiltered n) =
      (symmetricAlgebraToAssociatedGraded K L).toLinearMap.comp
        (SymmetricPower.toSymmetricAlgebra n) := by
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top K (Fin n) L)
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      SymmetricPower.toSymmetricAlgebra_tprod]
    have he : symmetrizationPowerFiltered n (SymmetricPower.tprod K v) =
        (n.factorial : K)⁻¹ • ∑ e : Equiv.Perm (Fin n),
          (⟨_, ofFn_prod_mem_filtration n (v ∘ e)⟩ : filtration K L n) := by
      apply Subtype.ext
      simp [symmetrizationPowerFiltered, symmetrizationPower_tprod]
    have hp (e : Equiv.Perm (Fin n)) :
        (∏ i, SymmetricAlgebra.ι K L (v (e i))) = ∏ i, SymmetricAlgebra.ι K L (v i) :=
      Equiv.prod_comp e (fun i => SymmetricAlgebra.ι K L (v i))
    rw [he, map_smul, map_sum]
    simp only [ofFn_prod_toGr, Function.comp_apply, hp,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hn, one_smul]
  exact LinearMap.congr_fun hm s

/-- Normalized symmetrization has precisely the commutative product as its PBW symbol.
This holds in every degree, including zero, and in arbitrary dimension.
The proof is reconstructed; no HC image or restriction theorem is assumed. -/
theorem symmetrizationPower_toGr [CharZero K] (n : ℕ)
    (s : SymmetricPower K (Fin n) L) :
    toGr K L n (symmetrizationPowerFiltered n s) =
      symmetricAlgebraToAssociatedGraded K L (SymmetricPower.toSymmetricAlgebra n s) := by
  apply symmetrizationPower_toGr_of_factorial_ne_zero
  exact_mod_cast n.factorial_ne_zero

/-- The actual central lift constructed from an invariant tensor has this same symbol.
This is the filtered central-element input for the subsequent HC degree induction,
not a claim that all Weyl-invariant Cartan symbols have been lifted. -/
theorem symmetrizationPowerToCenter_toGr [CharZero K] (n : ℕ)
    (s : invariantSymmetricPower (K := K) (L := L) n) :
    toGr K L n
      ⟨(symmetrizationPowerToCenter n s : UniversalEnvelopingAlgebra K L),
        symmetrizationPower_mem_filtration n s.val⟩ =
      symmetricAlgebraToAssociatedGraded K L
        (SymmetricPower.toSymmetricAlgebra n s.val) :=
  symmetrizationPower_toGr n s.val

/-- In positive degrees the lift drops one filtration step exactly when its commutative
product vanishes. The forward implication uses the production graded PBW injectivity. -/
theorem symmetrizationPower_mem_filtration_iff [CharZero K] (n : ℕ)
    (s : SymmetricPower K (Fin (n + 1)) L) :
    symmetrizationPower (n + 1) s ∈ filtration K L n ↔
      SymmetricPower.toSymmetricAlgebra (n + 1) s = 0 := by
  change ((symmetrizationPowerFiltered (n + 1) s : filtration K L (n + 1)) :
    UniversalEnvelopingAlgebra K L) ∈ filtration K L n ↔ _
  rw [← toGr_succ_eq_zero_iff (symmetrizationPowerFiltered (n + 1) s),
    symmetrizationPower_toGr]
  exact (symmetricAlgebraToAssociatedGraded_bijective K L).injective.eq_iff' (map_zero _)

end UniversalEnvelopingAlgebra
