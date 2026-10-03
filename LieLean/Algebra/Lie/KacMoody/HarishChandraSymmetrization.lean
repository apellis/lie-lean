/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.HarishChandraInvariance
import LieLean.Algebra.Lie.UniversalEnveloping.Graded
import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.Data.Fintype.Perm

/-!
# Degreewise PBW symmetrization toward the Harish-Chandra image

This constructs the normalized symmetrization into the actual enveloping algebra,
not a postulated inverse of Harish-Chandra restriction.

## Main definitions

* `SymmetricPower.liftSymmetric`: descent of a symmetric multilinear map.
* `SymmetricPower.diagonal`: infinitesimal insertion on the symmetric quotient.
* `UniversalEnvelopingAlgebra.symmetrizationPowerToCenter`: actual central lifts.
* `Matrix.Realization.KacMoodyAlgebra.harishChandraSymmetricPower`: their HC images.

## Main results

* `symmetrizationPower_diagonal_ad`: intertwining with commutators.
* `symmetrizationPower_mem_center`: invariant symmetric tensors give central elements.
* `symmetrizationPower_diagonal`: the normalized map sends `x^n` to `ι(x)^n`.
* `eval_harishChandraSymmetricPower`: the actual Verma central character of each lift.

The central-lift interface assumes characteristic zero. The elementary construction
and intertwining are proved more generally, without finite-dimensionality; in positive
characteristic the factorial inverse can vanish, and no nondegenerate lifting is claimed.
This covers the intended finite-dimensional characteristic-zero case. It does not
extend Chevalley restriction or the HC isomorphism beyond their classical scope.
Finite Cartan type, finite-dimensional Cartan, and the required symmetrization/invariant
form hypotheses must be retained when implementing those subsequent steps.

## References

P. Etingof, MIT 18.757 (Fall 2023), Lecture 13, §13.3, proof of Theorem 13.5:
https://ocw.mit.edu/courses/18-757-representations-of-lie-groups-fall-2023/mit18_757_f23_lec13.pdf
Lecture 14, §14.1, Theorem 14.1(iv)-(v), identifies the subsequent Chevalley/graded
restriction step. The elementary tensor construction below is reconstructed and works over any
characteristic-zero field; the source's complex semisimple HC isomorphism is NOT asserted here.
-/

noncomputable section

open TensorProduct

namespace SymmetricPower

variable {K I : Type} {M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- The universal linear lift of a permutation-invariant multilinear map. -/
def liftSymmetric (f : MultilinearMap K (fun _ : I => M) N)
    (hf : ∀ (e : Equiv.Perm I) (v : I → M), f (v ∘ e) = f v) :
    SymmetricPower K I M →ₗ[K] N where
  toFun := AddCon.lift (addConGen (Rel K I M)) (PiTensorProduct.lift f).toAddMonoidHom (by
    intro x y h
    change (PiTensorProduct.lift f) x = (PiTensorProduct.lift f) y
    induction h with
    | of x y h =>
      cases h with
      | perm e v => simpa only [PiTensorProduct.lift.tprod, Function.comp_def] using (hf e v).symm
    | refl => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | add _ _ ih₁ ih₂ => simpa only [map_add] using congrArg₂ (· + ·) ih₁ ih₂)
  map_add' := map_add _
  map_smul' r x := by
    induction x using AddCon.induction_on with
    | H x => exact (PiTensorProduct.lift f).map_smul r x

@[simp] theorem liftSymmetric_tprod
    (f : MultilinearMap K (fun _ : I => M) N)
    (hf : ∀ (e : Equiv.Perm I) (v : I → M), f (v ∘ e) = f v) (v : I → M) :
    liftSymmetric f hf (tprod K v) = f v := PiTensorProduct.lift.tprod _

/-- Sum of insertion of an endomorphism in every argument. -/
def diagonalMultilinear [Fintype I] [DecidableEq I] (D : M →ₗ[K] M)
    (f : MultilinearMap K (fun _ : I => M) N) : MultilinearMap K (fun _ : I => M) N :=
  ∑ i : I, f.compLinearMap (Function.update (fun _ => LinearMap.id) i D)

@[simp] theorem diagonalMultilinear_apply [Fintype I] [DecidableEq I]
    (D : M →ₗ[K] M) (f : MultilinearMap K (fun _ : I => M) N) (v : I → M) :
    diagonalMultilinear D f v = ∑ i : I, f (Function.update v i (D (v i))) := by
  simp only [diagonalMultilinear, sum_apply, MultilinearMap.compLinearMap_apply]
  congr 1
  funext i
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

/-- Diagonal insertion preserves permutation-invariance. -/
theorem diagonalMultilinear_perm [Fintype I] [DecidableEq I]
    (D : M →ₗ[K] M) (f : MultilinearMap K (fun _ : I => M) N)
    (hf : ∀ (e : Equiv.Perm I) (v : I → M), f (v ∘ e) = f v)
    (e : Equiv.Perm I) (v : I → M) :
    diagonalMultilinear D f (v ∘ e) = diagonalMultilinear D f v := by
  simp only [diagonalMultilinear_apply]
  apply Fintype.sum_equiv e
  intro i
  rw [← hf e (Function.update v (e i) (D (v (e i))))]
  congr 1
  funext j
  simp only [Function.comp_apply, Function.update_apply]
  by_cases h : j = i <;> simp [h, e.injective.eq_iff]

/-- The endomorphism induced on the symmetric power by diagonal insertion.
For `D = ad x` this is the infinitesimal adjoint action, not a group action. -/
def diagonal [Fintype I] [DecidableEq I] (D : M →ₗ[K] M) :
    SymmetricPower K I M →ₗ[K] SymmetricPower K I M :=
  liftSymmetric (diagonalMultilinear D (tprod K))
    (diagonalMultilinear_perm D (tprod K) (fun e v => tprod_equiv e v))

@[simp] theorem diagonal_tprod [Fintype I] [DecidableEq I]
    (D : M →ₗ[K] M) (v : I → M) :
    diagonal D (tprod K v) = ∑ i : I, tprod K (Function.update v i (D (v i))) := by
  rw [diagonal, liftSymmetric_tprod, diagonalMultilinear_apply]

end SymmetricPower

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type} {L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- Ordered multiplication of `n` Lie algebra generators. -/
def orderedMultilinear (n : ℕ) :
    MultilinearMap K (fun _ : Fin n => L) (UniversalEnvelopingAlgebra K L) :=
  (MultilinearMap.mkPiAlgebraFin K n _).compLinearMap (fun _ => (ι K).toLinearMap)

/-- The normalized permutation average of ordered multiplication, in every degree. -/
def symmetrizationMultilinear (n : ℕ) :
    MultilinearMap K (fun _ : Fin n => L) (UniversalEnvelopingAlgebra K L) :=
  (n.factorial : K)⁻¹ • ∑ e : Equiv.Perm (Fin n), (orderedMultilinear n).domDomCongr e

@[simp] theorem symmetrizationMultilinear_apply (n : ℕ) (v : Fin n → L) :
    symmetrizationMultilinear n v =
      (n.factorial : K)⁻¹ • ∑ e : Equiv.Perm (Fin n),
        (List.ofFn (fun i => ι K (v (e i)))).prod := by
  simp [symmetrizationMultilinear, orderedMultilinear, MultilinearMap.domDomCongr_apply]

/-- Averaging really removes the order of the tensor factors. -/
theorem symmetrizationMultilinear_perm (n : ℕ) (e : Equiv.Perm (Fin n))
    (v : Fin n → L) : symmetrizationMultilinear (K := K) n (v ∘ e) =
      symmetrizationMultilinear n v := by
  simp only [symmetrizationMultilinear_apply, Function.comp_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft e) _ _ (fun _ => rfl)

/-- Degreewise PBW symmetrization from the actual symmetric tensor quotient to `U(L)`.
This is the construction in Etingof, Lecture 13, §13.3, proof of Theorem 13.5;
its extension beyond the complex finite-dimensional case is elementary. -/
def symmetrizationPower (n : ℕ) :
    SymmetricPower K (Fin n) L →ₗ[K] UniversalEnvelopingAlgebra K L :=
  SymmetricPower.liftSymmetric (symmetrizationMultilinear n)
    (symmetrizationMultilinear_perm n)

@[simp] theorem symmetrizationPower_tprod (n : ℕ) (v : Fin n → L) :
    symmetrizationPower n (SymmetricPower.tprod K v) =
      (n.factorial : K)⁻¹ • ∑ e : Equiv.Perm (Fin n),
        (List.ofFn (fun i => ι K (v (e i)))).prod := by
  rw [symmetrizationPower, SymmetricPower.liftSymmetric_tprod,
    symmetrizationMultilinear_apply]

/-- The normalization sends a diagonal pure symmetric tensor to the actual power. -/
theorem symmetrizationPower_diagonal [CharZero K] (n : ℕ) (x : L) :
    symmetrizationPower n (SymmetricPower.tprod K (fun _ : Fin n => x)) =
      (ι K x) ^ n := by
  rw [symmetrizationPower_tprod]
  simp only [List.ofFn_const, List.prod_replicate, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast n.factorial_ne_zero

/-- The commutator with a generator differentiates an ordered product. -/
theorem lie_orderedMultilinear (x : L) (n : ℕ) (v : Fin n → L) :
    ⁅ι K x, orderedMultilinear (K := K) n v⁆ =
      ∑ i : Fin n, orderedMultilinear (K := K) n (Function.update v i ⁅x, v i⁆) := by
  induction n with
  | zero => simp [orderedMultilinear, LieRing.of_associative_ring_bracket]
  | succ n ih =>
    have hn (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simp only [orderedMultilinear, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebraFin_apply, LieHom.coe_toLinearMap,
      List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      Function.update_apply, Fin.succ_inj, Fin.succ_ne_zero, hn,
      ite_false, ite_true]
    have h := ih (fun i => v i.succ)
    simp only [orderedMultilinear, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebraFin_apply, LieHom.coe_toLinearMap, Function.update_apply] at h
    rw [LieRing.of_associative_ring_bracket] at h ⊢
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, ← Finset.mul_sum, ← h]
    noncomm_ring

/-- Infinitesimal adjoint equivariance of the averaged multilinear product. -/
theorem lie_symmetrizationMultilinear (x : L) (n : ℕ) (v : Fin n → L) :
    ⁅ι K x, symmetrizationMultilinear (K := K) n v⁆ =
      ∑ i : Fin n, symmetrizationMultilinear (K := K) n
        (Function.update v i ⁅x, v i⁆) := by
  simp only [symmetrizationMultilinear, smul_apply, sum_apply,
    MultilinearMap.domDomCongr_apply, lie_smul, lie_sum, lie_orderedMultilinear]
  rw [← Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply Fintype.sum_equiv e
  intro i
  congr 1
  funext j
  simp only [Function.update_apply]
  by_cases h : j = i <;> simp [h, e.injective.eq_iff]

/-- Degreewise symmetrization intertwines the infinitesimal adjoint action with
commutators in `U(L)`. This is the equivariance used in Etingof §13.3 to lift
invariant symmetric tensors into the actual centre. -/
theorem symmetrizationPower_diagonal_ad (n : ℕ) (x : L)
    (s : SymmetricPower K (Fin n) L) :
    symmetrizationPower n (SymmetricPower.diagonal (LieAlgebra.ad K L x) s) =
      ⁅ι K x, symmetrizationPower n s⁆ := by
  have hm : (symmetrizationPower (K := K) (L := L) n).comp
      (SymmetricPower.diagonal (LieAlgebra.ad K L x)) =
      (LieAlgebra.ad K (UniversalEnvelopingAlgebra K L) (ι K x)).comp
        (symmetrizationPower n) := by
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top K (Fin n) L)
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.comp_apply, SymmetricPower.diagonal_tprod, map_sum,
      symmetrizationPower, SymmetricPower.liftSymmetric_tprod, LieAlgebra.ad_apply]
    exact (lie_symmetrizationMultilinear x n v).symm
  exact LinearMap.congr_fun hm s

/-- Every adjoint-invariant symmetric tensor has a canonical image in the actual
centre. No surjectivity or orbit separation is assumed. -/
theorem symmetrizationPower_mem_center (n : ℕ) (s : SymmetricPower K (Fin n) L)
    (hs : ∀ x : L, SymmetricPower.diagonal (LieAlgebra.ad K L x) s = 0) :
    symmetrizationPower n s ∈ Subalgebra.center K (UniversalEnvelopingAlgebra K L) := by
  rw [Subalgebra.mem_center_iff]
  intro u
  induction u using UniversalEnvelopingAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r _
  | ι x =>
    have h := symmetrizationPower_diagonal_ad n x s
    rw [hs x, map_zero, LieRing.of_associative_ring_bracket] at h
    exact sub_eq_zero.mp h.symm
  | mul a b ha hb => calc
      a * b * symmetrizationPower n s = a * (b * symmetrizationPower n s) := mul_assoc _ _ _
      _ = symmetrizationPower n s * (a * b) := by rw [hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => simp only [add_mul, mul_add, ha, hb]

/-- The space of symmetric tensors killed by every infinitesimal adjoint operator. -/
def invariantSymmetricPower (n : ℕ) : Submodule K (SymmetricPower K (Fin n) L) :=
  ⨅ x : L, LinearMap.ker (SymmetricPower.diagonal (LieAlgebra.ad K L x))

/-- Canonical central elements from adjoint-invariant symmetric tensors, degree by degree.
This is a linear map, not an algebra homomorphism; ordinary symmetrization does not
preserve multiplication of invariants. Characteristic zero is retained at this public
lifting interface, where the normalization is nondegenerate in every degree. -/
def symmetrizationPowerToCenter [CharZero K] (n : ℕ) :
    invariantSymmetricPower (K := K) (L := L) n →ₗ[K]
      Subalgebra.center K (UniversalEnvelopingAlgebra K L) :=
  ((symmetrizationPower (K := K) (L := L) n).comp
    (invariantSymmetricPower n).subtype).codRestrict
      (Subalgebra.center K (UniversalEnvelopingAlgebra K L)).toSubmodule (fun s =>
      symmetrizationPower_mem_center n s.val (fun x =>
        LinearMap.mem_ker.mp (((Submodule.mem_iInf _).mp s.property) x)))

@[simp] theorem coe_symmetrizationPowerToCenter [CharZero K] (n : ℕ)
    (s : invariantSymmetricPower (K := K) (L := L) n) :
    (symmetrizationPowerToCenter n s : UniversalEnvelopingAlgebra K L) =
      symmetrizationPower n s.val := rfl

end UniversalEnvelopingAlgebra

namespace Matrix.Realization.KacMoodyAlgebra

open Module UniversalEnvelopingAlgebra

variable {I K : Type} {H : Type*} [Fintype I] [DecidableEq I]
  [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (P : Matrix.Realization A K H)

/-- The actual HC image of the constructed central lift. In finite type these are
candidates for the degree induction in the proof of HC surjectivity. Establishing
that they supply every leading Weyl invariant still needs Chevalley restriction,
symmetric-power/homogeneous-polynomial identification, and graded HC compatibility.
The construction itself is valid without finite type, so no such hypothesis is faked. -/
def harishChandraSymmetricPower (n : ℕ) :
    invariantSymmetricPower (K := K) (L := KacMoodyAlgebra P) n →ₗ[K]
      SymmetricAlgebra K H :=
  (harishChandra P).toLinearMap.comp (symmetrizationPowerToCenter n)

/-- Evaluation of this image is the Verma character of the same genuine central lift,
not a separate invariant polynomial or a postulated central element. -/
theorem eval_harishChandraSymmetricPower (n : ℕ) (Λ : Dual K H)
    (s : invariantSymmetricPower (K := K) (L := KacMoodyAlgebra P) n) :
    SymmetricAlgebra.lift Λ (harishChandraSymmetricPower P n s) =
      VermaModule.centralCharacter P Λ (symmetrizationPowerToCenter n s) := by
  exact eval_harishChandraProjection_center P Λ (symmetrizationPowerToCenter n s)

end Matrix.Realization.KacMoodyAlgebra
