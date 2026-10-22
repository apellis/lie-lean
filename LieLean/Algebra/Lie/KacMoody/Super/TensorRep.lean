/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.Enveloping
import LieLean.Algebra.Lie.KacMoody.TensorRep

/-!
# The tensor-algebra representation of `U(G̃(A, τ))`

Let `λ ∈ 𝔥*`. As in the even case ([Kac] §1.2, proof of Thm. 1.2; `AuxLieAlgebra.tensorRep`),
the enveloping algebra of the auxiliary contragredient Lie superalgebra `G̃(A, τ)` ([Kac78] §1.1)
acts on the tensor algebra `T(V) = K⟨vᵢ : i ∈ ι⟩`: `fᵢ` acts by left multiplication by `vᵢ`, a word
`v_{j₁} ⋯ v_{jₖ}` is an `𝔥`-eigenvector of weight `λ - α_{j₁} - ⋯ - α_{jₖ}`, and `eᵢ` is defined by
`eᵢ 1 = 0` and `eᵢ (vⱼ a) = (-1)^{p i p j} vⱼ (eᵢ a) + δᵢⱼ ⟨λ - wt a, αᵢ^∨⟩ a`.

This is the Verma module of highest weight `λ`; it shows that the `fᵢ` generate a free
subalgebra of `U(G̃(A, τ))` and that `𝔥 → U(G̃(A, τ))` is injective.

## Main definitions

* `Matrix.Realization.SuperEnveloping.tensorRep`: the representation on `T(V)`.
* `Matrix.Realization.SuperEnveloping.fAlg`: the algebra morphism `T(V) → U(G̃(A, τ))`,
  `vᵢ ↦ fᵢ`.

## Main results

* `Matrix.Realization.SuperEnveloping.tensorRep_fAlg_one`: `fAlg x` acts on `1` as `x`.
* `Matrix.Realization.SuperEnveloping.fAlg_injective`: the `fᵢ` generate a free subalgebra.
* `Matrix.Realization.SuperEnveloping.h_injective`: `𝔥 → U(G̃(A, τ))` is injective.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.1.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.2.
-/

open FreeAlgebra (word onWords onWords_word endo_ext word_nil word_cons)
open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2)

namespace SuperEnveloping

open AuxLieAlgebra (wordWt wordWt_nil wordWt_cons repH repH_word repF repF_word repH_mulLeft)

local notation "T" => FreeAlgebra K ι

variable (Λ : Dual K H)

/-- The action of `eᵢ` on words. -/
def eWord (i : ι) : List ι → T
  | [] => 0
  | j :: w => superSign K p i j • (FreeAlgebra.ι K j * eWord i w) +
      if i = j then (Λ (P.coroot i) - wordWt P w (P.coroot i)) • word w else 0

/-- The action of `eᵢ` on `T(V)`. -/
def repE (i : ι) : Module.End K T := onWords (eWord P p Λ i)

@[simp] lemma repE_word (i : ι) (w : List ι) : repE P p Λ i (word w) = eWord P p Λ i w := by
  simp [repE]

lemma repH_eWord (a : H) (i : ι) (w : List ι) :
    repH P Λ a (eWord P p Λ i w) =
      (Λ a - wordWt P w a + P.root i a) • eWord P p Λ i w := by
  induction w with
  | nil => simp [eWord]
  | cons j w ih =>
    simp only [eWord, map_add, map_smul, repH_mulLeft, ih, wordWt_cons, LinearMap.add_apply]
    split_ifs with hij
    · subst hij
      simp only [map_smul, repH_word, smul_add, mul_smul_comm, smul_smul, smul_sub]
      module
    · simp only [add_zero, map_zero, mul_smul_comm, smul_sub, smul_smul]
      module

/-- The data of the representation of `U(G̃(A, τ))` on `T(V)`. -/
def tensorRepData : LiftData P p (Module.End K T) where
  h := repH P Λ
  e := repE P p Λ
  f := repF
  h_mul_h a b := endo_ext fun w ↦ by
    simp [smul_smul, mul_comm]
  e_mul_f i j := endo_ext fun w ↦ by
    simp only [Module.End.mul_apply, repF_word, repE_word, eWord, LinearMap.add_apply,
      LinearMap.smul_apply]
    simp only [repF, LinearMap.mulLeft_apply]
    split_ifs with hij
    · subst hij; simp
    · simp
  h_mul_e a i := endo_ext fun w ↦ by
    simp only [Module.End.mul_apply, repE_word, repH_word, map_smul, repH_eWord,
      LinearMap.add_apply, LinearMap.smul_apply]
    rw [← add_smul]
  h_mul_f a i := endo_ext fun w ↦ by
    simp only [Module.End.mul_apply, repF_word, repH_word, map_smul, wordWt_cons,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply]
    module

/-- The representation of `U(G̃(A, τ))` on the tensor algebra `T(V)` attached to `λ ∈ 𝔥*`. -/
def tensorRep : P.SuperEnveloping p →ₐ[K] Module.End K T :=
  lift (tensorRepData P p Λ)

@[simp] lemma tensorRep_e (i : ι) : tensorRep P p Λ (e P p i) = repE P p Λ i := lift_e _ i
@[simp] lemma tensorRep_f (i : ι) : tensorRep P p Λ (f P p i) = repF i := lift_f _ i
@[simp] lemma tensorRep_h (a : H) : tensorRep P p Λ (h P p a) = repH P Λ a := lift_h _ a

lemma tensorRep_e_one (i : ι) : tensorRep P p Λ (e P p i) 1 = 0 := by
  rw [tensorRep_e, ← word_nil, repE_word]; rfl

lemma tensorRep_h_one (a : H) : tensorRep P p Λ (h P p a) 1 = Λ a • 1 := by
  rw [tensorRep_h, ← word_nil, repH_word]
  simp

/-- The algebra morphism `T(V) → U(G̃(A, τ))` sending `vᵢ` to `fᵢ`. -/
def fAlg : FreeAlgebra K ι →ₐ[K] P.SuperEnveloping p := FreeAlgebra.lift K (f P p)

@[simp] lemma fAlg_ι (i : ι) : fAlg P p (FreeAlgebra.ι K i) = f P p i := by simp [fAlg]

/-- The algebra morphism `T(V) → U(G̃(A, τ))` sending `vᵢ` to `eᵢ`. -/
def eAlg : FreeAlgebra K ι →ₐ[K] P.SuperEnveloping p := FreeAlgebra.lift K (e P p)

@[simp] lemma eAlg_ι (i : ι) : eAlg P p (FreeAlgebra.ι K i) = e P p i := by simp [eAlg]

/-- The element `fAlg x` acts on `1 ∈ T(V)` as `x`. -/
lemma tensorRep_fAlg_one (x : FreeAlgebra K ι) : tensorRep P p Λ (fAlg P p x) 1 = x := by
  have : (tensorRep P p Λ).comp (fAlg P p) = Algebra.lmul K T := by
    ext i
    simp [repF]
  have := congrArg (fun φ ↦ φ x 1) this
  simpa using this

/-- The subalgebra of `U(G̃(A, τ))` generated by the `fᵢ` is free on them (the enveloping algebra
of `𝔫̃₋`; cf. [Kac] Thm. 1.2 (b)). -/
theorem fAlg_injective : Function.Injective (fAlg P p) := by
  intro x y hxy
  rw [← tensorRep_fAlg_one P p 0 x, ← tensorRep_fAlg_one P p 0 y, hxy]

/-- The map `𝔥 → U(G̃(A, τ))` is injective (cf. [Kac] Thm. 1.2 (a)). -/
theorem h_injective : Function.Injective (h P p) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  refine (forall_dual_apply_eq_zero_iff K a).mp fun Λ ↦ ?_
  have := tensorRep_h_one P p Λ a
  rw [ha, map_zero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
  simpa using this

end SuperEnveloping

end Matrix.Realization
