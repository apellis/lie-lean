/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityPsiEmb
import LieLean.RepresentationTheory.Crystal.KashiwaraSaito

/-!
# The Kashiwara–Saito characterization of `B(∞)`

Assume `A/ϖA` is formally real. The crystal `B(∞)` with `u_∞` and the embeddings
`Ψᵢ : B(∞) → B(∞) ⊗ Bᵢ` satisfies the conditions (1)–(7) of [KS97] Prop. 3.2.3
(`GrandLoop.ksDataInf`). Hence any crystal `B` with an element `b₀` satisfying them is isomorphic
to `B(∞)`, by an isomorphism sending `b₀` to `u_∞` (`GrandLoop.equivInf`, `GrandLoop.equivInf_b₀`;
[KS97] Prop. 3.2.3). The simple roots are linearly independent since the root datum is
`X`-regular.

## References

* [KS97] M. Kashiwara, Y. Saito, *Geometric construction of crystal bases*, Duke Math. J. 89
  (1997); arXiv:q-alg/9606009v1, §3.2.
-/

open Finset Pointwise LusztigF

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

lemma eq_nil_of_wordWeight_eq_zero {I : Type*} {w : List I} (h : wordWeight w = 0) : w = [] := by
  cases w with
  | nil => rfl
  | cons j w =>
    exfalso
    have := congrArg (· j) h
    simp at this

lemma rootSum_crystalDatum {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I}
    (R : D.RootDatum Y) (ν : I →₀ ℕ) : R.crystalDatum.rootSum ν = R.rootSum ν := rfl

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

section Base

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

variable (hvt hR) in
/-- **`B(∞)` satisfies the conditions of [KS97] Prop. 3.2.3**, with `b₀ = u_∞` and the strict
embeddings `Ψᵢ` of [Kas93a] Thm. 2.2.1. -/
def ksDataInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] :
    Crystal.KSData (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund)
      (mkB hvt hR hinj hϖ hϖv hk hfund []) where
  Ψ i := psiInfHom hvt hR hinj hϖ hϖv hk hfund i
  Ψ_injective i := psiInf_injective hinj hϖ hϖv hk hfund i
  wt_mem b := by
    obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
    exact ⟨wordWeight w, by
      rw [rootSum_crystalDatum R]; exact wtInf_mkB (hR := hR) hinj hϖ hϖv hk hfund w⟩
  wt_b₀ := by
    change wtInf (R := R) _ = 0
    rw [wtInf_mkB, wordWeight_nil, R.rootSum_zero, neg_zero]
  eq_b₀ b h := by
    obtain ⟨w, rfl⟩ := exists_eq_mkB (hR := hR) hinj hϖ hϖv hk hfund b
    change wtInf (R := R) _ = 0 at h
    rw [wtInf_mkB, neg_eq_zero, ← rootSum_crystalDatum R, ← R.crystalDatum.rootSum_zero] at h
    rw [eq_nil_of_wordWeight_eq_zero
      (R.crystalDatum.rootSum_injective hR h)]
  ε_b₀ i := by
    change ((epsInf hR hinj hϖ hϖv hk hfund i _ : ℤ) : WithBot ℤ) = 0
    rw [(epsInf_eq_zero_iff hinj hϖ hϖv hk hfund i _).2
      (eInf_mkB_eq_none hinj hϖ hϖv hk hfund i []
        (by rw [kE_fWi_eq_zero i (by simp)]; exact zero_mem _))]
    rfl
  ε_ne_bot _ _ := WithBot.coe_ne_bot
  Ψ_snd_nonpos i b := psiInf_snd_nonpos hinj hϖ hϖv hk hfund i b
  exists_Ψ_snd_neg b hb := exists_psiInf_snd_neg hinj hϖ hϖv hk hfund b hb

variable (hvt hR) in
/-- **The Kashiwara–Saito characterization of `B(∞)`** ([KS97] Prop. 3.2.3): a crystal `B` with an
element `b₀` satisfying the conditions (1)–(7) (`Crystal.KSData`) is isomorphic to `B(∞)`. -/
def equivInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {B : Type*} {C : Crystal R.crystalDatum B}
    {b₀ : B} (K : Crystal.KSData C b₀) :
    Crystal.Equiv C (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund) :=
  K.equiv hR (ksDataInf hvt hR hinj hϖ hϖv hk hfund)

theorem equivInf_b₀ [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {B : Type*}
    {C : Crystal R.crystalDatum B} {b₀ : B} (K : Crystal.KSData C b₀) :
    equivInf hvt hR hinj hϖ hϖv hk hfund K b₀ = mkB hvt hR hinj hϖ hϖv hk hfund [] :=
  K.equiv_b₀ hR (ksDataInf hvt hR hinj hϖ hϖv hk hfund)

end Base

end GrandLoop

end LieLean.QuantumGroup
