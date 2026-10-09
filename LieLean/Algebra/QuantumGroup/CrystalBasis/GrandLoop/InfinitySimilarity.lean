/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.InfinityKS
import LieLean.RepresentationTheory.Crystal.Similarity

/-!
# Similarity of `B(∞)`

For every positive integer `m` there is a unique injective map `S_m : B(∞) → B(∞)` with
`wt(S_m b) = m wt(b)`, `εᵢ(S_m b) = m εᵢ(b)`, `S_m(ẽᵢ b) = ẽᵢᵐ S_m(b)` and
`S_m(f̃ᵢ b) = f̃ᵢᵐ S_m(b)` ([Kas96] Thm. 3.2):
`S_m(f̃_{i₁} ⋯ f̃_{iₗ} u_∞) = f̃_{i₁}ᵐ ⋯ f̃_{iₗ}ᵐ u_∞`.

## Main definitions

* `GrandLoop.similarityInf`: `S_m` (`GrandLoop.similarityInf_injective`,
  `GrandLoop.similarityInf_one`, `GrandLoop.similarityInf_mkB`).

## Proof

[Kas96] uses the embedding of `B(∞)` into an infinite tensor product of the crystals `Bᵢ`
([Kas93a]). We use instead the strict embeddings `Ψᵢ` and the Kashiwara–Saito data of `B(∞)`
(`GrandLoop.ksDataInf`), through the scaled comparison `Crystal.KSData.similarity`. The setting is
that of `GrandLoop.ksDataInf` (in particular `A/ϖA` is formally real).

## References

* [Kas96] M. Kashiwara, *Similarity of crystal bases*, Contemp. Math. 194 (1996), 177–186, §3.
* [Kas93a] M. Kashiwara, *The crystal base and Littelmann's refined Demazure character formula*,
  Duke Math. J. 71 (1993), 839–858.
-/

noncomputable section

namespace LieLean.QuantumGroup

namespace GrandLoop

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] [CharZero k]
  {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {A : Type*} [CommRing A] [Algebra A k] {ϖ : A}

variable [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
include hinj hϖ hϖv hk hfund

lemma crystalInf_ε_eq_zero_iff (i : I) (b : BInf (D := D) hvt A ϖ) :
    (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).ε i b = 0 ↔
      (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).e i b = none := by
  change ((epsInf hR hinj hϖ hϖv hk hfund i b : ℤ) : WithBot ℤ) = 0 ↔
    eInf hR hinj hϖ hϖv hk hfund i b = none
  rw [← epsInf_eq_zero_iff hinj hϖ hϖv hk hfund i b]
  constructor <;> intro h <;> exact_mod_cast h

lemma crystalInf_ε_eq_zero (i : I) (b : BInf (D := D) hvt A ϖ)
    (h : (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).e i b = none) :
    (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).ε i b = 0 :=
  (crystalInf_ε_eq_zero_iff hinj hϖ hϖv hk hfund i b).2 h

lemma crystalInf_e_eq_none (i : I) (b : BInf (D := D) hvt A ϖ)
    (h : (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).ε i b = 0) :
    (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).e i b = none :=
  (crystalInf_ε_eq_zero_iff hinj hϖ hϖv hk hfund i b).1 h

variable (hvt hR) in
/-- **Similarity of `B(∞)`** ([Kas96] Thm. 3.2): the `m`-similarity
`S_m : B(∞) → B(∞)`, `f̃_{i₁} ⋯ f̃_{iₗ} u_∞ ↦ f̃_{i₁}ᵐ ⋯ f̃_{iₗ}ᵐ u_∞`. -/
def similarityInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {m : ℕ} (hm : 0 < m) :
    Crystal.Similarity (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund)
      (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund) m :=
  (ksDataInf hvt hR hinj hϖ hϖv hk hfund).similarity hR (ksDataInf hvt hR hinj hϖ hϖv hk hfund) hm
    (crystalInf_ε_eq_zero hinj hϖ hϖv hk hfund) (crystalInf_e_eq_none hinj hϖ hϖv hk hfund)

theorem similarityInf_injective [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {m : ℕ} (hm : 0 < m) :
    Function.Injective (similarityInf hvt hR hinj hϖ hϖv hk hfund hm) :=
  (ksDataInf hvt hR hinj hϖ hϖv hk hfund).similarity_injective hR
    (ksDataInf hvt hR hinj hϖ hϖv hk hfund) hm (crystalInf_ε_eq_zero hinj hϖ hϖv hk hfund)
    (crystalInf_e_eq_none hinj hϖ hϖv hk hfund)

theorem similarityInf_one [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {m : ℕ} (hm : 0 < m) :
    similarityInf hvt hR hinj hϖ hϖv hk hfund hm (mkB hvt hR hinj hϖ hϖv hk hfund []) =
      mkB hvt hR hinj hϖ hϖv hk hfund [] :=
  (ksDataInf hvt hR hinj hϖ hϖv hk hfund).similarity_b₀ hR
    (ksDataInf hvt hR hinj hϖ hϖv hk hfund) hm (crystalInf_ε_eq_zero hinj hϖ hϖv hk hfund)
    (crystalInf_e_eq_none hinj hϖ hϖv hk hfund)

/-- `S_m(f̃_w u_∞) = f̃_{wᵐ} u_∞`. -/
theorem fWord_similarityInf [IsFormallyReal (A ⧸ Ideal.span {ϖ})] {m : ℕ} (hm : 0 < m)
    (w : List I) :
    (crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).fWord (Crystal.stretchWord m w)
        (mkB hvt hR hinj hϖ hϖv hk hfund []) =
      ((crystalInf (hvt := hvt) hR hinj hϖ hϖv hk hfund).fWord w
        (mkB hvt hR hinj hϖ hϖv hk hfund [])).map
        (similarityInf hvt hR hinj hϖ hϖv hk hfund hm) := by
  rw [← (similarityInf hvt hR hinj hϖ hϖv hk hfund hm).fWord_stretchWord,
    similarityInf_one]

end GrandLoop

end LieLean.QuantumGroup
