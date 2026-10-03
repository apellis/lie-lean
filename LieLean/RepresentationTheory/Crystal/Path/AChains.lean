/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.AChains.Roots
import LieLean.RepresentationTheory.Crystal.Path.LSFinitePieces

/-!
# Time chains and position chains modulo the root lattice

## Main definitions / results

* `rootLattice`: the range of the integer simple-root map.
* `AChain`: positive-real-root saturated descending chains with time integrality.
* `chain_iff_aChain`: local equivalence under the incoming root-lattice congruence.
* `finite_congruences`: establishes that invariant from either finite collection of chains.
* `isLS_rationalPieces_iff_aChains`: the supplied finite-path characterization for actual
  dominant-integral realization data. No congruence or LS premise is hidden in its shape.

## References

P. Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142 (1995),
499–525, Section 4, pp. 509–510.
The proof is reconstructed. Source steps use the positive-real-root, negative-pairing, saturated
dominant-orbit Bruhat presentation of Remark 4.2. No maximal-distance function or reparametrization
quotient is constructed.
-/

open Module Set LittelmannPath

namespace Matrix.Realization.LSAChainBridge

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup H] [Module ℝ H]
  {A : Matrix ι ι ℤ} (P : Realization A ℝ H) (hA : A.IsGeneralizedCartan)

/-- The actual integer root lattice in the ambient weight space. -/
noncomputable def rootLattice : AddSubgroup (Dual ℝ H) := P.rootOf.range

/-- Source time-integral chains, allowing the source's empty chain. -/
def AChain (Λ : Dual ℝ H) (a : ℝ) : P.integralWeights → P.integralWeights → Prop :=
  Relation.ReflTransGen fun x y ↦ ∃ c,
    LSAChainBridgeRoots.SourceStep P hA Λ x y c ∧
      ∃ z : ℤ, a * c (x : Dual ℝ H) = z

variable {P hA} {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ)
  {x y : P.integralWeights} {p : Dual ℝ H} {a : ℝ}

/-- Every step coroot is integer-valued on the actual root lattice. -/
theorem step_integral_rootLattice {c : Dual ℝ (Dual ℝ H)}
    (hc : (P.lsData hA hΛ).Step x y c) {q : Dual ℝ H}
    (hq : q ∈ rootLattice P) : ∃ z : ℤ, c q = z := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨m, n, hm, hn, hx, hy, hb, hl, u, j, he, rfl⟩ := hc
  obtain ⟨l, hl⟩ := P.exists_apply_rootOf_eq_rootOf hA (u⁻¹).2 k
  refine ⟨(A *ᵥ l) j, ?_⟩
  change (u⁻¹).1 (P.rootOf k) (P.coroot j) = _
  rw [hl, rootOf_apply_coroot]

/-- The necessary congruence, not an arbitrary equality of time and position integrality. -/
theorem step_integral_iff {c : Dual ℝ (Dual ℝ H)}
    (hc : (P.lsData hA hΛ).Step x y c)
    (hq : p - a • (x : Dual ℝ H) ∈ rootLattice P) :
    (∃ z : ℤ, c p = z) ↔ ∃ z : ℤ, a * c (x : Dual ℝ H) = z := by
  obtain ⟨k, hk⟩ := step_integral_rootLattice hΛ hc hq
  rw [map_sub, map_smul, smul_eq_mul] at hk
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z - k, by push_cast; linarith⟩
  · rintro ⟨z, hz⟩
    exact ⟨z + k, by push_cast; linarith⟩

/-- Each integral time step has root-lattice displacement, for arbitrary real roots. -/
theorem step_displacement {c : Dual ℝ (Dual ℝ H)}
    (hc : (P.lsData hA hΛ).Step x y c)
    (hint : ∃ z : ℤ, a * c (x : Dual ℝ H) = z) :
    a • (x : Dual ℝ H) - a • (y : Dual ℝ H) ∈ rootLattice P := by
  obtain ⟨d, hd, hd'⟩ := LSAChainBridgeRoots.step_exists_sourceStep hΛ hc
  have hint' : ∃ z : ℤ, a * d (x : Dual ℝ H) = z := by
    obtain ⟨z, hz⟩ := hint
    rcases hd' with rfl | rfl
    · exact ⟨z, hz⟩
    · exact ⟨-z, by simp [hz]⟩
  obtain ⟨z, hz⟩ := hint'
  obtain ⟨u, j, k, hk, hk0, huk, hdc, hy⟩ := hd.exists_positive_root
  refine ⟨z • k, ?_⟩
  rw [map_zsmul, hy, smul_sub, smul_smul, hz, Int.cast_smul_eq_zsmul]
  abel

/-- Along a position chain, the incoming congruence propagates and yields a source a-chain. -/
theorem chain_to_aChain (h : (P.lsData hA hΛ).Chain p x y)
    (hq : p - a • (x : Dual ℝ H) ∈ rootLattice P) :
    AChain P hA Λ a x y ∧ p - a • (y : Dual ℝ H) ∈ rootLattice P := by
  induction h with
  | refl => exact ⟨.refl, hq⟩
  | @tail y z h hyz ih =>
    obtain ⟨c, hc, hint⟩ := hyz
    have ht := (step_integral_iff hΛ hc ih.2).mp hint
    have hstep := (LSAChainBridgeRoots.exists_step_integral_iff_exists_sourceStep_integral
      hΛ a).mp ⟨c, hc, ht⟩
    refine ⟨ih.1.tail hstep, ?_⟩
    have hadd := (rootLattice P).add_mem ih.2 (step_displacement hΛ hc ht)
    convert hadd using 1; abel

/-- Along a source a-chain, root-lattice congruence propagates and supplies position integrality. -/
theorem aChain_to_chain (h : AChain P hA Λ a x y)
    (hq : p - a • (x : Dual ℝ H) ∈ rootLattice P) :
    (P.lsData hA hΛ).Chain p x y ∧ p - a • (y : Dual ℝ H) ∈ rootLattice P := by
  induction h with
  | refl => exact ⟨.refl, hq⟩
  | @tail y z h hyz ih =>
    obtain ⟨c, hc, hint⟩ := hyz
    have hs := hc.step hΛ
    have hp := (step_integral_iff hΛ hs ih.2).mpr hint
    refine ⟨ih.1.tail ⟨c, hs, hp⟩, ?_⟩
    have hadd := (rootLattice P).add_mem ih.2 (step_displacement hΛ hs hint)
    convert hadd using 1; abel

/-- The exact local bridge; the root-lattice congruence is indispensable. -/
theorem chain_iff_aChain (hq : p - a • (x : Dual ℝ H) ∈ rootLattice P) :
    (P.lsData hA hΛ).Chain p x y ↔ AChain P hA Λ a x y :=
  ⟨fun h ↦ (chain_to_aChain hΛ h hq).1, fun h ↦ (aChain_to_chain hΛ h hq).1⟩

section Finite

variable {π : LittelmannPath (P.pathSpace hA)} {n : ℕ} {a : Fin (n + 2) → ℚ}
  (ha : StrictMono a) (ha0 : a 0 = 0)
  {x : Fin (n + 1) → P.integralWeights}
  (hpiece : ∀ i t, t ∈ Icc (a i.castSucc : ℝ) (a i.succ : ℝ) →
    π t = finitePiecePosition (P.pathSpace hA) a x i.castSucc +
      (t - (a i.castSucc : ℝ)) • (x i : Dual ℝ H))

include ha hpiece

omit [DecidableEq ι] in
/-- The affine formula transports the root-lattice congruence across one segment. -/
theorem piece_difference (i : Fin (n + 1)) :
    π (a i.succ : ℝ) - (a i.succ : ℝ) • (x i : Dual ℝ H) =
      π (a i.castSucc : ℝ) - (a i.castSucc : ℝ) • (x i : Dual ℝ H) := by
  have hi : (a i.castSucc : ℝ) ≤ (a i.succ : ℝ) := by
    exact_mod_cast (ha Fin.castSucc_lt_succ).le
  rw [hpiece i _ ⟨hi, le_rfl⟩, hpiece i _ ⟨le_rfl, hi⟩, sub_self, zero_smul,
    add_zero]
  rw [sub_smul (a i.succ : ℝ) (a i.castSucc : ℝ) (x i : Dual ℝ H)]
  abel

include ha0

/-- Either collection of breakpoint conditions forces all incoming congruences.
The invariant is proved from the zero start; it is not a theorem hypothesis. -/
theorem finite_congruences
    (h : ∀ i : Fin n,
      (P.lsData hA hΛ).Chain (π (a i.succ.castSucc : ℝ)) (x i.castSucc) (x i.succ) ∨
        AChain P hA Λ (a i.succ.castSucc : ℝ) (x i.castSucc) (x i.succ)) :
    ∀ i : Fin (n + 1),
      π (a i.castSucc : ℝ) - (a i.castSucc : ℝ) • (x i : Dual ℝ H) ∈ rootLattice P := by
  intro i
  induction i using Fin.induction with
  | zero => simp [ha0]
  | succ i ih =>
    have hq : π (a i.succ.castSucc : ℝ) -
        (a i.succ.castSucc : ℝ) • (x i.castSucc : Dual ℝ H) ∈ rootLattice P := by
      rw [Fin.castSucc_succ, piece_difference ha hpiece i.castSucc]
      exact ih
    rcases h i with hp | ht
    · exact (chain_to_aChain hΛ hp hq).2
    · exact (aChain_to_chain hΛ ht hq).2

/-- All finite cumulative-position chains are equivalent to all source a-chains.
Both implications prove, rather than assume, the root-lattice invariant. -/
theorem finite_chains_iff :
    (∀ i : Fin n,
      (P.lsData hA hΛ).Chain (π (a i.succ.castSucc : ℝ)) (x i.castSucc) (x i.succ)) ↔
    ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ) (x i.castSucc) (x i.succ) := by
  constructor
  · intro h i
    have hi := finite_congruences hΛ ha ha0 hpiece (fun j ↦ Or.inl (h j)) i.castSucc
    have hq : π (a i.succ.castSucc : ℝ) -
        (a i.succ.castSucc : ℝ) • (x i.castSucc : Dual ℝ H) ∈ rootLattice P := by
      rw [Fin.castSucc_succ, piece_difference ha hpiece i.castSucc]
      exact hi
    exact (chain_to_aChain hΛ (h i) hq).1
  · intro h i
    have hi := finite_congruences hΛ ha ha0 hpiece (fun j ↦ Or.inr (h j)) i.castSucc
    have hq : π (a i.succ.castSucc : ℝ) -
        (a i.succ.castSucc : ℝ) • (x i.castSucc : Dual ℝ H) ∈ rootLattice P := by
      rw [Fin.castSucc_succ, piece_difference ha hpiece i.castSucc]
      exact hi
    exact (aChain_to_chain hΛ (h i) hq).1

/-- Concrete dominant-integral finite-piece source a-chain characterization.
The supplied path and literal shape are the only path hypotheses; `IsLS` is not assumed.
The source permits empty a-chains, so redundant equal directions need not be removed. -/
theorem isLS_rationalPieces_iff_aChains (ha1 : a (Fin.last (n + 1)) = 1)
    (hx : ∀ i, ∃ w : P.weylGroup hA, (x i : Dual ℝ H) = w.1 Λ) :
    IsLS (P.lsData hA hΛ) π ↔
      ∀ i : Fin n, AChain P hA Λ (a i.succ.castSucc : ℝ) (x i.castSucc) (x i.succ) := by
  have hpos (i : Fin n) : π (a i.succ.castSucc : ℝ) =
      finitePiecePosition (P.pathSpace hA) a x i.succ.castSucc := by
    rw [hpiece i.succ _ ⟨le_rfl, ?_⟩]
    · simp
    · exact_mod_cast (ha Fin.castSucc_lt_succ).le
  rw [isLS_rationalPieces_iff ha ha0 ha1 hx hpiece]
  simpa only [hpos] using finite_chains_iff hΛ ha ha0 hpiece

end Finite

end Matrix.Realization.LSAChainBridge
