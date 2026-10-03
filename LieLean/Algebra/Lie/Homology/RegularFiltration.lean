/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.BGG.VermaHomology
import LieLean.Algebra.Lie.UniversalEnveloping.Filtration

/-!
# Total-degree filtration of the actual left-regular CE chains

## Main definitions / results

* `rectangle`: homogeneous exterior degree with bounded PBW coefficient degree.
* `total`: the strictly-below-total-degree filtration on the actual CE chain modules.
* `total_zero`, `total_mono`, `exists_mem_total`, `iSup_total`: zero bottom, monotonicity,
  and exhaustivity.
* `diff_mem_rectangle`, `d_mem_total`: preservation by the existing CE differentials.

## References

The argument is reconstructed directly from the existing CE recursion and PBW filtration.
All statements allow arbitrary commutative base rings and arbitrary Lie algebras, with no
finite-dimensionality hypothesis.
-/

noncomputable section
open TensorProduct ExteriorAlgebra
open UniversalEnvelopingAlgebra (LeftRegular)
namespace LieModule.ChevalleyEilenberg.RegularFiltration

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
local notation "U" => LeftRegular R L
local notation "E" => ExteriorAlgebra R L ⊗[R] U

/-- The rectangle of exterior degree `k` and enveloping degree at most `n`. -/
def rectangle (k n : ℕ) : Submodule R E :=
  Submodule.span R {c | ∃ (ω : ExteriorAlgebra R L), ω ∈ ⋀[R]^k L ∧
    ∃ u : U, LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n ∧
      ω ⊗ₜ[R] u = c}

variable {R L}

lemma tmul_mem_rectangle {k n : ℕ} {ω : ExteriorAlgebra R L} (hω : ω ∈ ⋀[R]^k L)
    {u : U} (hu : LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n) :
    ω ⊗ₜ[R] u ∈ rectangle R L k n :=
  Submodule.subset_span ⟨ω, hω, u, hu, rfl⟩

lemma rectangle_le {k n : ℕ} {S : Submodule R E}
    (h : ∀ (ω : ExteriorAlgebra R L), ω ∈ ⋀[R]^k L → ∀ u : U,
      LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n →
      ω ⊗ₜ[R] u ∈ S) : rectangle R L k n ≤ S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨ω, hω, u, hu, rfl⟩
  exact h ω hω u hu

lemma rectangle_mono (k : ℕ) {n m : ℕ} (h : n ≤ m) :
    rectangle R L k n ≤ rectangle R L k m :=
  rectangle_le fun _ hω _ hu ↦
    tmul_mem_rectangle hω (UniversalEnvelopingAlgebra.filtration_mono h hu)

lemma wedge_mem_rectangle (x : L) {k n : ℕ} {c : E}
    (hc : c ∈ rectangle R L k n) : wedge R L U x c ∈ rectangle R L (k + 1) n := by
  refine rectangle_le (S := (rectangle R L (k + 1) n).comap (wedge R L U x))
    (fun ω hω u hu ↦ ?_) hc
  rw [Submodule.mem_comap, wedge_tmul]
  apply tmul_mem_rectangle _ hu
  rw [exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ x) hω

lemma lie_mem_coefficient {n : ℕ} (x : L) {u : U}
    (hu : LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n) :
    LeftRegular.equiv R L ⁅x, u⁆ ∈ UniversalEnvelopingAlgebra.filtration R L (n + 1) := by
  rw [LeftRegular.equiv_lie]
  simpa [Nat.add_comm] using UniversalEnvelopingAlgebra.mul_mem_filtration
    (UniversalEnvelopingAlgebra.ι_mem_filtration_one x) hu

lemma lieAction_tmul_mem_rectangle (x : L) {k n : ℕ} {ω : ExteriorAlgebra R L}
    (hω : ω ∈ ⋀[R]^k L) {u : U}
    (hu : LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n) :
    lieAction R L U x (ω ⊗ₜ[R] u) ∈ rectangle R L k (n + 1) := by
  induction k generalizing ω with
  | zero =>
    rw [exteriorPower, pow_zero, Submodule.mem_one] at hω
    obtain ⟨r, rfl⟩ := hω
    rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul', map_smul, lieAction_one_tmul]
    apply Submodule.smul_mem
    exact tmul_mem_rectangle
      (by rw [exteriorPower, pow_zero]; exact Submodule.one_le.mp le_rfl)
      (lie_mem_coefficient x hu)
  | succ k ih =>
    rw [exteriorPower, pow_succ'] at hω
    induction hω using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      obtain ⟨y, rfl⟩ := ha
      rw [← wedge_tmul, lieAction_wedge]
      exact add_mem
        (wedge_mem_rectangle _ (rectangle_mono k (Nat.le_succ n) (tmul_mem_rectangle hb hu)))
        (wedge_mem_rectangle _ (ih hb))
    | add a _ b _ ha hb => rw [add_tmul, map_add]; exact add_mem ha hb

/-- The diagonal Lie action raises coefficient degree by at most one. -/
theorem lieAction_mem_rectangle (x : L) {k n : ℕ} {c : E}
    (hc : c ∈ rectangle R L k n) : lieAction R L U x c ∈ rectangle R L k (n + 1) :=
  rectangle_le (S := (rectangle R L k (n + 1)).comap (lieAction R L U x))
    (fun _ hω _ hu ↦ lieAction_tmul_mem_rectangle x hω hu) hc

lemma diff_tmul_mem_rectangle {k n : ℕ} {ω : ExteriorAlgebra R L}
    (hω : ω ∈ ⋀[R]^(k + 1) L) {u : U}
    (hu : LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n) :
    diff R L U (ω ⊗ₜ[R] u) ∈ rectangle R L k (n + 1) := by
  induction k generalizing ω with
  | zero =>
    rw [exteriorPower, pow_succ'] at hω
    induction hω using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      obtain ⟨x, rfl⟩ := ha
      rw [← wedge_tmul, diff_wedge,
        diff_eq_zero_of_mem_chainsIn_zero (tmul_mem_chainsIn hb u), map_zero, sub_zero]
      exact neg_mem (lieAction_tmul_mem_rectangle x hb hu)
    | add a _ b _ ha hb => rw [add_tmul, map_add]; exact add_mem ha hb
  | succ k ih =>
    rw [exteriorPower, pow_succ'] at hω
    induction hω using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      obtain ⟨x, rfl⟩ := ha
      rw [← wedge_tmul, diff_wedge]
      exact sub_mem (neg_mem (lieAction_tmul_mem_rectangle x hb hu))
        (wedge_mem_rectangle _ (ih hb))
    | add a _ b _ ha hb => rw [add_tmul, map_add]; exact add_mem ha hb

/-- The actual CE differential lowers exterior degree and raises PBW degree by at most one. -/
theorem diff_mem_rectangle {k n : ℕ} {c : E} (hc : c ∈ rectangle R L (k + 1) n) :
    diff R L U c ∈ rectangle R L k (n + 1) :=
  rectangle_le (S := (rectangle R L k (n + 1)).comap (diff R L U))
    (fun _ hω _ hu ↦ diff_tmul_mem_rectangle hω hu) hc

variable (R L)
/-- The strictly-below-total-degree filtration on actual `⋀ᵏL ⊗ LeftRegular` chains.
For `k < p` the coefficient degree is at most `p-k-1`; otherwise the stage is zero. -/
def total (k p : ℕ) : Submodule R (⋀[R]^k L ⊗[R] U) :=
  if k < p then (rectangle R L k (p - k - 1)).comap (incl R L U k) else ⊥

variable {R L}
/-- The bottom stage is zero, including in chain degree zero. -/
theorem total_zero (k : ℕ) : total R L k 0 = ⊥ := by simp [total]

/-- A pure chain of exterior degree `k` and PBW degree at most `n` lies below `p`
whenever `k+n < p`. -/
theorem tmul_mem_total {k n p : ℕ} (ω : ⋀[R]^k L) {u : U}
    (hu : LeftRegular.equiv R L u ∈ UniversalEnvelopingAlgebra.filtration R L n)
    (h : k + n < p) : ω ⊗ₜ[R] u ∈ total R L k p := by
  have hkp : k < p := by omega
  simp only [total, ite_eq_left hkp, Submodule.mem_comap, incl_tmul]
  exact tmul_mem_rectangle ω.2 (UniversalEnvelopingAlgebra.filtration_mono (by omega) hu)

/-- The total-degree stages form an increasing filtration. -/
theorem total_mono (k : ℕ) : Monotone (total R L k) := by
  intro p q hpq
  by_cases hp : k < p
  · have hq : k < q := lt_of_lt_of_le hp hpq
    simp only [total, ite_eq_left hp, ite_eq_left hq]
    exact Submodule.comap_mono (rectangle_mono k (by omega))
  · simp [total, hp]

/-- Every actual CE chain has finite total filtration degree. -/
theorem exists_mem_total (k : ℕ) (c : ⋀[R]^k L ⊗[R] U) :
    ∃ p, c ∈ total R L k p := by
  induction c with
  | tmul ω u =>
    obtain ⟨n, hn⟩ := UniversalEnvelopingAlgebra.exists_mem_filtration
      (LeftRegular.equiv R L u)
    refine ⟨k + n + 1, ?_⟩
    simp only [total, show k < k + n + 1 by omega, ↓reduceIte, Submodule.mem_comap, incl_tmul]
    exact tmul_mem_rectangle ω.2 (by rwa [show k + n + 1 - k - 1 = n by omega])
  | add c c' hc hc' =>
    obtain ⟨p, hp⟩ := hc
    obtain ⟨q, hq⟩ := hc'
    exact ⟨max p q, add_mem (total_mono k (le_max_left p q) hp)
      (total_mono k (le_max_right p q) hq)⟩

/-- The increasing total-degree filtration exhausts the actual chain module. -/
theorem iSup_total (k : ℕ) : ⨆ p, total R L k p = ⊤ := by
  refine eq_top_iff.mpr fun c _ ↦ ?_
  obtain ⟨p, hp⟩ := exists_mem_total k c
  exact Submodule.mem_iSup_of_mem p hp

/-- The existing, actual CE chain differential preserves total filtration degree. -/
theorem d_mem_total {k p : ℕ} {c : ⋀[R]^(k + 1) L ⊗[R] U}
    (hc : c ∈ total R L (k + 1) p) : d R L U k c ∈ total R L k p := by
  by_cases hp : k + 1 < p
  · have hkp : k < p := by omega
    simp only [total, ite_eq_left hp, Submodule.mem_comap] at hc
    simp only [total, ite_eq_left hkp, Submodule.mem_comap, incl_d]
    exact rectangle_mono k (by omega) (diff_mem_rectangle hc)
  · simp only [total, ite_eq_right hp, Submodule.mem_bot] at hc
    subst c
    exact Submodule.zero_mem _

end LieModule.ChevalleyEilenberg.RegularFiltration
