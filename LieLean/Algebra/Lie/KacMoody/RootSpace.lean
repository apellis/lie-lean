/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TensorRep
import LieLean.Algebra.Lie.Weights.OfMap

/-!
# Root space decomposition of `𝔤̃(A)` and the maximal ideal `𝔯`

We prove parts (d), (e) of [Kac] Theorem 1.2: the root space decomposition of `𝔤̃(A)` and the
existence of the maximal ideal `𝔯`. (The Chevalley involution, part (c), is
`Matrix.Realization.AuxLieAlgebra.chevalleyInvolution`.)

## Main definitions

* `Matrix.Realization.AuxLieAlgebra.rootSpace`: the root space `𝔤̃_μ`.
* `Matrix.Realization.AuxLieAlgebra.maxIdeal`: the unique maximal ideal `𝔯` of `𝔤̃(A)` meeting
  `𝔥` trivially.

## Main results

* `Matrix.Realization.AuxLieAlgebra.rootSpace_zero`: `𝔤̃_0 = 𝔥`.
* `Matrix.Realization.AuxLieAlgebra.rootSpace_pos_le`, `rootSpace_neg_le`: for `0 < α ∈ Q₊`,
  `𝔤̃_α ⊆ 𝔫̃₊` and `𝔤̃_{-α} ⊆ 𝔫̃₋`.
* `Matrix.Realization.AuxLieAlgebra.fHom_mem`, `eHom_mem`: `𝔫̃₋ = ⊕_{α > 0} 𝔤̃_{-α}` and
  `𝔫̃₊ = ⊕_{α > 0} 𝔤̃_α`.
* `Matrix.Realization.AuxLieAlgebra.le_maxIdeal_iff`: `𝔯` is the unique maximal ideal meeting `𝔥`
  trivially ([Kac] Thm. 1.2 (e)).
* `Matrix.Realization.AuxLieAlgebra.maxIdeal_eq`: `𝔯 = (𝔯 ∩ 𝔫̃₋) ⊕ (𝔯 ∩ 𝔫̃₊)`.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Thm. 1.2.
-/

open FreeLieAlgebra Module LieModule

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The nonzero elements `Q₊ \ {0}` of the positive cone of the root lattice. -/
def posCone (ι : Type*) : Set (ι → ℤ) := {k | 0 ≤ k ∧ k ≠ 0}

omit [Fintype ι] in
lemma posCone_add {k l : ι → ℤ} (hk : k ∈ posCone ι) (hl : l ∈ posCone ι) :
    k + l ∈ posCone ι := by
  refine ⟨add_nonneg hk.1 hl.1, fun h ↦ hk.2 ?_⟩
  ext i
  have h1 := hk.1 i; have h2 := hl.1 i; have := congr_fun h i
  simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 this ⊢
  omega

omit [Fintype ι] in
lemma single_mem_posCone [DecidableEq ι] (i : ι) : Pi.single i 1 ∈ posCone ι := by
  refine ⟨fun j ↦ ?_, fun h ↦ by simpa using congr_fun h i⟩
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- The set of weights `α` with `α ∈ Q₊ \ {0}`. -/
def posWeights : Set (Dual K H) := P.rootOf '' posCone ι

/-- The set of weights `-α` with `α ∈ Q₊ \ {0}`. -/
def negWeights : Set (Dual K H) := (fun k ↦ -P.rootOf k) '' posCone ι

lemma posWeights_add {μ ν : Dual K H} (hμ : μ ∈ P.posWeights) (hν : ν ∈ P.posWeights) :
    μ + ν ∈ P.posWeights := by
  obtain ⟨k, hk, rfl⟩ := hμ; obtain ⟨l, hl, rfl⟩ := hν
  exact ⟨k + l, posCone_add hk hl, map_add _ _ _⟩

lemma negWeights_add {μ ν : Dual K H} (hμ : μ ∈ P.negWeights) (hν : ν ∈ P.negWeights) :
    μ + ν ∈ P.negWeights := by
  obtain ⟨k, hk, rfl⟩ := hμ; obtain ⟨l, hl, rfl⟩ := hν
  exact ⟨k + l, posCone_add hk hl, by simp only [map_add, neg_add]⟩

lemma root_mem_posWeights (i : ι) : P.root i ∈ P.posWeights := by
  classical exact ⟨Pi.single i 1, single_mem_posCone i, by simp⟩

lemma neg_root_mem_negWeights (i : ι) : -P.root i ∈ P.negWeights := by
  classical exact ⟨Pi.single i 1, single_mem_posCone i, by simp⟩

variable [CharZero K]

lemma zero_notMem_posWeights : (0 : Dual K H) ∉ P.posWeights := by
  rintro ⟨k, hk, h0⟩
  exact P.rootOf_ne_zero hk.2 h0

lemma zero_notMem_negWeights : (0 : Dual K H) ∉ P.negWeights := by
  rintro ⟨k, hk, h0⟩
  exact P.rootOf_ne_zero hk.2 (neg_eq_zero.mp h0)

lemma disjoint_posWeights_negWeights : Disjoint P.posWeights P.negWeights := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, hk, rfl⟩ ⟨l, hl, hlk⟩
  have : P.rootOf (k + l) = 0 := by rw [map_add, ← hlk]; simp
  exact P.rootOf_ne_zero (posCone_add hk hl).2 this

variable [DecidableEq ι]

namespace AuxLieAlgebra

/-- The root space `𝔤̃_μ = {x | ∀ h, [h, x] = ⟨μ, h⟩ x}`. -/
abbrev rootSpace (μ : Dual K H) : Submodule K P.AuxLieAlgebra :=
  weightSpaceOfMap P.AuxLieAlgebra (h P) μ

omit [CharZero K] in
lemma e_mem_rootSpace (i : ι) : e P i ∈ rootSpace P (P.root i) := fun a ↦ lie_h_e P a i

omit [CharZero K] in
lemma f_mem_rootSpace (i : ι) : f P i ∈ rootSpace P (-P.root i) := fun a ↦ by
  simp [lie_h_f]

omit [CharZero K] in
lemma h_mem_rootSpace (a : H) : h P a ∈ rootSpace P 0 := fun b ↦ by simp [lie_h_h]

omit [CharZero K] in
lemma lie_mem_rootSpace {μ ν : Dual K H} {x y : P.AuxLieAlgebra} (hx : x ∈ rootSpace P μ)
    (hy : y ∈ rootSpace P ν) : ⁅x, y⁆ ∈ rootSpace P (μ + ν) :=
  lie_mem_weightSpaceOfMap (h P) hx hy

omit [CharZero K] in
/-- The sum of root spaces over a set of weights closed under addition is a subalgebra. -/
lemma lie_mem_biSup {S : Set (Dual K H)} (hS : ∀ μ ∈ S, ∀ ν ∈ S, μ + ν ∈ S)
    {x y : P.AuxLieAlgebra} (hx : x ∈ ⨆ μ ∈ S, rootSpace P μ) (hy : y ∈ ⨆ μ ∈ S, rootSpace P μ) :
    ⁅x, y⁆ ∈ ⨆ μ ∈ S, rootSpace P μ := by
  rw [← iSup_subtype''] at hx hy ⊢
  refine Submodule.iSup_induction _ (motive := fun x ↦ ⁅x, y⁆ ∈ _) hx (fun μ x hx ↦ ?_)
    (by simp) (fun x₁ x₂ h₁ h₂ ↦ by rw [add_lie]; exact Submodule.add_mem _ h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun y ↦ ⁅x, y⁆ ∈ _) hy (fun ν y hy ↦ ?_)
    (by simp) (fun y₁ y₂ h₁ h₂ ↦ by rw [lie_add]; exact Submodule.add_mem _ h₁ h₂)
  exact Submodule.mem_iSup_of_mem ⟨_, hS _ μ.2 _ ν.2⟩ (lie_mem_rootSpace P hx hy)

omit [CharZero K] in
/-- `𝔫̃₋ ⊆ ⊕_{α > 0} 𝔤̃_{-α}`. -/
lemma fHom_mem (y : FreeLieAlgebra K ι) : fHom P y ∈ ⨆ μ ∈ P.negWeights, rootSpace P μ := by
  induction y using FreeLieAlgebra.induction_on with
  | of i =>
    rw [fHom_of]
    exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (P.neg_root_mem_negWeights i)
      (f_mem_rootSpace P i))
  | zero => simp
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  | lie y z hy hz =>
    rw [LieHom.map_lie]; exact lie_mem_biSup P (fun _ h₁ _ h₂ ↦ P.negWeights_add h₁ h₂) hy hz

omit [CharZero K] in
/-- `𝔫̃₊ ⊆ ⊕_{α > 0} 𝔤̃_α`. -/
lemma eHom_mem (z : FreeLieAlgebra K ι) : eHom P z ∈ ⨆ μ ∈ P.posWeights, rootSpace P μ := by
  induction z using FreeLieAlgebra.induction_on with
  | of i =>
    rw [eHom_of]
    exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (P.root_mem_posWeights i)
      (e_mem_rootSpace P i))
  | zero => simp
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  | lie y z hy hz =>
    rw [LieHom.map_lie]; exact lie_mem_biSup P (fun _ h₁ _ h₂ ↦ P.posWeights_add h₁ h₂) hy hz

omit [CharZero K] in
lemma h_mem_biSup (a : H) : h P a ∈ ⨆ μ ∈ ({0} : Set (Dual K H)), rootSpace P μ :=
  Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem rfl (h_mem_rootSpace P a))

/-- The set of all weights of `𝔤̃(A)`: `-(Q₊ \ 0) ∪ {0} ∪ (Q₊ \ 0)`. -/
def allWeights : Set (Dual K H) := P.negWeights ∪ {0} ∪ P.posWeights

omit [CharZero K] in
/-- `𝔤̃(A)` is the sum of its root spaces. -/
lemma iSup_rootSpace_eq_top : ⨆ μ ∈ allWeights P, rootSpace P μ = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨y, a, z⟩, rfl⟩ := (triangularEquiv P).surjective x
  rw [triangularEquiv_apply]
  have h1 : ⨆ μ ∈ P.negWeights, rootSpace P μ ≤ ⨆ μ ∈ allWeights P, rootSpace P μ :=
    biSup_mono fun μ hμ ↦ Or.inl (Or.inl hμ)
  have h2 : ⨆ μ ∈ ({0} : Set (Dual K H)), rootSpace P μ ≤ ⨆ μ ∈ allWeights P, rootSpace P μ :=
    biSup_mono fun μ hμ ↦ Or.inl (Or.inr hμ)
  have h3 : ⨆ μ ∈ P.posWeights, rootSpace P μ ≤ ⨆ μ ∈ allWeights P, rootSpace P μ :=
    biSup_mono fun μ hμ ↦ Or.inr hμ
  exact Submodule.add_mem _ (Submodule.add_mem _ (h1 (fHom_mem P y)) (h2 (h_mem_biSup P a)))
    (h3 (eHom_mem P z))

omit [CharZero K] in
lemma disjoint_biSup {S T : Set (Dual K H)} (hST : Disjoint S T) :
    Disjoint (⨆ μ ∈ S, rootSpace P μ) (⨆ μ ∈ T, rootSpace P μ) :=
  (iSupIndep_weightSpaceOfMap (h P)).disjoint_biSup_biSup hST

omit [CharZero K] in
lemma mem_biSup_of_subset {S T : Set (Dual K H)} (hST : ∀ μ ∈ S, μ ∈ T) {x : P.AuxLieAlgebra}
    (hx : x ∈ ⨆ μ ∈ S, rootSpace P μ) : x ∈ ⨆ μ ∈ T, rootSpace P μ :=
  (biSup_mono hST : (⨆ μ ∈ S, rootSpace P μ) ≤ ⨆ μ ∈ T, rootSpace P μ) hx

omit [CharZero K] in
lemma rootSpace_le_biSup {μ : Dual K H} {S : Set (Dual K H)} (hμ : μ ∈ S) :
    rootSpace P μ ≤ ⨆ ν ∈ S, rootSpace P ν :=
  le_biSup (fun ν ↦ rootSpace P ν) hμ

/-- `𝔤̃_0 = 𝔥` ([Kac] Thm. 1.2 (d)). -/
theorem rootSpace_zero : rootSpace P 0 = LinearMap.range (h P) := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨⟨y, a, z⟩, rfl⟩ := (triangularEquiv P).surjective x
    rw [triangularEquiv_apply] at hx ⊢
    have hS : Disjoint ({0} : Set (Dual K H)) (P.negWeights ∪ P.posWeights) :=
      Set.disjoint_singleton_left.mpr fun h ↦
        h.elim P.zero_notMem_negWeights P.zero_notMem_posWeights
    have hmem : fHom P y + eHom P z ∈ ⨆ μ ∈ P.negWeights ∪ P.posWeights, rootSpace P μ :=
      Submodule.add_mem _ (mem_biSup_of_subset P (fun μ hμ ↦ Or.inl hμ) (fHom_mem P y))
        (mem_biSup_of_subset P (fun μ hμ ↦ Or.inr hμ) (eHom_mem P z))
    have hmem0 : fHom P y + eHom P z ∈ ⨆ μ ∈ ({0} : Set (Dual K H)), rootSpace P μ := by
      have := Submodule.sub_mem _ hx (h_mem_rootSpace P a)
      rw [add_right_comm, add_sub_cancel_right] at this
      exact rootSpace_le_biSup P (Set.mem_singleton 0) this
    have h0 := Submodule.disjoint_def.mp (disjoint_biSup P hS) _ hmem0 hmem
    rw [add_right_comm, add_comm, h0, add_zero]
    exact LinearMap.mem_range_self _ _
  · rintro _ ⟨a, rfl⟩; exact h_mem_rootSpace P a

/-- For `α > 0`, `𝔤̃_α ⊆ 𝔫̃₊` ([Kac] Thm. 1.2 (d)). -/
theorem rootSpace_pos_le {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    rootSpace P μ ≤ LinearMap.range (eHom P : FreeLieAlgebra K ι →ₗ[K] P.AuxLieAlgebra) := by
  intro x hx
  obtain ⟨⟨y, a, z⟩, rfl⟩ := (triangularEquiv P).surjective x
  rw [triangularEquiv_apply] at hx ⊢
  have hS : Disjoint (P.negWeights ∪ {0}) (P.posWeights) := by
    rw [Set.disjoint_union_left]
    exact ⟨P.disjoint_posWeights_negWeights.symm, by simp [P.zero_notMem_posWeights]⟩
  have hmem1 : fHom P y + h P a ∈ ⨆ μ ∈ P.negWeights ∪ {0}, rootSpace P μ :=
    Submodule.add_mem _ (mem_biSup_of_subset P (fun μ hμ ↦ Or.inl hμ) (fHom_mem P y))
      (mem_biSup_of_subset P (fun μ hμ ↦ Or.inr hμ) (h_mem_biSup P a))
  have hmem2 : fHom P y + h P a ∈ ⨆ μ ∈ P.posWeights, rootSpace P μ := by
    have := Submodule.sub_mem _ (rootSpace_le_biSup P hμ hx) (eHom_mem P z)
    convert this using 1; abel
  have h0 := Submodule.disjoint_def.mp (disjoint_biSup P hS) _ hmem1 hmem2
  rw [h0, zero_add]
  exact LinearMap.mem_range_self _ _

/-- For `α > 0`, `𝔤̃_{-α} ⊆ 𝔫̃₋` ([Kac] Thm. 1.2 (d)). -/
theorem rootSpace_neg_le {μ : Dual K H} (hμ : μ ∈ P.negWeights) :
    rootSpace P μ ≤ LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.AuxLieAlgebra) := by
  intro x hx
  obtain ⟨⟨y, a, z⟩, rfl⟩ := (triangularEquiv P).surjective x
  rw [triangularEquiv_apply] at hx ⊢
  have hS : Disjoint ({0} ∪ P.posWeights) (P.negWeights) := by
    rw [Set.disjoint_union_left]
    exact ⟨by simp [zero_notMem_negWeights], P.disjoint_posWeights_negWeights⟩
  have hmem1 : h P a + eHom P z ∈ ⨆ μ ∈ {0} ∪ P.posWeights, rootSpace P μ :=
    Submodule.add_mem _ (mem_biSup_of_subset P (fun μ hμ ↦ Or.inl hμ) (h_mem_biSup P a))
      (mem_biSup_of_subset P (fun μ hμ ↦ Or.inr hμ) (eHom_mem P z))
  have hmem2 : h P a + eHom P z ∈ ⨆ μ ∈ P.negWeights, rootSpace P μ := by
    have := Submodule.sub_mem _ (rootSpace_le_biSup P hμ hx) (fHom_mem P y)
    convert this using 1; abel
  have h0 := Submodule.disjoint_def.mp (disjoint_biSup P hS) _ hmem1 hmem2
  rw [add_assoc, h0, add_zero]
  exact LinearMap.mem_range_self _ _

/-! ### The maximal ideal `𝔯` -/

omit [CharZero K] in
/-- Ideals of `𝔤̃(A)` are stable under `ad 𝔥`. -/
lemma lie_h_mem (I : LieIdeal K P.AuxLieAlgebra) (a : H) :
    ∀ x ∈ I.toSubmodule, ⁅h P a, x⁆ ∈ I.toSubmodule :=
  fun _ hx ↦ I.lie_mem hx

/-- An ideal of `𝔤̃(A)` meeting `𝔥` trivially lies in the sum of the nonzero root spaces. -/
lemma le_of_inf_eq_bot {I : LieIdeal K P.AuxLieAlgebra}
    (hI : I.toSubmodule ⊓ LinearMap.range (h P) = ⊥) :
    I.toSubmodule ≤ ⨆ μ ∈ P.negWeights ∪ P.posWeights, rootSpace P μ := by
  have hle := inf_iSup_weightSpaceOfMap_le (h P) I.toSubmodule
    (lie_h_mem P I) (allWeights P)
  rw [iSup_rootSpace_eq_top, inf_top_eq] at hle
  refine hle.trans (iSup₂_le fun μ hμ ↦ ?_)
  rcases hμ with (hμ | hμ) | hμ
  · exact inf_le_right.trans (rootSpace_le_biSup P (Or.inl hμ))
  · rw [Set.mem_singleton_iff.mp hμ]
    exact (inf_le_inf_left _ (rootSpace_zero P).le).trans (hI.le.trans bot_le)
  · exact inf_le_right.trans (rootSpace_le_biSup P (Or.inr hμ))

/-- The maximal ideal `𝔯` of `𝔤̃(A)` meeting `𝔥` trivially ([Kac] Thm. 1.2 (e)). -/
def maxIdeal : LieIdeal K P.AuxLieAlgebra :=
  sSup {I | I.toSubmodule ⊓ LinearMap.range (h P) = ⊥}

lemma maxIdeal_le : (maxIdeal P).toSubmodule ≤
    ⨆ μ ∈ P.negWeights ∪ P.posWeights, rootSpace P μ := by
  change (sSup _ : LieIdeal K P.AuxLieAlgebra).toSubmodule ≤ _
  rw [LieSubmodule.sSup_toSubmodule]
  refine sSup_le ?_
  rintro _ ⟨I, hI, rfl⟩
  exact le_of_inf_eq_bot P hI

/-- `𝔯 ∩ 𝔥 = 0`. -/
theorem maxIdeal_inf_range_h :
    (maxIdeal P).toSubmodule ⊓ LinearMap.range (h P) = ⊥ := by
  rw [← rootSpace_zero]
  have hS : Disjoint (P.negWeights ∪ P.posWeights) ({0} : Set (Dual K H)) :=
    Set.disjoint_singleton_right.mpr fun h ↦
      h.elim P.zero_notMem_negWeights P.zero_notMem_posWeights
  refine eq_bot_iff.mpr fun x ⟨hx, hx0⟩ ↦ ?_
  exact Submodule.disjoint_def.mp (disjoint_biSup P hS) x (maxIdeal_le P hx)
    (rootSpace_le_biSup P (Set.mem_singleton 0) hx0)

/-- `𝔯` is the unique maximal ideal meeting `𝔥` trivially ([Kac] Thm. 1.2 (e)). -/
theorem le_maxIdeal_iff (I : LieIdeal K P.AuxLieAlgebra) :
    I ≤ maxIdeal P ↔ I.toSubmodule ⊓ LinearMap.range (h P) = ⊥ := by
  refine ⟨fun hI ↦ eq_bot_iff.mpr ?_, fun hI ↦ le_sSup hI⟩
  rw [← maxIdeal_inf_range_h P]
  exact inf_le_inf_right _ fun x hx ↦ hI hx

/-- `𝔯 = (𝔯 ∩ 𝔫̃₋) ⊕ (𝔯 ∩ 𝔫̃₊)` ([Kac] Thm. 1.2 (e)). -/
theorem maxIdeal_eq : (maxIdeal P).toSubmodule =
    (maxIdeal P).toSubmodule ⊓
        LinearMap.range (fHom P : FreeLieAlgebra K ι →ₗ[K] P.AuxLieAlgebra) ⊔
      (maxIdeal P).toSubmodule ⊓
        LinearMap.range (eHom P : FreeLieAlgebra K ι →ₗ[K] P.AuxLieAlgebra) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  have hle := inf_iSup_weightSpaceOfMap_le (h P) (maxIdeal P).toSubmodule
    (lie_h_mem P _) (P.negWeights ∪ P.posWeights)
  rw [inf_eq_left.mpr (maxIdeal_le P)] at hle
  refine hle.trans (iSup₂_le fun μ hμ ↦ ?_)
  rcases hμ with hμ | hμ
  · exact le_sup_of_le_left (inf_le_inf_left _ (rootSpace_neg_le P hμ))
  · exact le_sup_of_le_right (inf_le_inf_left _ (rootSpace_pos_le P hμ))

end AuxLieAlgebra

end Matrix.Realization

end
