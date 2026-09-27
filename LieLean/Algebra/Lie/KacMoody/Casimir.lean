/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CasimirForm
import LieLean.Algebra.Lie.KacMoody.HighestWeight

/-!
# The generalized Casimir operator

Let `A` be a symmetrizable generalized Cartan matrix with symmetrization `S`, realization
`(𝔥, Π, Π^∨)` over a field `K` of characteristic zero, and let `B = (·|·)` be a standard invariant
form on `𝔤 = 𝔤(A)` (`KacMoodyAlgebra.IsStandardForm`, [Kac] Thm. 2.2 (check)). Let `V` be a
`𝔤`-module such that for every `v ∈ V`, only finitely many positive root spaces `𝔤_α` act
nontrivially on `v` (`KacMoodyAlgebra.IsPosFinite`); every module in the category `𝒪` has this
property. Following [Kac] §2.5 the *generalized Casimir operator* on `V` is
`Ω = 2 ν⁻¹(ρ) + ∑ⱼ u^j u_j + 2 ∑_{α > 0} ∑ₖ e_{-α}^{(k)} e_α^{(k)}`,
where `{u_j}`, `{u^j}` are dual bases of `𝔥`, and `{e_α^{(k)}}`, `{e_{-α}^{(k)}}` are dual bases
of `𝔤_α` and `𝔤_{-α}`; the sum over `α > 0` is finite on each vector. We use the dual bases of
`KacMoody/CasimirForm.lean` for all root spaces including `𝔤_0 = 𝔥`; by
`IsStandardForm.casimirSum_eq_of_basis` the operator does not depend on these choices.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.IsPosFinite`: for every `v`, `𝔤_α v = 0` for all but
  finitely many `α ∈ Q₊ \ {0}`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimirTerm`: `∑ₖ e_{-μ}^{(k)} e_μ^{(k)}`.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimir`: the Casimir operator `Ω`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.IsCategoryO.isPosFinite`: modules in `𝒪` satisfy the
  finiteness condition.
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimir_lie`: `Ω` commutes with the action of
  `𝔤(A)` ([Kac] Thm. 2.6 (check)).
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimir_apply_of_lie_e_eq_zero`: on a vector
  `v` of weight `λ` killed by all the `eᵢ`, `Ω v = (λ + 2ρ | λ) v` ([Kac] Cor. 2.6 (check)).
* `Matrix.Realization.KacMoodyAlgebra.IsStandardForm.casimir_eq_smul_of_surjective`: `Ω` acts on
  any quotient of the Verma module `M(λ)` by the scalar `(λ + 2ρ | λ)` ([Kac] Cor. 2.6 (check)).

## Proof

For `z ∈ 𝔤_γ` and `μ ∈ 𝔥*` write `R_μ(z) = ∑ₖ e_{-μ}^{(k)} [z, e_μ^{(k)}]` and
`L_μ(z) = ∑ₖ [z, e_{-μ}^{(k)}] e_μ^{(k)}`. Then `[z, ∑ₖ e_{-μ}^{(k)} e_μ^{(k)}] = L_μ(z) + R_μ(z)`,
and [Kac] Lemma 2.4 (check) gives `L_μ(z) = -R_{μ-γ}(z)`. For `z = eᵢ` the sum over `μ > 0` of
`R_μ - R_{μ-αᵢ}` telescopes to `-R_0` (the `R_μ` vanish unless `𝔤_μ ≠ 0`, and `μ - αᵢ` with
`μ > 0` is either `0`, positive, or not a weight); for `z = fᵢ` one uses `L_μ - L_{μ-αᵢ}` instead.
The remaining terms in `𝔥` are computed with the dual bases of `𝔥`, and cancel since
`2(ρ | αᵢ) = (αᵢ | αᵢ)`. This is the argument of [Kac] §2.6, written out by us in this form.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §2.4–2.6.
-/

open Module LieModule

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} {P : Realization A K H}
  (V : Type*) [AddCommGroup V] [Module K V] [LieRingModule P.KacMoodyAlgebra V]
  [LieModule K P.KacMoodyAlgebra V]

variable (P) in
/-- A `𝔤(A)`-module `V` satisfies the finiteness condition of [Kac] §2.5 (check) if for every
`v ∈ V`, `𝔤_α v = 0` for all but finitely many `α ∈ Q₊ \ {0}`. Modules in the category `𝒪` have
this property (`IsCategoryO.isPosFinite`). -/
def IsPosFinite : Prop :=
  ∀ v : V, {α | α ∈ P.posWeights ∧ ∃ x ∈ rootSpace P α, ⁅x, v⁆ ≠ 0}.Finite

/-! ### Modules in the category `𝒪` -/

variable {V} in
/-- In a module in `𝒪`, only finitely many weights of the form `α + λ`, `α ∈ Q₊ \ {0}`, occur. -/
theorem IsCategoryO.finite_setOf_weightSpace_add_ne_bot [CharZero K] (hV : IsCategoryO P V)
    (μ₀ : Dual K H) :
    {α | α ∈ P.posWeights ∧ weightSpace P V (α + μ₀) ≠ ⊥}.Finite := by
  classical
  obtain ⟨s, hs⟩ := hV.exists_finset
  let c : Dual K H → ι → ℤ := fun Λ ↦
    if hc : ∃ c, P.rootOf c = Λ - μ₀ then hc.choose else 0
  refine (s.finite_toSet.biUnion fun Λ _ ↦ ((Set.Finite.pi (t := fun i ↦ Set.Icc 0 (c Λ i))
    fun i ↦ Set.finite_Icc _ _).image P.rootOf)).subset ?_
  rintro _ ⟨⟨l, hl, rfl⟩, hne⟩
  obtain ⟨Λ, hΛ, k, hk, heq⟩ := hs _ hne
  have hlk : P.rootOf (l + k) = Λ - μ₀ := by
    rw [map_add, ← sub_eq_zero, ← sub_eq_zero.mpr heq]
    abel
  have hex : ∃ c, P.rootOf c = Λ - μ₀ := ⟨_, hlk⟩
  have hc : c Λ = l + k := P.rootOf_injective (by
    simp only [c, hex, ↓reduceDIte]
    rw [hex.choose_spec, hlk])
  refine Set.mem_biUnion hΛ ⟨l, fun i _ ↦ ⟨hl.1 i, ?_⟩, rfl⟩
  rw [hc, Pi.add_apply, le_add_iff_nonneg_right]
  exact hk i

variable {V} in
/-- Modules in the category `𝒪` satisfy the finiteness condition of [Kac] §2.5 (check). -/
theorem IsCategoryO.isPosFinite [CharZero K] (hV : IsCategoryO P V) : IsPosFinite P V := by
  intro v
  have hv : v ∈ ⨆ μ, weightSpace P V μ := by rw [hV.iSup_weightSpaceOfMap_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun v ↦
    {α | α ∈ P.posWeights ∧ ∃ x ∈ rootSpace P α, ⁅x, v⁆ ≠ 0}.Finite) hv ?_ ?_ ?_
  · intro μ v hv
    refine (hV.finite_setOf_weightSpace_add_ne_bot μ).subset ?_
    rintro α ⟨hα, x, hx, hxv⟩
    refine ⟨hα, fun hbot ↦ hxv ?_⟩
    have : ⁅x, v⁆ ∈ weightSpace P V (α + μ) := lie_mem_weightSpaceOfMap (h P) hx hv
    rwa [hbot, Submodule.mem_bot] at this
  · simp
  · intro v w hv hw
    refine (hv.union hw).subset ?_
    rintro α ⟨hα, x, hx, hxv⟩
    by_cases h1 : ⁅x, v⁆ = 0
    · exact Or.inr ⟨hα, x, hx, by rwa [lie_add, h1, zero_add] at hxv⟩
    · exact Or.inl ⟨hα, x, hx, h1⟩

/-! ### Telescoping sums over positive weights -/

omit [Fintype ι] [DecidableEq ι] in
lemma one_le_sum_of_mem_posCone [Fintype ι] {k : ι → ℤ} (hk : k ∈ posCone ι) : 1 ≤ ∑ j, k j := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk.2
  have h0 := hk.1 j
  simp only [Pi.zero_apply] at hj h0
  exact (show 1 ≤ k j by omega).trans (Finset.single_le_sum (fun j _ ↦ hk.1 j) (Finset.mem_univ j))

omit [DecidableEq ι] in
variable (P) in
/-- If `β ∈ -(Q₊ \ {0})`, then `β + αᵢ ∉ Q₊ \ {0}`. -/
lemma add_root_notMem_posWeights [CharZero K] {β : Dual K H} (hβ : β ∈ P.negWeights) (i : ι) :
    β + P.root i ∉ P.posWeights := by
  classical
  rintro ⟨l, hl, hl'⟩
  obtain ⟨k, hk, rfl⟩ := hβ
  simp only at hl'
  have heq : P.rootOf (l + k) = P.rootOf (Pi.single i 1) := by
    rw [map_add, rootOf_single, hl']
    abel
  have := congrArg (fun f : ι → ℤ ↦ ∑ j, f j) (P.rootOf_injective heq)
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true] at this
  have h1 := one_le_sum_of_mem_posCone hl
  have h2 := one_le_sum_of_mem_posCone hk
  omega

variable (P) in
/-- Shifting a sum over the positive weights by a simple root: if `F` vanishes at `μ` whenever
`𝔤_μ = 0`, then `∑_{μ > 0} F(μ - αᵢ) = F(0) + ∑_{μ > 0} F(μ)`. -/
theorem finsum_mem_posWeights_sub_root [CharZero K] {M : Type*} [AddCommGroup M]
    (F : Dual K H → M) (i : ι) (hF : ∀ μ, rootSpace P μ = ⊥ → F μ = 0)
    (hfin : (P.posWeights ∩ Function.support F).Finite) :
    ∑ᶠ μ ∈ P.posWeights, F (μ - P.root i) = F 0 + ∑ᶠ μ ∈ P.posWeights, F μ := by
  have hpt (β : Dual K H) : P.posWeights.indicator (fun μ ↦ F (μ - P.root i)) (β + P.root i) =
      (insert 0 P.posWeights).indicator F β := by
    by_cases hβ : β ∈ insert 0 P.posWeights
    · have : β + P.root i ∈ P.posWeights := by
        rcases hβ with rfl | hβ
        · simpa using P.root_mem_posWeights i
        · exact P.posWeights_add hβ (P.root_mem_posWeights i)
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hβ, add_sub_cancel_right]
    · rw [Set.indicator_of_notMem hβ]
      by_cases h' : β + P.root i ∈ P.posWeights
      · rw [Set.indicator_of_mem h', add_sub_cancel_right]
        refine hF β (by_contra fun hne ↦ ?_)
        rcases mem_allWeights_of_rootSpace_ne_bot P hne with (hneg | h0) | hpos
        · exact add_root_notMem_posWeights P hneg i h'
        · exact hβ (Or.inl h0)
        · exact hβ (Or.inr hpos)
      · rw [Set.indicator_of_notMem h']
  calc ∑ᶠ μ ∈ P.posWeights, F (μ - P.root i)
      = ∑ᶠ μ, P.posWeights.indicator (fun μ ↦ F (μ - P.root i)) μ := finsum_mem_def _ _
    _ = ∑ᶠ β, P.posWeights.indicator (fun μ ↦ F (μ - P.root i))
          (Equiv.addRight (P.root i) β) := (finsum_comp_equiv _).symm
    _ = ∑ᶠ β, (insert 0 P.posWeights).indicator F β := finsum_congr hpt
    _ = ∑ᶠ β ∈ insert 0 P.posWeights, F β := (finsum_mem_def _ _).symm
    _ = F 0 + ∑ᶠ μ ∈ P.posWeights, F μ := finsum_mem_insert' F P.zero_notMem_posWeights hfin

variable (P) in
lemma finite_posWeights_inter_support_sub_root [CharZero K] {M : Type*} [AddCommGroup M]
    (F : Dual K H → M) (i : ι) (hF : ∀ μ, rootSpace P μ = ⊥ → F μ = 0)
    (hfin : (P.posWeights ∩ Function.support F).Finite) :
    (P.posWeights ∩ Function.support fun μ ↦ F (μ - P.root i)).Finite := by
  refine ((hfin.insert 0).preimage (f := fun μ ↦ μ - P.root i)
    (sub_left_injective.injOn)).subset ?_
  rintro μ ⟨hμ, hne⟩
  simp only [Set.mem_preimage, Set.mem_insert_iff]
  by_cases h0 : μ - P.root i = 0
  · exact Or.inl h0
  refine Or.inr ⟨?_, hne⟩
  have hne' : rootSpace P (μ - P.root i) ≠ ⊥ := fun hbot ↦ hne (hF _ hbot)
  rcases mem_allWeights_of_rootSpace_ne_bot P hne' with (hneg | h0') | hpos
  · exact absurd (by rwa [sub_add_cancel]) (add_root_notMem_posWeights P hneg i)
  · exact absurd h0' h0
  · exact hpos

omit [Fintype ι] [DecidableEq ι] in
private lemma finsum_mem_sub_distrib_of_finite {α M : Type*} [AddCommGroup M] {s : Set α}
    {f g : α → M} (hf : (s ∩ Function.support f).Finite)
    (hg : (s ∩ Function.support g).Finite) :
    ∑ᶠ i ∈ s, (f i - g i) = ∑ᶠ i ∈ s, f i - ∑ᶠ i ∈ s, g i := by
  have hfg : (s ∩ Function.support fun i ↦ f i - g i).Finite :=
    (hf.union hg).subset fun i ⟨his, hi⟩ ↦ by
      rcases Function.support_sub f g hi with h | h
      · exact Or.inl ⟨his, h⟩
      · exact Or.inr ⟨his, h⟩
  rw [eq_sub_iff_add_eq, ← finsum_mem_add_distrib' hfg hg]
  simp only [sub_add_cancel]

omit [DecidableEq ι] in
/-- `(αᵢ | αᵢ) = 2 (αᵢ | ρ)`, i.e. `⟨αᵢ, ν⁻¹(αᵢ)⟩ = 2 ⟨αᵢ, ν⁻¹(ρ)⟩`. -/
lemma root_toDual_symm_root [CharZero K] [FiniteDimensional K H] (S : A.Symmetrization)
    (hA : A.IsGeneralizedCartan) (i : ι) :
    P.root i ((P.toDual S).symm (P.root i)) = 2 * P.root i ((P.toDual S).symm P.rho) := by
  rw [← dualBilinForm_apply_eq, ← dualBilinForm_apply_eq, (P.isSymm_dualBilinForm S).eq _ P.rho,
    two_mul_dualBilinForm_rho_root S hA]

/-! ### The Casimir operator -/

/-- The bilinear map `(y, x) ↦ y (x v)`. -/
def lieLieBilin (v : V) : P.KacMoodyAlgebra →ₗ[K] P.KacMoodyAlgebra →ₗ[K] V :=
  LinearMap.mk₂ K (fun y x ↦ ⁅y, ⁅x, v⁆⁆) (fun _ _ _ ↦ add_lie _ _ _) (fun _ _ _ ↦ smul_lie _ _ _)
    (fun _ _ _ ↦ by rw [add_lie, lie_add]) (fun _ _ _ ↦ by rw [smul_lie, lie_smul])

@[simp] lemma lieLieBilin_apply (v : V) (y x : P.KacMoodyAlgebra) :
    lieLieBilin V v y x = ⁅y, ⁅x, v⁆⁆ := rfl

variable [CharZero K] [FiniteDimensional K H] {S : A.Symmetrization}
  {B : LinearMap.BilinForm K P.KacMoodyAlgebra}

namespace IsStandardForm

variable (hB : IsStandardForm P S B)
include hB

/-- The operator `∑ₖ e_{-μ}^{(k)} e_μ^{(k)}` on `V`, for dual bases `{e_μ^{(k)}}` of `𝔤_μ` and
`{e_{-μ}^{(k)}}` of `𝔤_{-μ}`. For `μ = 0` it is `∑ⱼ u^j u_j` for dual bases of `𝔥`. -/
def casimirTerm (μ : Dual K H) : Module.End K V :=
  ∑ k, toEnd K P.KacMoodyAlgebra V (hB.dualBasis μ k) *
    toEnd K P.KacMoodyAlgebra V (rootSpaceBasis P μ k)

lemma casimirTerm_apply (μ : Dual K H) (v : V) :
    hB.casimirTerm V μ v = hB.casimirSum (fun y x ↦ ⁅y, ⁅x, v⁆⁆) μ := by
  simp [casimirTerm, casimirSum_def, LinearMap.sum_apply]

variable {V}

lemma exists_of_casimirTerm_ne_zero {μ : Dual K H} {v : V} (hv : hB.casimirTerm V μ v ≠ 0) :
    ∃ x ∈ rootSpace P μ, ⁅x, v⁆ ≠ 0 := by
  rw [casimirTerm_apply] at hv
  obtain ⟨y, -, x, hx, hne⟩ := hB.exists_ne_zero_of_casimirSum_ne_zero hv
  exact ⟨x, hx, fun h0 ↦ hne (by rw [h0, lie_zero])⟩

lemma finite_casimirTerm (hV : IsPosFinite P V) (v : V) :
    (P.posWeights ∩ Function.support fun μ ↦ hB.casimirTerm V μ v).Finite :=
  (hV v).subset fun _ ⟨hμ, hne⟩ ↦ ⟨hμ, hB.exists_of_casimirTerm_ne_zero hne⟩

variable (V) in
/-- The generalized Casimir operator ([Kac] §2.5 (check))
`Ω = 2 ν⁻¹(ρ) + ∑ⱼ u^j u_j + 2 ∑_{α > 0} ∑ₖ e_{-α}^{(k)} e_α^{(k)}` on a module `V` satisfying the
finiteness condition `IsPosFinite`. -/
def casimir (hV : IsPosFinite P V) : Module.End K V where
  toFun v := (2 : K) • ⁅h P ((P.toDual S).symm P.rho), v⁆ + hB.casimirTerm V 0 v +
    (2 : K) • ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ v
  map_add' v w := by
    simp only [map_add, lie_add]
    rw [finsum_mem_add_distrib' (hB.finite_casimirTerm hV v) (hB.finite_casimirTerm hV w)]
    module
  map_smul' c v := by
    simp only [map_smul, lie_smul, RingHom.id_apply]
    have := (DistribSMul.toAddMonoidHom V c).map_finsum_mem' (hB.finite_casimirTerm hV v)
    simp only [DistribSMul.toAddMonoidHom_apply] at this
    rw [← this]
    module

lemma casimir_apply (hV : IsPosFinite P V) (v : V) :
    hB.casimir V hV v = (2 : K) • ⁅h P ((P.toDual S).symm P.rho), v⁆ + hB.casimirTerm V 0 v +
      (2 : K) • ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ v := rfl

/-! ### Commutation with `𝔤(A)` -/

/-- An element `x ∈ 𝔤_0 = 𝔥` acts on a weight vector `m` of weight `λ` by `(ν⁻¹(λ) | x)`. -/
lemma lie_of_mem_rootSpace_zero {M : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule P.KacMoodyAlgebra M] [LieModule K P.KacMoodyAlgebra M]
    {x : P.KacMoodyAlgebra} (hx : x ∈ rootSpace P 0) {Λ : Dual K H}
    {m : M} (hm : m ∈ weightSpaceOfMap M (h P) Λ) :
    ⁅x, m⁆ = B (h P ((P.toDual S).symm Λ)) x • m := by
  rw [rootSpace_zero] at hx
  obtain ⟨a, rfl⟩ := hx
  rw [hm a, hB.h_h, bilinForm_toDual_symm_left]

variable (V)

lemma lie_casimirTerm (z : P.KacMoodyAlgebra) (μ : Dual K H) (v : V) :
    ⁅z, hB.casimirTerm V μ v⁆ = hB.casimirSum (fun y x ↦ ⁅⁅z, y⁆, ⁅x, v⁆⁆) μ +
      hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅z, x⁆, v⁆⁆) μ + hB.casimirTerm V μ ⁅z, v⁆ := by
  simp only [casimirTerm_apply, casimirSum_def, lie_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [leibniz_lie z (hB.dualBasis μ k), leibniz_lie z (rootSpaceBasis P μ k : P.KacMoodyAlgebra) v,
    lie_add]
  abel

/-- [Kac] Lemma 2.4 (check), in the form `L_μ(z) = -R_{μ-γ}(z)` for `z ∈ 𝔤_γ`. -/
lemma casimirSum_lie_left_lie {γ : Dual K H} {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P γ)
    (μ : Dual K H) (v : V) :
    hB.casimirSum (fun y x ↦ ⁅⁅z, y⁆, ⁅x, v⁆⁆) μ =
      -hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅z, x⁆, v⁆⁆) (μ - γ) := by
  have := hB.casimirSum_lie_left (lieLieBilin V v) hz μ
  simp only [lieLieBilin_apply] at this
  rw [← this, eq_neg_iff_add_eq_zero, casimirSum_def, casimirSum_def, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [← add_lie, ← lie_skew z, neg_add_cancel, zero_lie]

/-- For `z ∈ 𝔤_γ`: `[z, ∑ₖ e_{-μ}^{(k)} e_μ^{(k)}] = R_μ(z) - R_{μ-γ}(z)`. -/
lemma lie_casimirTerm_sub {γ : Dual K H} {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P γ)
    (μ : Dual K H) (v : V) :
    ⁅z, hB.casimirTerm V μ v⁆ - hB.casimirTerm V μ ⁅z, v⁆ =
      hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅z, x⁆, v⁆⁆) μ -
        hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅z, x⁆, v⁆⁆) (μ - γ) := by
  rw [lie_casimirTerm, hB.casimirSum_lie_left_lie V hz]
  abel

/-- For `z ∈ 𝔤_γ`: `[z, ∑ₖ e_{-μ}^{(k)} e_μ^{(k)}] = L_μ(z) - L_{μ+γ}(z)`. -/
lemma lie_casimirTerm_sub' {γ : Dual K H} {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P γ)
    (μ : Dual K H) (v : V) :
    ⁅z, hB.casimirTerm V μ v⁆ - hB.casimirTerm V μ ⁅z, v⁆ =
      hB.casimirSum (fun y x ↦ ⁅⁅z, y⁆, ⁅x, v⁆⁆) μ -
        hB.casimirSum (fun y x ↦ ⁅⁅z, y⁆, ⁅x, v⁆⁆) (μ + γ) := by
  rw [lie_casimirTerm, hB.casimirSum_lie_left_lie V hz (μ + γ), add_sub_cancel_right]
  abel

/-- The `𝔥`-part of `L`: `L_0(z) = -z ν⁻¹(γ)` for `z ∈ 𝔤_γ`. -/
lemma casimirSum_zero_left {γ : Dual K H} {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P γ)
    (v : V) :
    hB.casimirSum (fun y x ↦ ⁅⁅z, y⁆, ⁅x, v⁆⁆) 0 = -⁅z, ⁅h P ((P.toDual S).symm γ), v⁆⁆ := by
  have hH : h P ((P.toDual S).symm γ) ∈ rootSpace P 0 := by
    rw [rootSpace_zero]; exact ⟨_, rfl⟩
  conv_rhs => rw [← hB.sum_smul_basis 0 hH]
  simp only [casimirSum_def, sum_lie, lie_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk : hB.dualBasis 0 k ∈ rootSpace P 0 := by simpa using hB.dualBasis_mem 0 k
  rw [← lie_skew z, hB.lie_of_mem_rootSpace_zero hk hz, neg_lie, smul_lie, smul_lie, lie_smul]

/-- The `𝔥`-part of `R`: `R_0(z) = -ν⁻¹(γ) z` for `z ∈ 𝔤_γ`. -/
lemma casimirSum_zero_right {γ : Dual K H} {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P γ)
    (v : V) :
    hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅z, x⁆, v⁆⁆) 0 = -⁅h P ((P.toDual S).symm γ), ⁅z, v⁆⁆ := by
  have hH : h P ((P.toDual S).symm γ) ∈ rootSpace P (-0) := by
    rw [neg_zero, rootSpace_zero]; exact ⟨_, rfl⟩
  conv_rhs => rw [← hB.sum_smul_dualBasis 0 hH]
  simp only [casimirSum_def, sum_lie, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← lie_skew z, hB.lie_of_mem_rootSpace_zero (rootSpaceBasis_mem P 0 k) hz, neg_lie,
    smul_lie, lie_neg, lie_smul, smul_lie, hB.symm]

omit [CharZero K] [FiniteDimensional K H] hB in
lemma lie_lie_h_sub {γ : Dual K H} {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P γ) (a : H)
    (v : V) : ⁅z, ⁅h P a, v⁆⁆ - ⁅h P a, ⁅z, v⁆⁆ = -(γ a • ⁅z, v⁆) := by
  rw [← lie_lie, ← lie_skew, hz a, neg_lie, smul_lie]

/-- `R_0(z) - L_0(z) = -⟨γ, ν⁻¹(γ)⟩ z` for `z ∈ 𝔤_γ`. -/
lemma casimirSum_zero_right_sub_left {γ : Dual K H} {z : P.KacMoodyAlgebra}
    (hz : z ∈ rootSpace P γ) (v : V) :
    hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅z, x⁆, v⁆⁆) 0 - hB.casimirSum (fun y x ↦ ⁅⁅z, y⁆, ⁅x, v⁆⁆) 0 =
      -(γ ((P.toDual S).symm γ) • ⁅z, v⁆) := by
  rw [hB.casimirSum_zero_right V hz, hB.casimirSum_zero_left V hz, ← lie_lie_h_sub V hz]
  abel

variable {V}

omit [Module K V] [LieModule K P.KacMoodyAlgebra V] in
lemma finite_casimirSum_left (hV : IsPosFinite P V) (z : P.KacMoodyAlgebra) (v : V) :
    (P.posWeights ∩ Function.support fun μ ↦
      hB.casimirSum (fun y x ↦ ⁅⁅z, y⁆, ⁅x, v⁆⁆) μ).Finite := by
  refine (hV v).subset fun μ ⟨hμ, hne⟩ ↦ ⟨hμ, ?_⟩
  obtain ⟨y, -, x, hx, hne⟩ := hB.exists_ne_zero_of_casimirSum_ne_zero hne
  exact ⟨x, hx, fun h0 ↦ hne (by rw [h0, lie_zero])⟩

omit [Module K V] [LieModule K P.KacMoodyAlgebra V] in
lemma finite_casimirSum_right (hV : IsPosFinite P V) {γ : Dual K H} (hγ : γ ∈ P.posWeights)
    {z : P.KacMoodyAlgebra} (hz : z ∈ rootSpace P γ) (v : V) :
    (P.posWeights ∩ Function.support fun μ ↦
      hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅z, x⁆, v⁆⁆) μ).Finite := by
  refine ((hV v).preimage (f := fun μ ↦ γ + μ) (add_right_injective γ).injOn).subset
    fun μ ⟨hμ, hne⟩ ↦ ?_
  obtain ⟨y, -, x, hx, hne⟩ := hB.exists_ne_zero_of_casimirSum_ne_zero hne
  exact ⟨P.posWeights_add hγ hμ, ⁅z, x⁆, lie_mem_weightSpaceOfMap (h P) hz hx,
    fun h0 ↦ hne (by rw [h0, lie_zero])⟩

lemma lie_finsum_casimirTerm_sub (hV : IsPosFinite P V) (z : P.KacMoodyAlgebra) (v : V) :
    ⁅z, ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ v⁆ -
        ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ ⁅z, v⁆ =
      ∑ᶠ μ ∈ P.posWeights, (⁅z, hB.casimirTerm V μ v⁆ - hB.casimirTerm V μ ⁅z, v⁆) := by
  have h1 := (toEnd K P.KacMoodyAlgebra V z).toAddMonoidHom.map_finsum_mem'
    (hB.finite_casimirTerm hV v)
  simp only [LinearMap.toAddMonoidHom_coe, toEnd_apply_apply] at h1
  rw [h1, finsum_mem_sub_distrib_of_finite _ (hB.finite_casimirTerm hV _)]
  refine (hB.finite_casimirTerm hV v).subset fun μ ⟨hμ, hne⟩ ↦ ⟨hμ, fun h0 ↦ hne ?_⟩
  simp only [h0, lie_zero]

/-- `Ω` commutes with `eᵢ` ([Kac] Thm. 2.6 (check)). -/
theorem casimir_lie_e (hA : A.IsGeneralizedCartan) (hV : IsPosFinite P V) (i : ι) (v : V) :
    hB.casimir V hV ⁅e P i, v⁆ = ⁅e P i, hB.casimir V hV v⁆ := by
  have hz : e P i ∈ rootSpace P (P.root i) := fun a ↦ lie_h_e P a i
  have hfin := hB.finite_casimirSum_right hV (P.root_mem_posWeights i) hz v
  have hR0 : ∀ μ, rootSpace P μ = ⊥ → hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅e P i, x⁆, v⁆⁆) μ = 0 :=
    fun μ hμ ↦ hB.casimirSum_eq_zero_of_eq_bot (fun y ↦ by simp) hμ
  have hsum : ⁅e P i, ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ v⁆ -
      ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ ⁅e P i, v⁆ =
      -hB.casimirSum (fun y x ↦ ⁅y, ⁅⁅e P i, x⁆, v⁆⁆) 0 := by
    rw [hB.lie_finsum_casimirTerm_sub hV,
      finsum_mem_congr rfl fun μ _ ↦ hB.lie_casimirTerm_sub V hz μ v,
      finsum_mem_sub_distrib_of_finite hfin
        (finite_posWeights_inter_support_sub_root P _ i hR0 hfin),
      finsum_mem_posWeights_sub_root P _ i hR0 hfin]
    abel
  have h0 := hB.lie_casimirTerm_sub V hz 0 v
  have hL := hB.casimirSum_lie_left_lie V hz 0 v
  have hRL := hB.casimirSum_zero_right_sub_left V hz v
  have hρ := lie_lie_h_sub V hz ((P.toDual S).symm P.rho) v
  rw [root_toDual_symm_root S hA] at hRL
  simp only [casimir_apply, lie_add, lie_smul]
  linear_combination (norm := module) -(2 : K) • hρ - h0 - (2 : K) • hsum + hL + hRL

/-- `Ω` commutes with `fᵢ` ([Kac] Thm. 2.6 (check)). -/
theorem casimir_lie_f (hA : A.IsGeneralizedCartan) (hV : IsPosFinite P V) (i : ι) (v : V) :
    hB.casimir V hV ⁅f P i, v⁆ = ⁅f P i, hB.casimir V hV v⁆ := by
  have hz : f P i ∈ rootSpace P (-P.root i) := fun a ↦ by
    rw [lie_h_f, LinearMap.neg_apply, neg_smul]
  have hfin := hB.finite_casimirSum_left hV (f P i) v
  have hL0 : ∀ μ, rootSpace P μ = ⊥ → hB.casimirSum (fun y x ↦ ⁅⁅f P i, y⁆, ⁅x, v⁆⁆) μ = 0 :=
    fun μ hμ ↦ hB.casimirSum_eq_zero_of_eq_bot (fun y ↦ by simp) hμ
  have hsum : ⁅f P i, ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ v⁆ -
      ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ ⁅f P i, v⁆ =
      -hB.casimirSum (fun y x ↦ ⁅⁅f P i, y⁆, ⁅x, v⁆⁆) 0 := by
    rw [hB.lie_finsum_casimirTerm_sub hV,
      finsum_mem_congr rfl fun μ _ ↦ by rw [hB.lie_casimirTerm_sub' V hz μ v, ← sub_eq_add_neg],
      finsum_mem_sub_distrib_of_finite hfin
        (finite_posWeights_inter_support_sub_root P _ i hL0 hfin),
      finsum_mem_posWeights_sub_root P _ i hL0 hfin]
    abel
  have h0 := hB.lie_casimirTerm_sub' V hz 0 v
  have hR := hB.casimirSum_lie_left_lie V hz (0 + -P.root i) v
  rw [add_sub_cancel_right] at hR
  have hRL := hB.casimirSum_zero_right_sub_left V hz v
  have hρ := lie_lie_h_sub V hz ((P.toDual S).symm P.rho) v
  simp only [map_neg, LinearMap.neg_apply, neg_neg, root_toDual_symm_root S hA] at hRL hρ
  simp only [casimir_apply, lie_add, lie_smul]
  linear_combination (norm := module) -(2 : K) • hρ - h0 - (2 : K) • hsum + hR - hRL

omit [CharZero K] [FiniteDimensional K H] hB in
lemma h_mem_rootSpace_zero (a : H) : h P a ∈ rootSpace P 0 := fun b ↦ by
  rw [lie_h_h, LinearMap.zero_apply, zero_smul]

/-- `Ω` commutes with `𝔥` ([Kac] Thm. 2.6 (check)). -/
theorem casimir_lie_h (hV : IsPosFinite P V) (a : H) (v : V) :
    hB.casimir V hV ⁅h P a, v⁆ = ⁅h P a, hB.casimir V hV v⁆ := by
  have hz := h_mem_rootSpace_zero (P := P) a
  have hsum : ⁅h P a, ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ v⁆ -
      ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ ⁅h P a, v⁆ = 0 := by
    rw [hB.lie_finsum_casimirTerm_sub hV]
    exact finsum_mem_eq_zero_of_forall_eq_zero fun μ _ ↦ by
      rw [hB.lie_casimirTerm_sub V hz μ v, sub_zero, sub_self]
  have h0 := hB.lie_casimirTerm_sub V hz 0 v
  rw [sub_zero, sub_self] at h0
  have hρ := lie_lie_h_sub V hz ((P.toDual S).symm P.rho) v
  rw [LinearMap.zero_apply, zero_smul, neg_zero] at hρ
  simp only [casimir_apply, lie_add, lie_smul]
  linear_combination (norm := module) -(2 : K) • hρ - h0 - (2 : K) • hsum

/-- **The Casimir operator commutes with `𝔤(A)`** ([Kac] Thm. 2.6 (check)): for a module `V`
satisfying the finiteness condition `IsPosFinite`, `Ω [x, v] = [x, Ω v]`. -/
theorem casimir_lie (hA : A.IsGeneralizedCartan) (hV : IsPosFinite P V) (x : P.KacMoodyAlgebra)
    (v : V) : hB.casimir V hV ⁅x, v⁆ = ⁅x, hB.casimir V hV v⁆ := by
  revert v
  refine induction_on P x (fun i ↦ hB.casimir_lie_e hA hV i) (fun i ↦ hB.casimir_lie_f hA hV i)
    (fun a ↦ hB.casimir_lie_h hV a) (by simp) ?_ ?_ ?_
  · intro y z hy hz v
    rw [add_lie, map_add, hy, hz, add_lie]
  · intro c y hy v
    rw [smul_lie, map_smul, hy, smul_lie]
  · intro y z hy hz v
    simp only [lie_lie, map_sub, hy, hz]

/-! ### The Casimir operator on highest-weight modules -/

/-- **[Kac] Cor. 2.6 (check)**: if `v ∈ V` has weight `Λ` and is killed by all the `eᵢ`, then
`Ω v = (Λ + 2ρ | Λ) v`. -/
theorem casimir_apply_of_lie_e_eq_zero (hV : IsPosFinite P V) {Λ : Dual K H} {v : V}
    (hv : v ∈ weightSpace P V Λ) (he : ∀ i, ⁅e P i, v⁆ = 0) :
    hB.casimir V hV v = P.dualBilinForm S (Λ + 2 • P.rho) Λ • v := by
  have hpos : ∑ᶠ μ ∈ P.posWeights, hB.casimirTerm V μ v = 0 := by
    refine finsum_mem_eq_zero_of_forall_eq_zero fun μ hμ ↦ ?_
    rw [casimirTerm_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have hk : (rootSpaceBasis P μ k : P.KacMoodyAlgebra) ∈ (nPos P).toSubmodule := by
      rw [nPos_toSubmodule_eq]
      exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ (rootSpaceBasis_mem P μ k))
    simp only
    rw [lie_eq_zero_of_mem_nPos he hk, lie_zero]
  have h0 : hB.casimirTerm V 0 v = ⁅h P ((P.toDual S).symm Λ), v⁆ := by
    have hH : h P ((P.toDual S).symm Λ) ∈ rootSpace P (-0) := by
      rw [neg_zero, rootSpace_zero]; exact ⟨_, rfl⟩
    conv_rhs => rw [← hB.sum_smul_dualBasis 0 hH]
    rw [casimirTerm_apply, casimirSum_def, sum_lie]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hB.lie_of_mem_rootSpace_zero (rootSpaceBasis_mem P 0 k) hv, lie_smul, smul_lie, hB.symm]
  have hsymm : P.rho ((P.toDual S).symm Λ) = Λ ((P.toDual S).symm P.rho) := by
    rw [← dualBilinForm_apply_eq, ← dualBilinForm_apply_eq, (P.isSymm_dualBilinForm S).eq]
  rw [casimir_apply, hpos, h0, hv, hv, dualBilinForm_apply_eq, LinearMap.add_apply,
    LinearMap.smul_apply, hsymm]
  module

/-- **[Kac] Cor. 2.6 (check)**: the Casimir operator acts on every quotient `V` of the Verma
module `M(Λ)` by the scalar `(Λ + 2ρ | Λ)`. -/
theorem casimir_eq_smul_of_surjective (hA : A.IsGeneralizedCartan) (hV : IsPosFinite P V)
    {Λ : Dual K H} (φ : VermaModule P Λ →ₗ⁅K,P.KacMoodyAlgebra⁆ V) (hφ : Function.Surjective φ)
    (v : V) : hB.casimir V hV v = P.dualBilinForm S (Λ + 2 • P.rho) Λ • v := by
  let N : LieSubmodule K P.KacMoodyAlgebra V :=
    { carrier := {v | hB.casimir V hV v = P.dualBilinForm S (Λ + 2 • P.rho) Λ • v}
      add_mem' := fun {v w} (hv : _ = _) (hw : _ = _) ↦ show _ = _ by
        rw [map_add, hv, hw, smul_add]
      zero_mem' := show _ = _ by rw [map_zero, smul_zero]
      smul_mem' := fun c v (hv : _ = _) ↦ show _ = _ by rw [map_smul, hv, smul_comm]
      lie_mem := fun {x v} (hv : _ = _) ↦ show _ = _ by rw [hB.casimir_lie hA, hv, lie_smul] }
  have hle : LieSubmodule.lieSpan K P.KacMoodyAlgebra {φ (VermaModule.hwv P Λ)} ≤ N := by
    rw [LieSubmodule.lieSpan_le]
    rintro _ rfl
    exact hB.casimir_apply_of_lie_e_eq_zero hV
      (map_mem_weightSpaceOfMap P φ (VermaModule.hwv_mem_weightSpace P Λ))
      fun i ↦ by rw [← LieModuleHom.map_lie, VermaModule.lie_e_hwv, map_zero]
  rw [VermaModule.lieSpan_map_hwv_eq_top φ hφ] at hle
  exact hle (LieSubmodule.mem_top v)

end IsStandardForm

end Matrix.Realization.KacMoodyAlgebra
