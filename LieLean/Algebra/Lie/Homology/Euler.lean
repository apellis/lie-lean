/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Weights
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Weight spaces of the chains and the Euler characteristic

We keep the setting of `LieLean.Algebra.Lie.Homology.Weights`: a vector space `H` acts on a Lie
algebra `L` by derivations and compatibly on an `L`-module `M` (a `DerivAction`). We assume that
`L` and `M` have bases `(x_i)_{i ∈ I}` and `(m_j)_{j ∈ J}` of weight vectors, of weights `γ i` and
`ν j`, with `I` linearly ordered. Then `⋀L ⊗ M` has the basis
`x_S ⊗ m_j = x_{i₁} ∧ ⋯ ∧ x_{i_k} ⊗ m_j` (`S = {i₁ < ⋯ < i_k}`) of weight vectors of weight
`γ S + ν j`, `γ S = ∑_{i ∈ S} γ i`, and degree `|S|`. Hence the weight-`μ` chains of degree `k`
have dimension `#{(S, j) | |S| = k, γ S + ν j = μ}`, and when there are finitely many pairs
`(S, j)` of weight `μ`:

* (Euler characteristic of the chains) `∑_k (-1)^k dim C_k(L, M)_μ = ∑_{γ S + ν j = μ} (-1)^{|S|}`;
* (Euler–Poincaré principle) `∑_k (-1)^k dim H_k(L, M)_μ = ∑_k (-1)^k dim C_k(L, M)_μ`.

## Main definitions

* `LieModule.ChevalleyEilenberg.DerivAction.chainBasis`: the basis `x_S ⊗ m_j` of `⋀L ⊗ M`.
* `LieModule.ChevalleyEilenberg.DerivAction.chainWt`: its weights `γ S + ν j`.

## Main results

* `LieModule.ChevalleyEilenberg.DerivAction.chainsIn_inf_chainWeightSpace_eq_span`:
  `C_k(L, M)_μ` is spanned by the basis vectors of degree `k` and weight `μ`.
* `LieModule.ChevalleyEilenberg.DerivAction.finrank_chainsIn_inf_chainWeightSpace`: its
  dimension.
* `LieModule.ChevalleyEilenberg.DerivAction.sum_neg_one_pow_finrank_chains`: the Euler
  characteristic of the weight-`μ` chains.
* `LieModule.ChevalleyEilenberg.DerivAction.sum_neg_one_pow_finrank_homology`: the Euler
  characteristic of the weight-`μ` homology.

## References

* H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent. Math.
  **34** (1976), 37–76, Lemma 9.2. The Euler–Poincaré argument is standard; we reconstructed the
  details.
-/

open Module TensorProduct ExteriorAlgebra

noncomputable section

namespace Module.End

variable {K H M : Type*} [Field K] [AddCommGroup H] [Module K H] [AddCommGroup M] [Module K M]
  (T : H →ₗ[K] Module.End K M) {ι : Type*} (b : Basis ι K M) (w : ι → Dual K H)

/-- The coordinates of `T a m` in a basis of weight vectors. -/
lemma repr_apply_of_mem_weightSpaceOf (hb : ∀ i, b i ∈ weightSpaceOf T (w i)) (a : H) (m : M)
    (i : ι) : b.repr (T a m) i = w i a * b.repr m i := by
  have : (Finsupp.lapply i ∘ₗ b.repr.toLinearMap ∘ₗ T a) =
      w i a • (Finsupp.lapply i ∘ₗ b.repr.toLinearMap) := by
    refine b.ext fun j ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      mem_weightSpaceOf.mp (hb j) a, map_smul, Basis.repr_self, Finsupp.lapply_apply,
      LinearMap.smul_apply, smul_eq_mul]
    by_cases hij : j = i
    · subst hij; rfl
    · simp [hij]
  exact LinearMap.congr_fun this m

/-- If `M` has a basis of weight vectors, each weight space is spanned by the basis vectors of
that weight. -/
theorem weightSpaceOf_eq_span_image (hb : ∀ i, b i ∈ weightSpaceOf T (w i)) (μ : Dual K H) :
    weightSpaceOf T μ = Submodule.span K (b '' {i | w i = μ}) := by
  refine le_antisymm (fun m hm ↦ ?_) (Submodule.span_le.mpr ?_)
  · rw [b.mem_span_image]
    intro i hi
    refine LinearMap.ext fun a ↦ ?_
    have h1 := repr_apply_of_mem_weightSpaceOf T b w hb a m i
    rw [mem_weightSpaceOf.mp hm a, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    exact (mul_right_cancel₀ (Finsupp.mem_support_iff.mp hi) h1).symm
  · rintro _ ⟨i, hi, rfl⟩
    rw [← Set.mem_ofPred_eq.mp hi]
    exact hb i

end Module.End

namespace LieModule.ChevalleyEilenberg.DerivAction

variable {K H L M : Type*} [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M]
  {I J : Type*} [LinearOrder I] (bL : Basis I K L) (bM : Basis J K M)

local notation "E" => ExteriorAlgebra K L ⊗[K] M

/-! ### A basis of weight vectors of `⋀L ⊗ M` -/

/-- The basis `x_S ⊗ m_j` of `⋀L ⊗ M`, `x_S = x_{i₁} ∧ ⋯ ∧ x_{i_k}` for `S = {i₁ < ⋯ < i_k}`. -/
def chainBasis : Basis (Finset I × J) K E := bL.ExteriorAlgebra.tensorProduct bM

lemma chainBasis_apply (t : Finset I × J) :
    chainBasis bL bM t = bL.ExteriorAlgebra t.1 ⊗ₜ bM t.2 :=
  Basis.tensorProduct_apply' _ _ t

lemma basis_exteriorAlgebra_eq (S : Finset I) :
    bL.ExteriorAlgebra S = ιMulti K S.card (bL ∘ S.orderEmbOfFin rfl) := by
  rw [ExteriorAlgebra.basis_apply]
  rfl

lemma basis_exteriorAlgebra_mem (S : Finset I) : bL.ExteriorAlgebra S ∈ ⋀[K]^S.card L := by
  rw [basis_exteriorAlgebra_eq]
  exact ιMulti_range K S.card ⟨_, rfl⟩

lemma chainBasis_mem_chainsIn (t : Finset I × J) : chainBasis bL bM t ∈ chainsIn K L M t.1.card :=
  chainBasis_apply bL bM t ▸ tmul_mem_chainsIn (basis_exteriorAlgebra_mem bL t.1) _

variable (γ : I → Dual K H) (ν : J → Dual K H)

/-- The weight `γ S + ν j` of the basis vector `x_S ⊗ m_j`. -/
def chainWt (t : Finset I × J) : Dual K H := ∑ i ∈ t.1, γ i + ν t.2

omit [LinearOrder I] in
lemma chainWt_apply (t : Finset I × J) : chainWt γ ν t = ∑ i ∈ t.1, γ i + ν t.2 := rfl

variable [LieRingModule L M] {ρ : DerivAction K H L M} {γ ν}

lemma ιMulti_tmul_mem_chainWeightSpace {n : ℕ} (f : Fin n → L) (g : Fin n → Dual K H)
    (hf : ∀ i, f i ∈ Module.End.weightSpaceOf ρ.D (g i)) {m : M} {ν₀ : Dual K H}
    (hm : m ∈ Module.End.weightSpaceOf ρ.φ ν₀) :
    ιMulti K n f ⊗ₜ m ∈ ρ.chainWeightSpace (∑ i, g i + ν₀) := by
  induction n with
  | zero => simpa using ρ.one_tmul_mem_chainWeightSpace hm
  | succ n ih =>
    rw [ιMulti_succ_apply, ← wedge_tmul, Fin.sum_univ_succ, add_assoc]
    exact ρ.wedge_mem_chainWeightSpace (hf 0)
      (ih (Matrix.vecTail f) (Matrix.vecTail g) fun i ↦ hf i.succ)

lemma chainBasis_mem_chainWeightSpace (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
    (hbM : ∀ j, bM j ∈ Module.End.weightSpaceOf ρ.φ (ν j)) (t : Finset I × J) :
    chainBasis bL bM t ∈ ρ.chainWeightSpace (chainWt γ ν t) := by
  rw [chainBasis_apply, basis_exteriorAlgebra_eq, chainWt]
  have := ιMulti_tmul_mem_chainWeightSpace (ρ := ρ) (bL ∘ t.1.orderEmbOfFin rfl)
    (γ ∘ t.1.orderEmbOfFin rfl) (fun i ↦ hbL _) (hbM t.2)
  convert this using 2
  conv_lhs => rw [← Finset.image_orderEmbOfFin_univ t.1 rfl]
  rw [Finset.sum_image fun _ _ _ _ h ↦ (t.1.orderEmbOfFin rfl).injective h]
  rfl

/-- The weight spaces of `⋀L ⊗ M` are spanned by the basis vectors of the corresponding weight. -/
theorem chainWeightSpace_eq_span (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
    (hbM : ∀ j, bM j ∈ Module.End.weightSpaceOf ρ.φ (ν j)) (μ : Dual K H) :
    ρ.chainWeightSpace μ = Submodule.span K (chainBasis bL bM '' {t | chainWt γ ν t = μ}) :=
  Module.End.weightSpaceOf_eq_span_image ρ.θ (chainBasis bL bM) (chainWt γ ν)
    (chainBasis_mem_chainWeightSpace bL bM hbL hbM) μ

omit [LieRingModule L M] in
/-- The chains of degree `k` are spanned by the basis vectors of degree `k`. -/
theorem chainsIn_eq_span (k : ℕ) :
    chainsIn K L M k = Submodule.span K (chainBasis bL bM '' {t | t.1.card = k}) := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rintro _ ⟨u, rfl⟩
    induction u with
    | add u u' hu hu' => rw [map_add]; exact add_mem hu hu'
    | tmul ω m =>
      rw [incl_tmul]
      have hω : (ω : ExteriorAlgebra K L) ∈
          Submodule.span K (bL.ExteriorAlgebra '' {S | S.card = k}) := by
        have h1 : ω ∈ Submodule.span K (Set.range (bL.exteriorPower k)) :=
          (bL.exteriorPower k).mem_span ω
        have h2 := Submodule.mem_map_of_mem (f := (⋀[K]^k L).subtype) h1
        rw [Submodule.map_span, ← Set.range_comp] at h2
        refine Submodule.span_mono ?_ h2
        rintro _ ⟨s, rfl⟩
        refine ⟨s.val, s.prop, ?_⟩
        rw [Function.comp_apply, Submodule.subtype_apply, ← basis_eq_coe_basis]
      have hm : m ∈ Submodule.span K (Set.range bM) := bM.mem_span m
      generalize (ω : ExteriorAlgebra K L) = ω' at hω ⊢
      induction hω using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨S, hS, rfl⟩ := hx
        induction hm using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨j, rfl⟩ := hy
          exact Submodule.subset_span ⟨(S, j), hS, chainBasis_apply bL bM (S, j)⟩
        | zero => simp
        | add y y' _ _ hy hy' => rw [tmul_add]; exact add_mem hy hy'
        | smul r y _ hy => rw [tmul_smul]; exact Submodule.smul_mem _ r hy
      | zero => simp
      | add x x' _ _ hx hx' => rw [add_tmul]; exact add_mem hx hx'
      | smul r x _ hx => rw [← smul_tmul']; exact Submodule.smul_mem _ r hx
  · rintro _ ⟨t, ht, rfl⟩
    exact (Set.mem_ofPred_eq.mp ht) ▸ chainBasis_mem_chainsIn bL bM t

/-- `C_k(L, M)_μ` is spanned by the basis vectors of degree `k` and weight `μ`. -/
theorem chainsIn_inf_chainWeightSpace_eq_span
    (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
    (hbM : ∀ j, bM j ∈ Module.End.weightSpaceOf ρ.φ (ν j)) (k : ℕ) (μ : Dual K H) :
    chainsIn K L M k ⊓ ρ.chainWeightSpace μ =
      Submodule.span K (chainBasis bL bM '' {t | t.1.card = k ∧ chainWt γ ν t = μ}) := by
  ext c
  rw [Submodule.mem_inf, chainsIn_eq_span bL bM, chainWeightSpace_eq_span bL bM hbL hbM,
    Basis.mem_span_image, Basis.mem_span_image, Basis.mem_span_image, ← Set.subset_inter_iff]
  rfl

/-! ### Dimensions and the Euler characteristic of the chains -/

section Dimension

variable (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
  (hbM : ∀ j, bM j ∈ Module.End.weightSpaceOf ρ.φ (ν j))
  {μ : Dual K H} {s : Finset (Finset I × J)} (hs : ∀ t, chainWt γ ν t = μ ↔ t ∈ s)

include hbL hbM hs in
lemma chainsIn_inf_chainWeightSpace_eq_span_finset (k : ℕ) :
    chainsIn K L M k ⊓ ρ.chainWeightSpace μ =
      Submodule.span K (Set.range fun t : s.filter (fun t ↦ t.1.card = k) ↦
        chainBasis bL bM t) := by
  rw [chainsIn_inf_chainWeightSpace_eq_span bL bM hbL hbM]
  congr 1
  ext c
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Subtype.exists, Finset.mem_filter,
    ← hs]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, ⟨h2, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h2, h1⟩, rfl⟩
    exact ⟨t, ⟨h1, h2⟩, rfl⟩

include hbL hbM hs in
lemma finiteDimensional_chainsIn_inf_chainWeightSpace (k : ℕ) :
    FiniteDimensional K ↥(chainsIn K L M k ⊓ ρ.chainWeightSpace μ) := by
  rw [chainsIn_inf_chainWeightSpace_eq_span_finset bL bM hbL hbM hs k]
  exact FiniteDimensional.span_of_finite K (Set.finite_range _)

include hbL hbM hs in
/-- `dim C_k(L, M)_μ = #{(S, j) | |S| = k, γ S + ν j = μ}`. -/
theorem finrank_chainsIn_inf_chainWeightSpace (k : ℕ) :
    finrank K ↥(chainsIn K L M k ⊓ ρ.chainWeightSpace μ) =
      (s.filter fun t ↦ t.1.card = k).card := by
  have hli : LinearIndependent K fun t : s.filter (fun t ↦ t.1.card = k) ↦ chainBasis bL bM t :=
    (chainBasis bL bM).linearIndependent.comp _ Subtype.val_injective
  rw [chainsIn_inf_chainWeightSpace_eq_span_finset bL bM hbL hbM hs k, finrank_span_eq_card hli,
    Fintype.card_coe]

include hbL hbM hs in
/-- **The Euler characteristic of the weight-`μ` chains**:
`∑_k (-1)^k dim C_k(L, M)_μ = ∑_{γ S + ν j = μ} (-1)^{|S|}`. -/
theorem sum_neg_one_pow_finrank_chains {N : ℕ} (hN : ∀ t ∈ s, t.1.card ≤ N) :
    ∑ k ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ k * finrank K ↥(chainsIn K L M k ⊓ ρ.chainWeightSpace μ) =
      ∑ t ∈ s, (-1 : ℤ) ^ t.1.card := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun t : Finset I × J ↦ t.1.card)
    (t := Finset.range (N + 1)) fun t ht ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (hN t ht))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [finrank_chainsIn_inf_chainWeightSpace bL bM hbL hbM hs k, Finset.sum_congr rfl
    fun t ht ↦ by rw [(Finset.mem_filter.mp ht).2], Finset.sum_const, nsmul_eq_mul, mul_comm]

end Dimension

/-! ### The Euler–Poincaré principle -/

section Homology

variable [LieModule K L M] (hbL : ∀ i, bL i ∈ Module.End.weightSpaceOf ρ.D (γ i))
  (hbM : ∀ j, bM j ∈ Module.End.weightSpaceOf ρ.φ (ν j))

include hbL in
omit [LieModule K L M] [LinearOrder I] in
/-- `L` is the sum of its weight spaces if it has a basis of weight vectors. -/
lemma iSup_weightSpaceOf_D : ⨆ γ', Module.End.weightSpaceOf ρ.D γ' = ⊤ :=
  eq_top_iff.mpr fun y _ ↦ Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (γ i) (hbL i)) (bL.mem_span y)

include hbM in
omit [LieModule K L M] [LinearOrder I] in
/-- `M` is the sum of its weight spaces if it has a basis of weight vectors. -/
lemma iSup_weightSpaceOf_φ : ⨆ ν', Module.End.weightSpaceOf ρ.φ ν' = ⊤ :=
  eq_top_iff.mpr fun m _ ↦ Submodule.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (ν j) (hbM j)) (bM.mem_span m)

include hbL hbM in
omit [LinearOrder I] in
/-- The weight-`μ` boundaries are the boundaries of the weight-`μ` chains:
`B_k ∩ (⋀L ⊗ M)_μ = d(C_{k+1}(L, M)_μ)`. -/
lemma boundaries_inf_chainWeightSpace (k : ℕ) (μ : Dual K H) :
    boundaries K L M k ⊓ ρ.chainWeightSpace μ =
      (chainsIn K L M (k + 1) ⊓ ρ.chainWeightSpace μ).map (diff K L M) := by
  apply le_antisymm
  · rintro b ⟨hb, hbμ⟩
    have hdec := ρ.iSup_inf_chainWeightSpace (iSup_weightSpaceOf_D bL hbL)
      (iSup_weightSpaceOf_φ bM hbM) (chainsIn K L M (k + 1)) fun a _ hc ↦ ρ.θ_mem_chainsIn a hc
    have hb' : b ∈ ⨆ ν', (chainsIn K L M (k + 1) ⊓ ρ.chainWeightSpace ν').map (diff K L M) := by
      rw [← Submodule.map_iSup, hdec]
      exact hb
    refine Module.End.mem_of_mem_iSup_of_le ρ.θ _ (fun ν' ↦ ?_) hbμ hb'
    rintro _ ⟨c, ⟨-, hc⟩, rfl⟩
    exact ρ.diff_mem_chainWeightSpace hc
  · rintro _ ⟨c, ⟨hc, hcμ⟩, rfl⟩
    exact ⟨⟨c, hc, rfl⟩, ρ.diff_mem_chainWeightSpace hcμ⟩

include hbL hbM in
omit [LinearOrder I] in
/-- `dim C_{k+1}(L, M)_μ = dim (Z_{k+1})_μ + dim (B_k)_μ`. -/
lemma finrank_chainsIn_succ (k : ℕ) (μ : Dual K H)
    [FiniteDimensional K ↥(chainsIn K L M (k + 1) ⊓ ρ.chainWeightSpace μ)] :
    finrank K ↥(chainsIn K L M (k + 1) ⊓ ρ.chainWeightSpace μ) =
      finrank K ↥(cycles K L M (k + 1) ⊓ ρ.chainWeightSpace μ) +
        finrank K ↥(boundaries K L M k ⊓ ρ.chainWeightSpace μ) := by
  set C := chainsIn K L M (k + 1) ⊓ ρ.chainWeightSpace μ
  -- an additive group structure on `C` compatible with its additive monoid structure
  let _ : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
  have := LinearMap.finrank_range_add_finrank_ker (LinearMap.domRestrict (diff K L M) C)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
    ← boundaries_inf_chainWeightSpace bL bM hbL hbM] at this
  have hC : C ⊓ LinearMap.ker (diff K L M) = cycles K L M (k + 1) ⊓ ρ.chainWeightSpace μ := by
    rw [cycles, inf_right_comm]
  rw [← this, hC, add_comm]

variable {μ : Dual K H} {s : Finset (Finset I × J)} (hs : ∀ t, chainWt γ ν t = μ ↔ t ∈ s)

include hbL hbM hs in
/-- **The Euler–Poincaré principle** for the weight-`μ` part of the Chevalley–Eilenberg complex:
`∑_k (-1)^k dim H_k(L, M)_μ = ∑_k (-1)^k dim C_k(L, M)_μ = ∑_{γ S + ν j = μ} (-1)^{|S|}`. -/
theorem sum_neg_one_pow_finrank_homology {N : ℕ} (hN : ∀ t ∈ s, t.1.card ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * finrank K (ρ.homologyWeightSpace k μ) =
      ∑ t ∈ s, (-1 : ℤ) ^ t.1.card := by
  rw [← sum_neg_one_pow_finrank_chains bL bM hbL hbM hs hN]
  have hfin := finiteDimensional_chainsIn_inf_chainWeightSpace (ρ := ρ) bL bM hbL hbM hs
  have hZ : ∀ k, FiniteDimensional K ↥(cycles K L M k ⊓ ρ.chainWeightSpace μ) := fun k ↦
    Submodule.finiteDimensional_of_le (inf_le_inf_right _ inf_le_left :
      cycles K L M k ⊓ ρ.chainWeightSpace μ ≤ chainsIn K L M k ⊓ ρ.chainWeightSpace μ)
  have hzh : ∀ k, (finrank K (ρ.homologyWeightSpace k μ) : ℤ) +
      finrank K ↥(boundaries K L M k ⊓ ρ.chainWeightSpace μ) =
        finrank K ↥(cycles K L M k ⊓ ρ.chainWeightSpace μ) := fun k ↦ by
    rw [← Nat.cast_add, ρ.finrank_homologyWeightSpace_add k μ]
  have hc0 : finrank K ↥(chainsIn K L M 0 ⊓ ρ.chainWeightSpace μ) =
      finrank K ↥(cycles K L M 0 ⊓ ρ.chainWeightSpace μ) := by
    rw [cycles_zero]
  have hcs : ∀ k, (finrank K ↥(chainsIn K L M (k + 1) ⊓ ρ.chainWeightSpace μ) : ℤ) =
      finrank K ↥(cycles K L M (k + 1) ⊓ ρ.chainWeightSpace μ) +
        finrank K ↥(boundaries K L M k ⊓ ρ.chainWeightSpace μ) := fun k ↦ by
    rw [← Nat.cast_add, finrank_chainsIn_succ bL bM hbL hbM k μ]
  have hbN : finrank K ↥(boundaries K L M N ⊓ ρ.chainWeightSpace μ) = 0 := by
    have h0 : finrank K ↥(chainsIn K L M (N + 1) ⊓ ρ.chainWeightSpace μ) = 0 := by
      rw [finrank_chainsIn_inf_chainWeightSpace bL bM hbL hbM hs, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      exact fun t ht h ↦ by have := hN t ht; omega
    rw [boundaries_inf_chainWeightSpace bL bM hbL hbM]
    exact Nat.eq_zero_of_le_zero (h0 ▸ Submodule.finrank_map_le _ _)
  have key : ∀ n, ∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ k * finrank K ↥(chainsIn K L M k ⊓ ρ.chainWeightSpace μ) =
        ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * finrank K (ρ.homologyWeightSpace k μ) +
          (-1) ^ n * finrank K ↥(boundaries K L M n ⊓ ρ.chainWeightSpace μ) := by
    intro n
    induction n with
    | zero => simp [hc0, ← hzh]
    | succ n ih =>
      rw [Finset.sum_range_succ _ (n + 1), ih, Finset.sum_range_succ _ (n + 1), hcs, ← hzh,
        pow_succ]
      ring
  rw [key N, hbN]
  simp

end Homology

end LieModule.ChevalleyEilenberg.DerivAction
