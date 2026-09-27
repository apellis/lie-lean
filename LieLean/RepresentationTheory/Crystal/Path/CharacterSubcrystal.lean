/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Decomposition

/-!
# Characters of arbitrary path crystals

Let `A` be a generalized Cartan matrix with a realization over a conditionally complete ordered
field (i.e. over `ℝ`). Let `C` be a set of Littelmann paths which is stable under all root
operators, whose weights lie in finitely many cones `Λ - Q₊`, and in which every weight occurs
only finitely often (`Matrix.Realization.IsAdmissiblePathSet`); for instance any union of
connected components of `B(λ) * B(μ)` (see
`LieLean.RepresentationTheory.Crystal.Path.Decomposition`). We prove Littelmann's character
formula in this generality:

  `ch C = ∑_{π ∈ C highest weight} ch L(π(1))`

for symmetrizable `A` (`Matrix.Realization.setCharacter_eq_hsum`); the highest weight paths are
those with all `eᵢ π = 0`, i.e. the paths in the dominant chamber (all `hᵢ > -1`), and their
endpoints are dominant integral. For any generalized Cartan matrix we prove the generalized
Brauer–Klimyk formula `Matrix.Realization.coeffAt_weylAltSum_mul_setCharacter`, of which this is
the case `ν = 0`. This generalizes `Matrix.Realization.pathCharacter_eq_character` (`C = B(λ)`,
whose only highest weight path is `π_λ`) and gives another proof of the Littlewood–Richardson rule
(`C = B(λ) * B(μ)`).

In particular the character of a connected component of `B(λ) * B(μ)` is the sum of the
characters `ch L(ν)` over its highest weight elements; Littelmann's isomorphism theorem (not
proved here) says that there is exactly one.

## Proof

The proof is that of `Matrix.Realization.coeffAt_weylAltSum_mul_pathCharacter`, which uses only
that `B(λ)` is stable under the root operators and has finite weight multiplicities in a cone:
the weight multiplicities of a seminormal crystal are `W`-invariant (Kashiwara's action `Sᵢ`,
`Matrix.Realization.card_wt_weylGroup_of_isSeminormal`), and Littelmann's cancelling involution
(`LittelmannPath.exists_reflectAfter_hitIndex`) stays in the connected component. (Our
write-up.)

## Main definitions

* `Matrix.Realization.IsAdmissiblePathSet`: the hypotheses on `C`.
* `Matrix.Realization.setCharacter`: the character `∑_{π ∈ C} e^{π(1)} ∈ ℰ`.
* `Matrix.Realization.hwFamily`: the summable family `π ↦ ch L(π(1))` over the highest weight
  paths `π ∈ C`.

## Main results

* `Matrix.Realization.card_wt_weylGroup_of_isSeminormal`: weight multiplicities of seminormal
  crystals are `W`-invariant.
* `Matrix.Realization.coeffAt_weylAltSum_mul_setCharacter`: the generalized Brauer–Klimyk
  formula for `C`.
* `Matrix.Realization.setCharacter_eq_hsum`: **Littelmann's character formula for arbitrary path
  crystals**, `ch C = ∑_{π ∈ C highest weight} ch L(π(1))` (symmetrizable `A`).
* `Matrix.Realization.isAdmissiblePathSet_range_concatHom`,
  `Matrix.Realization.isAdmissiblePathSet_component_concat`: `B(λ) * B(μ)` and its connected
  components are admissible; hence `Matrix.Realization.setCharacter_component_concat_eq_hsum`:
  the character of a connected component of `B(λ) ⊗ B(μ)` is the sum of the `ch L(ν)` over its
  highest weight elements.

## References

* [Lit95] P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math.
  **142** (1995), 499–525.
* [Lit94] P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. **116** (1994), 329–346.
-/

open Module Set HahnSeries

/-! ### Highest weight paths -/

namespace LittelmannPath

variable {ι X : Type*} [AddCommGroup X] {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [FloorRing 𝕜]
  {D : CartanDatum ι X} {V : Type*} [AddCommGroup V] [Module 𝕜 V] {S : D.PathSpace 𝕜 V}

/-- A path is a highest weight element of the path crystal iff no `hᵢ` reaches `-1`. -/
theorem hitSet_neg_one_eq_empty_iff [Finite ι] (η : LittelmannPath S) :
    η.hitSet (fun _ ↦ -1) = ∅ ↔ (crystal S).IsHighestWeight η := by
  rw [hitSet_eq_empty_iff]
  refine forall_congr' fun j ↦ ?_
  rw [crystal_e, e_eq_none_iff, ε, show (-1 - -1 : ℤ) = 0 by norm_num, WithBot.coe_le_coe,
    Int.floor_le_iff]
  constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

end LittelmannPath

namespace Matrix.Realization

open CharacterRing KacMoodyAlgebra LittelmannPath WeightOrd

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [ConditionallyCompleteLinearOrder K]
  [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] [FloorRing K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} (hA : A.IsGeneralizedCartan)

omit [DecidableEq ι] in
/-- The endpoint of a highest weight path is dominant integral. -/
theorem isDominantIntegral_wt_of_isHighestWeight {η : LittelmannPath (P.pathSpace hA)}
    (h : (crystal (P.pathSpace hA)).IsHighestWeight η) :
    P.IsDominantIntegral (η.wt : Dual K H) := by
  intro j
  have hm : -1 < η.minPairing j := e_eq_none_iff.mp (h j)
  have h1 := η.minPairing_le_pairing_one j
  rw [pairing_one] at h1
  set n := (P.cartanDatum hA).coroot j η.wt
  have hn : (0 : ℤ) ≤ n := by
    have : (-1 : K) < n := hm.trans_le h1
    have : (-1 : ℤ) < n := by exact_mod_cast this
    omega
  refine ⟨n.toNat, ?_⟩
  rw [← coroot_cartanDatum_cast, ← Int.cast_natCast, Int.toNat_of_nonneg hn]

/-! ### `W`-invariance of weight multiplicities -/

section WeylInvariance

omit [DecidableEq ι] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] in
lemma card_wt_reflection_of_isSeminormal {B : Type*} (C : Crystal (P.cartanDatum hA) B)
    (hC : C.IsSeminormal) (i : ι) (μ : Dual K H) :
    Nat.card {b // (C.wt b : Dual K H) = P.reflection hA i μ} =
      Nat.card {b // (C.wt b : Dual K H) = μ} := by
  by_cases hμ : μ ∈ P.integralWeights
  · lift μ to P.integralWeights using hμ
    rw [← coe_reflection_cartanDatum,
      Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Subtype.coe_inj),
      Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ Subtype.coe_inj), hC.card_wt_reflection]
  · have h₁ : IsEmpty {b // (C.wt b : Dual K H) = μ} :=
      ⟨fun ⟨b, hb⟩ ↦ hμ (hb ▸ (C.wt b).2)⟩
    have h₂ : IsEmpty {b // (C.wt b : Dual K H) = P.reflection hA i μ} := by
      refine ⟨fun ⟨b, hb⟩ ↦ hμ ?_⟩
      rw [← P.reflection_reflection hA i μ, ← hb, ← coe_reflection_cartanDatum]
      exact ((P.cartanDatum hA).reflection i (C.wt b)).2
    simp [Nat.card_of_isEmpty]

omit [DecidableEq ι] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] in
/-- The weight multiplicities of a seminormal crystal over the Cartan datum of a realization are
invariant under the Weyl group (possibly infinite multiplicities being counted as `0`); a
bijection is given by Kashiwara's action of the simple reflections ([Kas] §7 (check)). -/
theorem card_wt_weylGroup_of_isSeminormal {B : Type*} (C : Crystal (P.cartanDatum hA) B)
    (hC : C.IsSeminormal) {w : Dual K H ≃ₗ[K] Dual K H} (hw : w ∈ P.weylGroup hA)
    (μ : Dual K H) :
    Nat.card {b // (C.wt b : Dual K H) = w μ} = Nat.card {b // (C.wt b : Dual K H) = μ} := by
  refine P.weylGroup_induction hA (p := fun w ↦ ∀ μ, Nat.card {b //
    (C.wt b : Dual K H) = w μ} = Nat.card {b // (C.wt b : Dual K H) = μ})
    (fun _ ↦ rfl) (fun i w ih μ ↦ ?_) hw μ
  rw [LinearEquiv.mul_apply, card_wt_reflection_of_isSeminormal hA C hC, ih]

end WeylInvariance

/-! ### Admissible sets of paths -/

variable (P) in
/-- The hypotheses under which the character of a set `C` of paths is defined and computed: `C`
is stable under all root operators, its weights lie in finitely many cones `Λ - Q₊`, and every
weight occurs only finitely often. -/
structure IsAdmissiblePathSet (C : Set (LittelmannPath (P.pathSpace hA))) : Prop where
  isStable : (crystal (P.pathSpace hA)).IsStable C
  exists_finset : ∃ t : Finset (Dual K H), ∀ b ∈ C, ∃ Λ ∈ t, ∃ k : ι → ℤ, 0 ≤ k ∧
    (b.wt : Dual K H) = Λ - P.rootOf k
  finite_fibre : ∀ x : Dual K H, {b ∈ C | (b.wt : Dual K H) = x}.Finite

omit [DecidableEq ι] in
/-- `B(λ)` is admissible. -/
theorem isAdmissiblePathSet_pathCrystal {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ) :
    IsAdmissiblePathSet P hA
      (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component where
  isStable := isStable_component _
  exists_finset := ⟨{Λ}, fun b hb ↦ ⟨Λ, Finset.mem_singleton_self _,
    exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ ⟨b, hb⟩⟩⟩
  finite_fibre x := ((finite_fibre hA hΛ x).image Subtype.val).subset fun b ⟨hb, hbx⟩ ↦
    ⟨⟨b, hb⟩, hbx, rfl⟩

variable {hA} {C : Set (LittelmannPath (P.pathSpace hA))} (hC : IsAdmissiblePathSet P hA C)
include hC

section Fibres

/-- The crystal structure on an admissible set of paths. -/
noncomputable abbrev setCrystal : Crystal (P.cartanDatum hA) C := Crystal.restrict hC.isStable

omit [DecidableEq ι] in
lemma isSeminormal_setCrystal : (setCrystal hC).IsSeminormal :=
  (isSeminormal_crystal _).restrict _

omit hC in
/-- The multiplicity `#{π ∈ C | π(1) = x}`. -/
noncomputable abbrev setMult (C : Set (LittelmannPath (P.pathSpace hA))) (x : Dual K H) : ℕ :=
  Nat.card {b : C // (b.1.wt : Dual K H) = x}

omit [DecidableEq ι] in
lemma finite_setFibre (x : Dual K H) : {b : C | (b.1.wt : Dual K H) = x}.Finite :=
  ((hC.finite_fibre x).preimage Subtype.val_injective.injOn).subset fun b hb ↦ ⟨b.2, hb⟩

omit [DecidableEq ι] in
/-- Weight multiplicities of `C` are `W`-invariant. -/
lemma setMult_apply (w : P.weylGroup hA) (x : Dual K H) :
    setMult C (w.1 x) = setMult C x :=
  card_wt_weylGroup_of_isSeminormal hA (setCrystal hC) (isSeminormal_setCrystal hC) w.2 x

omit [DecidableEq ι] in
/-- For each `μ` and each regular dominant integral `ρ'`, only finitely many `w ∈ W` have
`μ - wρ'` a weight of `C`. -/
lemma finite_setOf_setMult_ne_zero {ρ' : Dual K H}
    (hρ' : ∀ i, ∃ n : ℕ, ρ' (P.coroot i) = n + 1) (μ : Dual K H) :
    {w : P.weylGroup hA | setMult C (μ - w.1 ρ') ≠ 0}.Finite := by
  classical
  obtain ⟨t, ht⟩ := hC.exists_finset
  have hρ : P.IsDominantIntegral ρ' := fun i ↦ by
    obtain ⟨n, hn⟩ := hρ' i
    exact ⟨n + 1, by rw [hn]; push_cast; ring⟩
  have key : ∀ w : P.weylGroup hA, setMult C (μ - w.1 ρ') ≠ 0 →
      ∃ Λ ∈ t, ∃ k k' : ι → ℤ, 0 ≤ k ∧ 0 ≤ k' ∧ ρ' - w.1 ρ' = P.rootOf k ∧
        Λ + ρ' - μ = P.rootOf (k + k') := by
    intro w hw
    obtain ⟨⟨b, hb⟩⟩ : Nonempty {b : C // (b.1.wt : Dual K H) = μ - w.1 ρ'} := by
      by_contra h
      have := not_nonempty_iff.mp h
      exact hw Nat.card_of_isEmpty
    obtain ⟨k, hk, hwk⟩ := P.exists_sub_apply_eq_rootOf hA hρ w
    obtain ⟨Λ, hΛ, k', hk', hbk⟩ := ht b.1 b.2
    refine ⟨Λ, hΛ, k, k', hk, hk', hwk, ?_⟩
    rw [map_add, ← hwk, show P.rootOf k' = Λ - (μ - w.1 ρ') by rw [← hb, hbk]; abel]
    abel
  refine (t.finite_toSet.biUnion fun Λ _ ↦ (?_ : {w : P.weylGroup hA | ∃ k k' : ι → ℤ,
    0 ≤ k ∧ 0 ≤ k' ∧ ρ' - w.1 ρ' = P.rootOf k ∧ Λ + ρ' - μ = P.rootOf (k + k')}.Finite)).subset
    fun w hw ↦ ?_
  · by_cases hne : ∃ k₀ k₀' : ι → ℤ, 0 ≤ k₀ ∧ 0 ≤ k₀' ∧ Λ + ρ' - μ = P.rootOf (k₀ + k₀')
    · obtain ⟨k₀, k₀', hk₀, hk₀', hμ₀⟩ := hne
      refine (((Set.finite_Icc (0 : ι → ℤ) (k₀ + k₀')).image fun k ↦ ρ' - P.rootOf k).preimage
        (P.apply_injective_of_regular hA hρ').injOn).subset fun w ⟨k, k', hk, hk', hwk, hμ⟩ ↦ ?_
      have hkk : k + k' = k₀ + k₀' := P.rootOf_injective (hμ.symm.trans hμ₀)
      refine ⟨k, ⟨hk, fun j ↦ ?_⟩, by simp only; rw [← hwk]; abel⟩
      have := congr_fun hkk j
      have := hk' j
      have := hk₀ j
      have := hk₀' j
      simp only [Pi.add_apply, Pi.zero_apply] at *
      omega
    · refine Set.finite_empty.subset fun w ⟨k, k', hk, hk', _, hμ⟩ ↦ hne ⟨k, k', hk, hk', hμ⟩
  · obtain ⟨Λ, hΛ, k, k', hk, hk', hwk, hμ⟩ := key w hw
    exact Set.mem_biUnion (x := Λ) hΛ ⟨k, k', hk, hk', hwk, hμ⟩

omit [DecidableEq ι] in
/-- For regular dominant integral `ρ'`, only finitely many pairs `(w, π) ∈ W × C` have
`w(π(1) + ρ') = κ`. -/
lemma finite_setOf_apply_wt_add_eq_set {ρ' : Dual K H}
    (hρ' : ∀ i, ∃ n : ℕ, ρ' (P.coroot i) = n + 1) (κ : Dual K H) :
    {p : P.weylGroup hA × C | p.1.1 ((p.2.1.wt : Dual K H) + ρ') = κ}.Finite := by
  refine ((finite_setOf_setMult_ne_zero hC hρ' κ).biUnion fun w _ ↦
    (Set.finite_singleton w).prod (finite_setFibre hC ((w⁻¹).1 κ - ρ'))).subset ?_
  rintro ⟨w, b⟩ (hp : w.1 _ = κ)
  have hb : (b.1.wt : Dual K H) = (w⁻¹).1 κ - ρ' := by
    rw [← hp, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
    exact (add_sub_cancel_right _ _).symm
  refine Set.mem_biUnion (x := w) ?_ ⟨rfl, hb⟩
  change setMult C (κ - w.1 ρ') ≠ 0
  rw [show κ - w.1 ρ' = w.1 (b.1.wt : Dual K H) by rw [← hp, map_add, add_sub_cancel_right],
    setMult_apply hC]
  exact (Nat.card_pos_iff.mpr ⟨⟨⟨b, rfl⟩⟩, (finite_setFibre hC _).to_subtype⟩).ne'

end Fibres

/-! ### Littelmann's involution on `W × C` -/

section Involution

variable {ν : Dual K H} (hν : P.IsDominantIntegral ν)

omit [DecidableEq ι] in
/-- Littelmann's involution on pairs `(w, π) ∈ W × C` with `π` not `ν`-dominant
(`Matrix.Realization.reflectPair` for `C = B(λ)`). -/
noncomputable def setReflectPair (p : P.weylGroup hA × C)
    (h : (p.2.1.hitSet (shiftLevel hA hν)).Nonempty) : P.weylGroup hA × C :=
  (p.1 * (P.coxeterSystem hA).simple (hitIndex h),
    ⟨(exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h).choose,
      Crystal.closure_subset hC.isStable (singleton_subset_iff.mpr p.2.2)
        (exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h).choose_spec.2.1⟩)

lemma setReflectPair_spec (p : P.weylGroup hA × C)
    (h : (p.2.1.hitSet (shiftLevel hA hν)).Nonempty) :
    ∃ h' : ((setReflectPair hC hν p h).2.1.hitSet (shiftLevel hA hν)).Nonempty,
      hitIndex h' = hitIndex h ∧
      ((setReflectPair hC hν p h).2.1.wt : Dual K H) + (ν + P.rho) =
        P.reflection hA (hitIndex h) ((p.2.1.wt : Dual K H) + (ν + P.rho)) ∧
      setReflectPair hC hν (setReflectPair hC hν p h) h' = p := by
  obtain ⟨-, -, h', hi, hwt, hback⟩ :=
    (exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h).choose_spec
  refine ⟨h', hi, ?_, ?_⟩
  · change ((exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h).choose.wt : Dual K H) +
      (ν + P.rho) = _
    rw [hwt, AddSubgroup.coe_add, coe_reflection_cartanDatum, AddSubgroup.coe_zsmul,
      coe_root_cartanDatum, ← Int.cast_smul_eq_zsmul K, shiftLevel_cast, map_add, map_add,
      reflection_apply P hA _ P.rho, rho_coroot, one_smul, reflection_apply P hA _ ν]
    module
  · have hc := (exists_reflectAfter_hitIndex (shiftLevel_le hA hν) h').choose_spec.1
    have hc2 : reflectAfter (setReflectPair hC hν p h).2.1 (hitIndex h')
        (shiftLevel hA hν (hitIndex h')) = some p.2.1 := by
      rw [hi]
      exact hback
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change p.1 * _ * (P.coxeterSystem hA).simple (hitIndex h') = p.1
      rw [hi, CoxeterSystem.simple_mul_simple_cancel_right]
    · exact Option.some_injective _ (hc.symm.trans hc2)

end Involution

/-! ### The character formula -/

section Formula

/-- The character `ch C = ∑_{π ∈ C} e^{π(1)} ∈ ℰ` of an admissible set of paths. -/
noncomputable def setCharacter : P.CharacterRing ℤ :=
  Crystal.formalCharacterOfCones (setCrystal hC) (by
    obtain ⟨t, ht⟩ := hC.exists_finset
    exact ⟨t, fun b ↦ ht b.1 b.2⟩)

omit [DecidableEq ι] in
lemma coeffAt_setCharacter (μ : Dual K H) : (setCharacter hC).coeffAt μ = setMult C μ :=
  Crystal.coeffAt_formalCharacterOfCones _ _ μ

open Classical in
/-- **Littelmann's generalized Brauer–Klimyk formula for admissible sets of paths** ([Lit95] §9
(check); our write-up): for dominant integral `ν`, the coefficient of `e^κ` in
`(∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(ν + ρ)}) · ch C` is the signed count of pairs `(w, π) ∈ W × C` with
`π` `ν`-dominant (no `hⱼ` reaches `-1 - ⟨ν, αⱼ^∨⟩`) and `w(ν + π(1) + ρ) = κ`. The proof is that
of `Matrix.Realization.coeffAt_weylAltSum_mul_pathCharacter`. -/
theorem coeffAt_weylAltSum_mul_setCharacter {ν : Dual K H} (hν : P.IsDominantIntegral ν)
    (κ : Dual K H) :
    (weylAltSum P hA (IrreducibleModule.isDominantIntegral_add_rho hν) *
      setCharacter hC).coeffAt κ =
    ∑ᶠ p : P.weylGroup hA × C,
      if p.2.1.hitSet (shiftLevel hA hν) = ∅ ∧
          p.1.1 ((p.2.1.wt : Dual K H) + (ν + P.rho)) = κ then
        (-1) ^ (P.coxeterSystem hA).length p.1 else 0 := by
  classical
  set ε : P.weylGroup hA → ℤ := fun w ↦ (-1) ^ (P.coxeterSystem hA).length w with hε
  set ρ' := ν + P.rho with hρ'
  have hreg : ∀ i, ∃ n : ℕ, ρ' (P.coroot i) = n + 1 := fun i ↦ by
    obtain ⟨n, hn⟩ := hν i
    exact ⟨n, by rw [hρ', LinearMap.add_apply, hn, rho_coroot]⟩
  have hinj := P.apply_injective_of_regular hA hreg
  have hF := finite_setOf_setMult_ne_zero hC hreg κ
  set T := hF.toFinset with hT
  -- the coefficient as a sum over `w`
  have step1 : (weylAltSum P hA (IrreducibleModule.isDominantIntegral_add_rho hν) *
      setCharacter hC).coeffAt κ = ∑ w ∈ T, ε w * (setMult C (κ - w.1 ρ') : ℤ) := by
    rw [CharacterRing.coeff_mul, finsum_eq_sum_of_support_subset _ (s := T.image fun w ↦ w.1 ρ') ?_,
      Finset.sum_image fun w _ w' _ h ↦ hinj h]
    · refine Finset.sum_congr rfl fun w _ ↦ ?_
      simp only [weylAltSum, coeff_ofFun]
      rw [finsum_eq_single _ w fun w' hw' ↦
        ite_eq_right fun h ↦ hw' (hinj h), ite_eq_left rfl, coeffAt_setCharacter]
    · intro μ hμ
      rw [Function.mem_support] at hμ
      obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hμ
      simp only [weylAltSum, coeff_ofFun] at h₁
      obtain ⟨w, hw⟩ : ∃ w : P.weylGroup hA, w.1 ρ' = μ := by
        by_contra! h
        exact h₁ (finsum_eq_zero_of_forall_eq_zero fun w ↦ ite_eq_right (h w))
      rw [Finset.coe_image]
      refine ⟨w, ?_, hw⟩
      rw [hT, Set.Finite.coe_toFinset]
      rw [coeffAt_setCharacter, ← hw] at h₂
      exact_mod_cast h₂
  -- the fibres and the set of pairs
  have hinv : ∀ (w : P.weylGroup hA) (x : Dual K H), w.1 x = κ ↔ x = (w⁻¹).1 κ := by
    intro w x
    constructor
    · rintro rfl
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
      rfl
    · rintro rfl
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
      rfl
  have hfin := fun w : P.weylGroup hA ↦ finite_setFibre hC ((w⁻¹).1 κ - ρ')
  have hκw : ∀ w : P.weylGroup hA, κ - w.1 ρ' = w.1 ((w⁻¹).1 κ - ρ') := fun w ↦ by
    rw [map_sub, ((hinv w _).mpr rfl)]
  have hcard : ∀ w : P.weylGroup hA,
      setMult C (κ - w.1 ρ') = (hfin w).toFinset.card := fun w ↦ by
    rw [hκw, setMult_apply hC, ← Nat.card_eq_card_finite_toFinset]
    rfl
  set Fall := T.biUnion fun w ↦ (hfin w).toFinset
  set S := (T ×ˢ Fall).filter fun p ↦ p.1.1 ((p.2.1.wt : Dual K H) + ρ') = κ with hS
  have hmemfib : ∀ (w : P.weylGroup hA) (b : C),
      b ∈ (hfin w).toFinset ↔ w.1 ((b.1.wt : Dual K H) + ρ') = κ := fun w b ↦ by
    rw [Set.Finite.mem_toFinset, hinv, Set.mem_ofPred_eq, eq_sub_iff_add_eq]
  have hmemT : ∀ (w : P.weylGroup hA) (b : C),
      w.1 ((b.1.wt : Dual K H) + ρ') = κ → w ∈ T := fun w b hb ↦ by
    rw [hT, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hcard]
    exact Finset.card_ne_zero.mpr ⟨b, (hmemfib w b).mpr hb⟩
  have hmemS : ∀ p, p ∈ S ↔ p.1.1 ((p.2.1.wt : Dual K H) + ρ') = κ := by
    rintro ⟨w, b⟩
    simp only [hS, Finset.mem_filter, Finset.mem_product, Fall, Finset.mem_biUnion]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨⟨hmemT w b h, w, hmemT w b h, (hmemfib w b).mpr h⟩, h⟩⟩
  have step2 : ∑ w ∈ T, ε w * (setMult C (κ - w.1 ρ') : ℤ) = ∑ p ∈ S, ε p.1 := by
    rw [hS, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hfil : Fall.filter (fun b ↦ w.1 ((b.1.wt : Dual K H) + ρ') = κ) =
        (hfin w).toFinset := by
      ext b
      simp only [Finset.mem_filter, Fall, Finset.mem_biUnion]
      exact ⟨fun h ↦ (hmemfib w b).mpr h.2, fun h ↦ ⟨⟨w, hw, h⟩, (hmemfib w b).mp h⟩⟩
    rw [← Finset.sum_filter]
    dsimp only
    rw [hfil, Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]
  rw [step1, step2, ← Finset.sum_filter_add_sum_filter_not S
    (fun p ↦ p.2.1.hitSet (shiftLevel hA hν) = ∅)]
  -- the pairs which are not `ν`-dominant cancel
  have hne : ∀ p ∈ S.filter (fun p ↦ ¬p.2.1.hitSet (shiftLevel hA hν) = ∅),
      (p.2.1.hitSet (shiftLevel hA hν)).Nonempty := fun p hp ↦
    Set.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hp).2
  have hzero : ∑ p ∈ S.filter (fun p ↦ ¬p.2.1.hitSet (shiftLevel hA hν) = ∅), ε p.1 = 0 := by
    refine Finset.sum_involution (fun p hp ↦ setReflectPair hC hν p (hne p hp))
      (fun p hp ↦ ?_) (fun p hp _ ↦ ?_) (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · change ε p.1 + ε (p.1 * _) = 0
      rw [hε]
      simp only [neg_one_pow_length_mul_simple]
      ring
    · intro h
      have h1 := congrArg Prod.fst h
      change p.1 * _ = p.1 at h1
      have h2 := (P.coxeterSystem hA).length_simple (hitIndex (hne p hp))
      rw [mul_eq_left.mp h1, CoxeterSystem.length_one] at h2
      exact absurd h2 (by norm_num)
    · obtain ⟨h', -, hwt, -⟩ := setReflectPair_spec hC hν p (hne p hp)
      refine Finset.mem_filter.mpr ⟨(hmemS _).mpr ?_, Set.nonempty_iff_ne_empty.mp h'⟩
      change (p.1 * _).1 _ = κ
      rw [coe_mul_simple_apply, hwt, reflection_reflection]
      exact (hmemS p).mp (Finset.mem_filter.mp hp).1
    · obtain ⟨h', -, -, hback⟩ := setReflectPair_spec hC hν p (hne p hp)
      exact hback
  rw [hzero, add_zero, finsum_eq_sum_of_support_subset _ (s := S) fun p hp ↦ ?_,
    Finset.sum_filter]
  · refine Finset.sum_congr rfl fun p hp ↦ ?_
    by_cases hd : p.2.1.hitSet (shiftLevel hA hν) = ∅
    · rw [ite_eq_left hd, ite_eq_left (And.intro hd ((hmemS p).mp hp))]
    · rw [ite_eq_right hd, ite_eq_right fun h : _ ∧ _ ↦ hd h.1]
  · rw [Function.mem_support] at hp
    exact (hmemS p).mpr (by by_contra h; exact hp (ite_eq_right fun h' : _ ∧ _ ↦ h h'.2))

open Classical in
/-- The summable family `π ↦ ch L(π(1))` over the highest weight paths `π ∈ C` (and `π ↦ 0` for
the other paths). -/
noncomputable def hwFamily : SummableFamily P.WeightOrd ℤ C where
  toFun b := if (crystal (P.pathSpace hA)).IsHighestWeight b.1 then
    (IrreducibleModule.isCategoryO P (b.1.wt : Dual K H)).character else 0
  isPWO_iUnion_support' := by
    obtain ⟨t, ht⟩ := hC.exists_finset
    refine (isPWO_iff P).mpr ⟨t, fun ν hν ↦ ?_⟩
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hν
    rw [HahnSeries.mem_support] at hb
    by_cases hd : (crystal (P.pathSpace hA)).IsHighestWeight b.1
    · rw [ite_eq_left hd] at hb
      have h2 : (IrreducibleModule.isCategoryO P (b.1.wt : Dual K H)).character.coeffAt
          (ofWeightOrd P ν) ≠ 0 := hb
      rw [IsCategoryO.coeffAt_character, Nat.cast_ne_zero] at h2
      obtain ⟨l, hl, hνμ⟩ := IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h2
      obtain ⟨Λ, hΛ, k, hk, hbk⟩ := ht b.1 b.2
      refine ⟨Λ, hΛ, k + l, add_nonneg hk hl, ?_⟩
      rw [hνμ, hbk, map_add]
      abel
    · rw [ite_eq_right hd, HahnSeries.coeff_zero] at hb
      exact absurd rfl hb
  finite_co_support' g := by
    obtain ⟨t, ht⟩ := hC.exists_finset
    refine (t.finite_toSet.biUnion fun Λ _ ↦
      (finite_setOf_mem_cone_and_mem_cone P Λ (ofWeightOrd P g)).biUnion fun μ _ ↦
        finite_setFibre hC μ).subset fun b hb ↦ ?_
    rw [Set.mem_ofPred_eq] at hb
    by_cases hd : (crystal (P.pathSpace hA)).IsHighestWeight b.1
    · rw [ite_eq_left hd] at hb
      have h2 : (IrreducibleModule.isCategoryO P (b.1.wt : Dual K H)).character.coeffAt
          (ofWeightOrd P g) ≠ 0 := hb
      rw [IsCategoryO.coeffAt_character, Nat.cast_ne_zero] at h2
      obtain ⟨Λ, hΛ, k, hk, hbk⟩ := ht b.1 b.2
      exact Set.mem_biUnion (x := Λ) hΛ (Set.mem_biUnion (x := (b.1.wt : Dual K H))
        ⟨⟨k, hk, hbk⟩, IrreducibleModule.mem_cone_of_finrank_weightSpace_ne_zero h2⟩ rfl)
    · rw [ite_eq_right hd, HahnSeries.coeff_zero] at hb
      exact absurd rfl hb

open Classical in
lemma hwFamily_apply (b : C) :
    hwFamily hC b = if (crystal (P.pathSpace hA)).IsHighestWeight b.1 then
      (IrreducibleModule.isCategoryO P (b.1.wt : Dual K H)).character else 0 :=
  rfl

/-- **Littelmann's character formula for arbitrary path crystals** ([Lit95] §9 (check); our
write-up): for a symmetrizable generalized Cartan matrix and an admissible set `C` of paths (e.g.
a union of connected components of `B(λ) * B(μ)`),
`ch C = ∑_{π ∈ C highest weight} ch L(π(1))` in `ℰ`, the sum over the paths `π ∈ C` with all
`eᵢ π = 0` (whose endpoints are dominant integral,
`Matrix.Realization.isDominantIntegral_wt_of_isHighestWeight`). The proof multiplies by the unit
`e^ρ R` and combines the case `ν = 0` of the Brauer–Klimyk formula
`Matrix.Realization.coeffAt_weylAltSum_mul_setCharacter` with the Weyl–Kac formula. -/
theorem setCharacter_eq_hsum [FiniteDimensional K H] (hS : A.IsSymmetrizable) :
    setCharacter hC = (hwFamily hC).hsum := by
  classical
  have hR : IsUnit (denominator P) := by
    have := VermaModule.denominator_mul_character P 0
    rw [exp_zero] at this
    exact IsUnit.of_mul_eq_one _ this
  have hρ : IsUnit (exp P ℤ P.rho) :=
    IsUnit.of_mul_eq_one (exp P ℤ (-P.rho)) (by rw [← exp_add, add_neg_cancel, exp_zero])
  have h0 := IrreducibleModule.isDominantIntegral_zero (P := P)
  have hl : shiftLevel hA h0 = fun _ ↦ -1 := funext (shiftLevel_zero hA)
  have hcongr : ∀ (μ₀ μ₁ : Dual K H) (_ : μ₀ = μ₁) (h₀ : ∀ i, ∃ n : ℕ, μ₀ (P.coroot i) = n)
      (h₁ : ∀ i, ∃ n : ℕ, μ₁ (P.coroot i) = n), weylAltSum P hA h₀ = weylAltSum P hA h₁ := by
    rintro μ₀ μ₁ rfl h₀ h₁
    rfl
  have hreg : ∀ i, ∃ n : ℕ, (0 + P.rho) (P.coroot i) = n + 1 := fun i ↦
    ⟨0, by rw [zero_add, rho_coroot]; simp⟩
  apply (hρ.mul hR).mul_left_cancel
  rw [IrreducibleModule.exp_rho_mul_denominator hA hS, ← SummableFamily.hsum_smul,
    hcongr _ _ (zero_add P.rho).symm (IrreducibleModule.isDominantIntegral_rho (P := P))
      (IrreducibleModule.isDominantIntegral_add_rho h0)]
  ext κ
  rw [coeffAt_weylAltSum_mul_setCharacter hC h0 κ, coeffAt, SummableFamily.coeff_hsum]
  have hterm : ∀ b : C,
      ((weylAltSum P hA (IrreducibleModule.isDominantIntegral_add_rho h0) • hwFamily hC)
        b).coeff (toWeightOrd P κ) =
        ∑ᶠ w : P.weylGroup hA, if b.1.hitSet (shiftLevel hA h0) = ∅ ∧
          w.1 ((b.1.wt : Dual K H) + (0 + P.rho)) = κ then
            (-1) ^ (P.coxeterSystem hA).length w else 0 := by
    intro b
    rw [← hcongr _ _ (zero_add P.rho).symm (IrreducibleModule.isDominantIntegral_rho (P := P))
      (IrreducibleModule.isDominantIntegral_add_rho h0),
      ← IrreducibleModule.exp_rho_mul_denominator hA hS, SummableFamily.smul_apply,
      HahnSeries.of_symm_smul_of_eq_mul, hwFamily_apply]
    by_cases hd : (crystal (P.pathSpace hA)).IsHighestWeight b.1
    · rw [ite_eq_left hd, IrreducibleModule.exp_rho_mul_denominator_mul_character hA hS
        (isDominantIntegral_wt_of_isHighestWeight hA hd)]
      change (weylAltSum P hA _).coeffAt κ = _
      rw [coeffAt_weylAltSum]
      refine finsum_congr fun w ↦ ?_
      rw [zero_add]
      simp only [hl, (hitSet_neg_one_eq_empty_iff b.1).mpr hd, true_and]
    · rw [ite_eq_right hd, mul_zero, HahnSeries.coeff_zero]
      refine (finsum_eq_zero_of_forall_eq_zero fun w ↦ ite_eq_right fun h ↦ hd ?_).symm
      rw [← hitSet_neg_one_eq_empty_iff, ← hl]
      exact h.1
  rw [finsum_congr hterm, ← finsum_comp_equiv (Equiv.prodComm C (P.weylGroup hA)),
    finsum_curry]
  · rfl
  · refine ((finite_setOf_apply_wt_add_eq_set hC hreg κ).preimage
      (Equiv.prodComm _ _).injective.injOn).subset fun q hq ↦ ?_
    rw [Function.mem_support] at hq
    by_contra h
    exact hq (ite_eq_right fun h' ↦ h h'.2)

end Formula

/-! ### Components of `B(λ) * B(μ)` -/

section Tensor

omit hC

omit [DecidableEq ι] in
/-- A stable subset of an admissible set of paths is admissible. -/
theorem IsAdmissiblePathSet.mono {C' : Set (LittelmannPath (P.pathSpace hA))}
    (hC : IsAdmissiblePathSet P hA C) (hC' : (crystal (P.pathSpace hA)).IsStable C')
    (h : C' ⊆ C) : IsAdmissiblePathSet P hA C' where
  isStable := hC'
  exists_finset := by
    obtain ⟨t, ht⟩ := hC.exists_finset
    exact ⟨t, fun b hb ↦ ht b (h hb)⟩
  finite_fibre x := (hC.finite_fibre x).subset fun b hb ↦ ⟨h hb.1, hb.2⟩

variable (hA) {Λ₁ Λ₂ : Dual K H} (hΛ₁ : P.IsDominantIntegral Λ₁) (hΛ₂ : P.IsDominantIntegral Λ₂)

omit [DecidableEq ι] in
/-- The set `B(λ) * B(μ)` of concatenations is admissible. -/
theorem isAdmissiblePathSet_range_concatHom :
    IsAdmissiblePathSet P hA (Set.range (concatHom hA hΛ₁ hΛ₂)) where
  isStable := (concatHom hA hΛ₁ hΛ₂).isStable_range
  exists_finset := ⟨{Λ₁ + Λ₂}, by
    rintro _ ⟨p, rfl⟩
    obtain ⟨k₁, hk₁, h₁⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ₁ p.1
    obtain ⟨k₂, hk₂, h₂⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ₂ p.2
    refine ⟨Λ₁ + Λ₂, Finset.mem_singleton_self _, k₁ + k₂, add_nonneg hk₁ hk₂, ?_⟩
    change ((p.1.1.wt + p.2.1.wt : P.integralWeights) : Dual K H) = _
    rw [AddSubgroup.coe_add]
    change (p.1.1.wt : Dual K H) = _ at h₁
    change (p.2.1.wt : Dual K H) = _ at h₂
    rw [h₁, h₂, map_add]
    abel⟩
  finite_fibre x := by
    set U := {ν | ν ∈ cone P (Λ₁ + Λ₂) ∧ x ∈ cone P ν}
    have hU : U.Finite := finite_setOf_mem_cone_and_mem_cone P (Λ₁ + Λ₂) x
    refine ((hU.biUnion fun ν _ ↦ (finite_fibre hA hΛ₁ (ν - Λ₂)).prod
      (finite_fibre hA hΛ₂ (x - (ν - Λ₂)))).image (concatHom hA hΛ₁ hΛ₂)).subset ?_
    rintro _ ⟨⟨p, rfl⟩, hx⟩
    change ((p.1.1.wt + p.2.1.wt : P.integralWeights) : Dual K H) = x at hx
    rw [AddSubgroup.coe_add] at hx
    obtain ⟨k₁, hk₁, h₁⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ₁ p.1
    obtain ⟨k₂, hk₂, h₂⟩ := exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ₂ p.2
    change (p.1.1.wt : Dual K H) = _ at h₁
    change (p.2.1.wt : Dual K H) = _ at h₂
    refine ⟨p, Set.mem_biUnion (x := (p.1.1.wt : Dual K H) + Λ₂)
      ⟨⟨k₁, hk₁, by rw [h₁]; abel⟩, ⟨k₂, hk₂, by rw [← hx, h₂]; abel⟩⟩ ⟨?_, ?_⟩, rfl⟩
    · change (p.1.1.wt : Dual K H) = _
      abel
    · change (p.2.1.wt : Dual K H) = _
      rw [← hx]
      abel

omit [DecidableEq ι] in
/-- A connected component of `B(λ) * B(μ)` is admissible. -/
theorem isAdmissiblePathSet_component_concat
    (p : (straightLine (P.pathSpace hA) ⟨Λ₁, hΛ₁.mem_integralWeights⟩).component ×
      (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component) :
    IsAdmissiblePathSet P hA (p.1.1.concat p.2.1).component :=
  (isAdmissiblePathSet_range_concatHom hA hΛ₁ hΛ₂).mono (isStable_component _)
    (Crystal.closure_subset (concatHom hA hΛ₁ hΛ₂).isStable_range
      (Set.singleton_subset_iff.mpr ⟨p, rfl⟩))

/-- **The character of a connected component of `B(λ) ⊗ B(μ)`**: for symmetrizable `A`, the
character of the connected component `B(η₁ * η₂)` of `B(λ) * B(μ) ≅ B(λ) ⊗ B(μ)` is
`∑ ch L(π(1))` over its highest weight elements `π` (which are of the form `π_λ * η` with `η`
`λ`-dominant, `Matrix.Realization.isHighestWeight_tensorPathCrystal_iff`). Littelmann's
isomorphism theorem (not proved here) says that there is exactly one. -/
theorem setCharacter_component_concat_eq_hsum [FiniteDimensional K H] (hS : A.IsSymmetrizable)
    (p : (straightLine (P.pathSpace hA) ⟨Λ₁, hΛ₁.mem_integralWeights⟩).component ×
      (straightLine (P.pathSpace hA) ⟨Λ₂, hΛ₂.mem_integralWeights⟩).component) :
    setCharacter (isAdmissiblePathSet_component_concat hA hΛ₁ hΛ₂ p) =
      (hwFamily (isAdmissiblePathSet_component_concat hA hΛ₁ hΛ₂ p)).hsum :=
  setCharacter_eq_hsum _ hS

end Tensor

end Matrix.Realization
