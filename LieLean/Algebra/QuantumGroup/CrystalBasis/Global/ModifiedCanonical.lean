/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorTransitionCanonical
import LieLean.Algebra.QuantumGroup.RootDatumHom
import LieLean.Algebra.QuantumGroup.Modified.Bar

/-!
# The elements `b ◇_ζ b''` of `U̇`

Over `ℚ(v)`, for `ζ ∈ X` and `b, b'' ∈ B`, Lusztig's element `b ◇_ζ b''` of `U̇` ([Lus] 25.2.1)
is the unique `u ∈ U̇1_ζ` with `u(ξ_{-λ} ⊗ η_{λ''}) = (b ◇ b'')_{λ,λ''}` in `ʷΛ_λ ⊗ Λ_{λ''}` for
all dominant `λ, λ''` with `λ'' - λ = ζ`, `b ∈ B(λ)` and `b'' ∈ B(λ'')`; moreover
`u(ξ_{-λ} ⊗ η_{λ''}) = 0` if `b ∉ B(λ)` or `b'' ∉ B(λ'')`. It lies in `𝒜U̇` and is fixed by
the bar involution of `U̇`.

## Main definitions

* `tensorIrrProj`: the projection `ʷM_λ ⊗ M_{λ''} → ʷΛ_λ ⊗ Λ_{λ''}`.
* `modTensorAct`: `u ↦ u(ξ_{-λ} ⊗ η_{λ''})`, `U̇ → ʷΛ_λ ⊗ Λ_{λ''}`.
* `modifiedCanonical`: the element `b ◇_ζ b''`.
* `Modified.columnEquiv`: the fixed-column comparison of [Lus] 23.2.5.
* `Modified.columnEquiv_mem_aForm_iff`, `Modified.aColumnEquiv`: its integral restriction.
* `Modified.columnCanonical`: transport from the free-coroot auxiliary datum, with no `hY`
  on the target; it lies in the specified column and integral form and is fixed by bar.

## Main results

* `existsUnique_modifiedCanonical`, `modTensorAct_modifiedCanonical`,
  `modifiedCanonical_mem_aForm`: [Lus] Thm. 25.2.1 (a).
* `modTensorAct_modifiedCanonical_eq_zero`: [Lus] Thm. 25.2.1 (b).
* `bar_modifiedCanonical`: [Lus] Thm. 25.2.1 (c), with `modTensorAct_bar`
  (`ū(ξ_{-λ} ⊗ η_{λ''}) = Ψ(u(ξ_{-λ} ⊗ η_{λ''}))`).
* `eq_zero_of_modTensorAct_eq_zero`: an element of `U̇1_ζ` acting by zero on
  `ξ_{-λ} ⊗ η_{λ''}` for all large `λ, λ''` with `λ'' - λ = ζ` is zero.
* `Modified.columnEquiv_leftActOne`, `Modified.columnEquiv_mul`: the column comparison is
  induced by the root-datum algebra map and intertwines its left action ([Lus] 23.2.5).

## Hypotheses

For the characterization in 25.2.1, Lusztig assumes the root datum `Y`-regular.
The characterization here assumes instead `hY`: for every `N`
there is a dominant `λ` with `⟨i, λ⟩ ≥ N` for all `i`. It follows from `Y`-regularity and is the
form in which the proof uses it. It cannot be dropped: in type affine `A₁` with `Y = X = ℤ²`,
`i ↦ (1, 0), (-1, 0)` and `i' ↦ (2, 0), (-2, 1)` (an `X`-regular root datum), every dominant `λ`
has `⟨i, λ⟩ = 0`, so `1_ζ` and `1_ζ + F_i 1_ζ` both satisfy (a) for `b = b'' = 1`. The global basis
of `Λ_λ` used here is the one constructed for `X`-regular root data (`R.IsXRegular`, where Lusztig
assumes `Y`-regular).

The column comparison has neither regularity hypothesis nor `hY`. It works over any field
at a non-root-of-unity parameter. It is the linear comparison needed for 25.2.2.
The integral restriction is `aColumnEquiv`. The construction `columnCanonical` transports the
canonical element from the free-coroot auxiliary datum, which preserves `IsXRegular` and has
arbitrarily large dominant weights. This is not the printed simply connected datum. Its use is
justified by the generalized column comparison, following the method of 25.2.2. Membership in
the column, integrality and bar invariance are proved; `ModifiedCanonicalBasis` proves that
these elements form rational and integral bases without target `hY`. `ModifiedCanonicalForm`
proves normalized form transport; `ModifiedCanonicalSigned` proves agreement with the old
construction under `hY`. The dominant-tensor characterization and its uniqueness retain `hY`;
`ModifiedCanonicalTransfer` proves (a), (b) for `columnCanonical` without `hY`, and derives `hY`
from `Y`-regularity.

## Implementation notes

Lusztig writes `(b ◇ b'')_{λ,λ''}` as `u(ξ_{-λ} ⊗ η_{λ''})` with `u` in a span of elements
`b₁⁺ b₂⁻ 1_ζ` of bounded degree and proves uniqueness with 23.3.8. Our route is our own: the
bifiltration `tensorDepth a b` of `ʷM_λ ⊗ M_{λ''}` by the degrees of the two factors is the image
of `triDepth a b ⊆ f ⊗ f` under `[y] ⊗ [x] ↦ y⁻x⁺(ξ ⊗ η)` (`exists_triAct_eq`, our form of
23.3.1 with degree control), and the projection to `ʷΛ_λ ⊗ Λ_{λ''}` is injective on
`tensorDepth n n` when `n ≤ ⟨i, λ⟩, ⟨i, λ''⟩` (`eq_zero_of_tensorIrrProj_eq_zero`, since `b ∈ B`
of degree `≤ ⟨i, λ⟩` lies in `B(λ)`). As in Lusztig's proof, the passage from large `λ, λ''` to
arbitrary ones is [Lus] 25.1.10 (`tensorTransition_tensorCanonical`).

For integrality (`modifiedCanonical_mem_aForm`), the element `y⁻x⁺(ξ ⊗ η)` above is chosen in
`ʷ𝒜M_λ ⊗_𝒜 𝒜M_{λ''}`, lifting the `𝒜`-coordinates of `(b ◇ b'')_{λ,λ''}` along `b ↦ b⁻η`, and
[Lus] 23.3.2 (a) (`leftActOne_mem_aForm_iff`) applies. Part (d) of 25.2.1 is in
`ModifiedCanonicalBasis.lean`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.8, 23.3, 24.3.2,
  25.1.10, 25.2.1.
-/

noncomputable section

namespace LieLean.QuantumGroup

open GrandLoop LusztigF TensorProduct Modified

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### Elements of `B` of small degree lie in `B(λ)` -/

section SmallDegree

omit [Finite I] [DecidableEq I] in
lemma NegativePart.proj_f_pow (i : I) (m : ℕ) (γ : I →₀ ℤ) (u : Um D 𝕧) :
    NegativePart.proj D 𝕧 γ ((NegativePart.f D 𝕧 i ^ m) u) =
      (NegativePart.f D 𝕧 i ^ m) (NegativePart.proj D 𝕧 (γ - Finsupp.single i (m : ℤ)) u) := by
  induction m generalizing γ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, NegativePart.proj_f, ih, Module.End.mul_apply,
      sub_sub, ← Finsupp.single_add]
    push_cast
    ring_nf

omit [Finite I] [DecidableEq I] in
lemma NegativePart.proj_eq_zero_of_not_nonneg {γ : I →₀ ℤ} (hγ : ¬ 0 ≤ γ) (u : Um D 𝕧) :
    NegativePart.proj D 𝕧 γ u = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [NegativePart.proj_mk]
  simp [zWeightProj, hγ]

variable (Λ : Dom R)

/-- An element `b ∈ B` with `tr |b| ≤ ⟨i, λ⟩` for all `i` lies in `B(λ)`. -/
theorem mem_canonicalBasisHW_of_degree_le {x : Um D 𝕧} (hx : x ∈ canonicalBasis D)
    {ν : I →₀ ℕ} (hxν : x ∈ Uw D 𝕧 ν) (hΛ : ∀ i, (ν.degree : ℤ) ≤ Λ.1 (R.coroot i)) :
    x ∈ canonicalBasisHW D Λ := by
  rw [mem_canonicalBasisHW_iff]
  refine ⟨hx, fun i hi ↦ ?_⟩
  have hne : x ≠ 0 := (linearIndependent_canonicalBasis D).ne_zero ⟨x, hx⟩
  set n := (Λ.1 (R.coroot i)).toNat + 1
  obtain ⟨y, hy⟩ := (mem_rightRange_iff D).1 hi
  have h1 := proj_of_mem_Uw (starU_mem_Uw hxν) (toZ ν)
  rw [ite_eq_left rfl, ← hy, NegativePart.proj_f_pow,
    NegativePart.proj_eq_zero_of_not_nonneg, map_zero] at h1
  · refine hne ?_
    rw [← starU_starU x, ← hy, ← h1, map_zero]
  · intro h
    have h2 := h i
    have h3 := Finsupp.le_degree i ν
    have h4 := hΛ i
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply, toZ_apply,
      Finsupp.single_eq_same] at h2
    omega

end SmallDegree

/-! ### `y ↦ y⁻η_λ` is injective in low degrees -/

section LowDegree

variable (Λ : Dom R) {N : ℕ} (hN : ∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i))
include hN

/-- If `N ≤ ⟨i, λ⟩` for all `i`, the image in `f` of an element of degree `< N` of `'f` lies in
the span of `B(λ)`. -/
lemma mk_mem_span_canonicalBasisHW {y : LusztigF 𝕂 I} (hy : y ∈ degSpan 𝕂 I N) :
    (Submodule.Quotient.mk y : Um D 𝕧) ∈ Submodule.span 𝕂 (canonicalBasisHW D Λ) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have hmem : (Submodule.Quotient.mk (monomial 𝕂 w) : Um D 𝕧) ∈ Uw D 𝕧 (wordWeight w) :=
      mk_mem_Uw (monomial_mem_weightSpace w)
    rw [← span_canonicalBasisAt] at hmem
    refine Submodule.span_mono (fun b hb ↦ ?_) hmem
    refine mem_canonicalBasisHW_of_degree_le Λ (Set.mem_iUnion.2 ⟨_, hb⟩)
      (span_canonicalBasisAt D (wordWeight w) ▸ Submodule.subset_span hb) fun i ↦ ?_
    have := hN i
    have hw' : w.length < N := hw
    rw [degree_wordWeight]
    omega
  | zero => exact zero_mem _
  | add y z _ _ hy hz => rw [Submodule.Quotient.mk_add]; exact add_mem hy hz
  | smul c y _ hy => rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ c hy

include hR in
/-- `y ↦ y⁻η_λ` is injective on the elements of degree `< N` of `f`, if `N ≤ ⟨i, λ⟩` for
all `i`. -/
theorem mk_eq_zero_of_evq_eq_zero {y : LusztigF 𝕂 I} (hy : y ∈ degSpan 𝕂 I N)
    (h : evq hvt Λ (Submodule.Quotient.mk y : Um D 𝕧) = 0) :
    (Submodule.Quotient.mk y : Um D 𝕧) = 0 := by
  have hdisj := (linearIndependent_canonicalBasis D).disjoint_span_image
    (s := Subtype.val ⁻¹' canonicalBasisHW D Λ)
    (t := Subtype.val ⁻¹' (canonicalBasis D \ canonicalBasisHW D Λ))
    (Set.disjoint_left.2 fun _ h₁ h₂ ↦ h₂.2 h₁)
  rw [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
    Set.inter_eq_self_of_subset_right (canonicalBasisHW_subset D Λ),
    Set.inter_eq_self_of_subset_right Set.sdiff_subset] at hdisj
  exact Submodule.disjoint_def.1 hdisj _ (mk_mem_span_canonicalBasisHW Λ hN hy)
    (mem_span_of_evq_eq_zero Λ hR h)

include hR in
/-- The projection `M_λ → Λ_λ` is injective on the `y⁻η` with `y` of degree `< N`, if
`N ≤ ⟨i, λ⟩` for all `i`. -/
theorem eq_zero_of_mkQ_eq_zero {p : VermaModule R 𝕧 Λ.1} (hp : p ∈ vermaDegSpan R 𝕧 Λ.1 N)
    (h : (VermaModule.maxSubmodule R 𝕧 Λ.1).mkQ p = 0) : p = 0 := by
  obtain ⟨y, hy, rfl⟩ := hp
  have h' : evq hvt Λ (Submodule.Quotient.mk y : Um D 𝕧) = 0 := h
  have h0 := mk_eq_zero_of_evq_eq_zero hR Λ hN hy h'
  rw [VermaModule.toVerma_eq_zero_iff hvn_ratFunc, ← mem_serreSubmodule]
  exact (Submodule.Quotient.mk_eq_zero _).1 h0

end LowDegree

/-! ### The bifiltration of `ʷM_λ ⊗ M_{λ''}` -/

section Depth

omit [Finite I] in
/-- `Eᵢ y⁻η` has degree `< tr |y|`, for `y` a monomial. -/
lemma E_smul_toVerma_monomial_mem_vermaDegSpan (Λ : Y →+ ℤ) (i : I) (w : List I) :
    E R 𝕧 i • VermaModule.toVerma R 𝕧 Λ (monomial 𝕂 w) ∈ vermaDegSpan R 𝕧 Λ w.length := by
  induction w with
  | nil =>
    rw [monomial_nil, VermaModule.toVerma_one, VermaModule.E_smul_hwv]
    exact zero_mem _
  | cons j w ih =>
    have hb : VermaModule.toVerma R 𝕧 Λ (monomial 𝕂 w) ∈ vermaDegSpan R 𝕧 Λ (w.length + 1) :=
      ⟨_, monomial_mem_degSpan (Nat.lt_succ_self _), rfl⟩
    rw [monomial_cons, ← F_smul_toVerma, ← mul_smul,
      ← sub_add_cancel (E R 𝕧 i * F R 𝕧 j) (F R 𝕧 j * E R 𝕧 i), add_smul, E_mul_F_sub,
      mul_smul, List.length_cons]
    refine add_mem ?_ (F_smul_mem_vermaDegSpan Λ j ih)
    split_ifs
    · rw [smul_assoc, sub_smul]
      exact Submodule.smul_mem _ _ (sub_mem (K_smul_mem_vermaDegSpan Λ _ hb)
        (K_smul_mem_vermaDegSpan Λ _ hb))
    · rw [zero_smul]
      exact zero_mem _

omit [Finite I] in
lemma E_smul_mem_vermaDegSpan (Λ : Y →+ ℤ) (i : I) {d : ℕ} {p : VermaModule R 𝕧 Λ}
    (hp : p ∈ vermaDegSpan R 𝕧 Λ d) : E R 𝕧 i • p ∈ vermaDegSpan R 𝕧 Λ d := by
  obtain ⟨y, hy, rfl⟩ := hp
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact vermaDegSpan_mono Λ (le_of_lt hw) (E_smul_toVerma_monomial_mem_vermaDegSpan Λ i w)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, smul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ c hy

variable (Λ Λ'' : Y →+ ℤ)

local notation "VT" =>
  TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ'')

local notation "mkT" =>
  TensorModule.mk (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ'')

local notation "tw" => ChevalleyTwist.toTwist R 𝕧 (VermaModule R 𝕧 Λ)

variable (R) in
/-- The span of the `ʷ(x⁻ξ) ⊗ y⁻η` with `x` of degree `< a` and `y` of degree `< b`, in
`ʷM_λ ⊗ M_{λ''}`. -/
def tensorDepth (a b : ℕ) : Submodule 𝕂 VT :=
  Submodule.map₂ ((TensorProduct.mk 𝕂 _ _).compr₂ (mkT).toLinearMap)
    ((vermaDegSpan R 𝕧 Λ a).map (tw).toLinearMap) (vermaDegSpan R 𝕧 Λ'' b)

variable {Λ Λ''}

omit [Finite I] in
lemma tmul_mem_tensorDepth {a b : ℕ} {p : VermaModule R 𝕧 Λ} {q : VermaModule R 𝕧 Λ''}
    (hp : p ∈ vermaDegSpan R 𝕧 Λ a) (hq : q ∈ vermaDegSpan R 𝕧 Λ'' b) :
    mkT (tw p ⊗ₜ[𝕂] q) ∈ tensorDepth R Λ Λ'' a b :=
  Submodule.apply_mem_map₂ _ ⟨p, hp, rfl⟩ hq

omit [Finite I] in
lemma tensorDepth_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    tensorDepth R Λ Λ'' a b ≤ tensorDepth R Λ Λ'' a' b' :=
  Submodule.map₂_le_map₂ (Submodule.map_mono (vermaDegSpan_mono Λ ha)) (vermaDegSpan_mono Λ'' hb)

omit [Finite I] in
lemma F_smul_twist_mem {a : ℕ} {p : VermaModule R 𝕧 Λ} (hp : p ∈ vermaDegSpan R 𝕧 Λ a)
    (i : I) : ∃ p' ∈ vermaDegSpan R 𝕧 Λ a, F R 𝕧 i • tw p = tw p' :=
  ⟨_, E_smul_mem_vermaDegSpan Λ i hp, by rw [ChevalleyTwist.smul_toTwist, chevalley_F]⟩

omit [Finite I] in
/-- `Fᵢ` raises the second degree by one. -/
lemma F_smul_mem_tensorDepth (i : I) {a b : ℕ} {z : VT} (hz : z ∈ tensorDepth R Λ Λ'' a b) :
    F R 𝕧 i • z ∈ tensorDepth R Λ Λ'' a (b + 1) := by
  have h : tensorDepth R Λ Λ'' a b ≤ (tensorDepth R Λ Λ'' a (b + 1)).comap
      (DistribSMul.toLinearMap 𝕂 _ (F R 𝕧 i)) := by
    refine Submodule.map₂_le.2 fun m hm q hq ↦ ?_
    obtain ⟨p, hp, rfl⟩ := hm
    obtain ⟨p', hp', e⟩ := F_smul_twist_mem hp i
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
      Submodule.mem_comap, DistribSMul.toLinearMap_apply]
    rw [TensorModule.F_smul_tmul, map_add, e]
    exact add_mem (tmul_mem_tensorDepth hp' (vermaDegSpan_mono Λ'' (Nat.le_succ b)
      (K_smul_mem_vermaDegSpan Λ'' _ hq))) (tmul_mem_tensorDepth hp
        (F_smul_mem_vermaDegSpan Λ'' i hq))
  exact h hz

omit [Finite I] in
lemma minusHom_monomial_smul_mem_tensorDepth (w : List I) {a b : ℕ} {z : VT}
    (hz : z ∈ tensorDepth R Λ Λ'' a b) :
    minusHom R 𝕧 (monomial 𝕂 w) • z ∈ tensorDepth R Λ Λ'' a (b + w.length) := by
  induction w with
  | nil => rw [monomial_nil, _root_.map_one, one_smul]; exact hz
  | cons i w ih =>
    rw [monomial_cons, _root_.map_mul, minusHom_θ, mul_smul, List.length_cons, ← add_assoc]
    exact F_smul_mem_tensorDepth i ih

omit [Finite I] in
lemma minusHom_smul_mem_tensorDepth {a b c : ℕ} {y : LusztigF 𝕂 I} (hy : y ∈ degSpan 𝕂 I c)
    {z : VT} (hz : z ∈ tensorDepth R Λ Λ'' a (b + 1)) :
    minusHom R 𝕧 y • z ∈ tensorDepth R Λ Λ'' a (b + c) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have hw' : w.length < c := hw
    exact tensorDepth_mono le_rfl (by omega) (minusHom_monomial_smul_mem_tensorDepth w hz)
  | zero => rw [map_zero, zero_smul]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [map_add, add_smul]; exact add_mem hy hy'
  | smul c y _ hy => rw [map_smul, smul_assoc]; exact Submodule.smul_mem _ c hy

end Depth

/-! ### `y⁻x⁺(ξ ⊗ η)` on the bifiltration -/

section TriAct

local notation "fQ" => LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧

variable (D) in
/-- The span of the `[y] ⊗ [x]` in `f ⊗ f` with `y` of degree `< b` and `x` of degree `< a`. -/
def triDepth (a b : ℕ) : Submodule 𝕂 (fQ ⊗[𝕂] fQ) :=
  Submodule.map₂ (TensorProduct.mk 𝕂 fQ fQ) ((degSpan 𝕂 I b).map (serreSubmodule D 𝕧).mkQ)
    ((degSpan 𝕂 I a).map (serreSubmodule D 𝕧).mkQ)

omit [Finite I] [DecidableEq I] in
lemma triDepth_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    triDepth D a b ≤ triDepth D a' b' :=
  Submodule.map₂_le_map₂ (Submodule.map_mono (degSpan_mono hb))
    (Submodule.map_mono (degSpan_mono ha))

omit [Finite I] [DecidableEq I] in
/-- Every element of `f ⊗ f` lies in some `triDepth D n n`. -/
lemma exists_mem_triDepth (z : fQ ⊗[𝕂] fQ) : ∃ n, z ∈ triDepth D n n := by
  induction z using TensorProduct.inductionOn with
  | tmul p q =>
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ p
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨d, hd⟩ := exists_mem_degSpan y
    obtain ⟨d', hd'⟩ := exists_mem_degSpan x
    exact ⟨max d d', Submodule.apply_mem_map₂ _
      ⟨y, degSpan_mono (le_max_left _ _) hd, rfl⟩ ⟨x, degSpan_mono (le_max_right _ _) hd', rfl⟩⟩
  | add z z' hz hz' =>
    obtain ⟨d, hd⟩ := hz
    obtain ⟨d', hd'⟩ := hz'
    exact ⟨max d d', add_mem (triDepth_mono (le_max_left _ _) (le_max_left _ _) hd)
      (triDepth_mono (le_max_right _ _) (le_max_right _ _) hd')⟩

variable (Λ Λ'' : Y →+ ℤ)

local notation "mkT" =>
  TensorModule.mk (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ)) (VermaModule R 𝕧 Λ'')

local notation "tw" => ChevalleyTwist.toTwist R 𝕧 (VermaModule R 𝕧 Λ)

omit [Finite I] in
lemma hwv_mem_vermaDegSpan : VermaModule.hwv R 𝕧 Λ'' ∈ vermaDegSpan R 𝕧 Λ'' 1 :=
  ⟨monomial 𝕂 [], monomial_mem_degSpan (by simp), by
    rw [monomial_nil, VermaModule.toVerma_one]⟩

omit [Finite I] in
/-- `x⁺(ξ ⊗ η) = ʷ(x⁻ξ) ⊗ η`. -/
lemma plusHom_smul_vermaTensorHwv (x : LusztigF 𝕂 I) :
    plusHom R 𝕧 x • vermaTensorHwv R 𝕧 Λ Λ'' =
      mkT (tw (VermaModule.toVerma R 𝕧 Λ x) ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ'') := by
  rw [vermaTensorHwv, plusHom_smul_tmul_hwv, ChevalleyTwist.smul_toTwist, chevalley_plusHom,
    VermaModule.toVerma_apply]

omit [Finite I] in
/-- `y⁻x⁺(ξ ⊗ η)` lies in `tensorDepth a b` for `[y] ⊗ [x] ∈ triDepth a b`. -/
lemma triAct_mem_tensorDepth {a b : ℕ} {z : fQ ⊗[𝕂] fQ} (hz : z ∈ triDepth D a b) :
    triAct R hvn_ratFunc Λ Λ'' z ∈ tensorDepth R Λ Λ'' a b := by
  have h : triDepth D a b ≤ (tensorDepth R Λ Λ'' a b).comap (triAct R hvn_ratFunc Λ Λ'') := by
    refine Submodule.map₂_le.2 fun p hp q hq ↦ ?_
    obtain ⟨y, hy, rfl⟩ := hp
    obtain ⟨x, hx, rfl⟩ := hq
    simp only [TensorProduct.mk_apply, Submodule.mem_comap, Submodule.mkQ_apply]
    change (minusHom R 𝕧 y * plusHom R 𝕧 x) • vermaTensorHwv R 𝕧 Λ Λ'' ∈ _
    rw [mul_smul, plusHom_smul_vermaTensorHwv]
    simpa using minusHom_smul_mem_tensorDepth (b := 0) hy
      (tmul_mem_tensorDepth ⟨x, hx, rfl⟩ (hwv_mem_vermaDegSpan Λ''))
  exact h hz

omit [Finite I] in
/-- `y⁻ (ʷp ⊗ η) = ʷp ⊗ y⁻η` modulo `tensorDepth a (length w)`, for `y = θ_w`. -/
lemma minusHom_monomial_smul_sub_mem_tensorDepth (w : List I) {a : ℕ} {p : VermaModule R 𝕧 Λ}
    (hp : p ∈ vermaDegSpan R 𝕧 Λ a) :
    minusHom R 𝕧 (monomial 𝕂 w) • mkT (tw p ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ'') -
      mkT (tw p ⊗ₜ[𝕂] VermaModule.toVerma R 𝕧 Λ'' (monomial 𝕂 w)) ∈
      tensorDepth R Λ Λ'' a w.length := by
  induction w with
  | nil =>
    rw [monomial_nil, _root_.map_one, one_smul, VermaModule.toVerma_one, sub_self]
    exact zero_mem _
  | cons i w ih =>
    set b := VermaModule.toVerma R 𝕧 Λ'' (monomial 𝕂 w)
    have hb : b ∈ vermaDegSpan R 𝕧 Λ'' (w.length + 1) :=
      ⟨_, monomial_mem_degSpan (Nat.lt_succ_self _), rfl⟩
    obtain ⟨p', hp', e'⟩ := F_smul_twist_mem hp i
    have e : minusHom R 𝕧 (monomial 𝕂 (i :: w)) •
          mkT (tw p ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ'') -
        mkT (tw p ⊗ₜ[𝕂] VermaModule.toVerma R 𝕧 Λ'' (monomial 𝕂 (i :: w))) =
        F R 𝕧 i • (minusHom R 𝕧 (monomial 𝕂 w) •
          mkT (tw p ⊗ₜ[𝕂] VermaModule.hwv R 𝕧 Λ'') - mkT (tw p ⊗ₜ[𝕂] b)) +
        mkT ((F R 𝕧 i • tw p) ⊗ₜ[𝕂] (K R 𝕧 (-ktilde R i) • b)) := by
      rw [smul_sub, TensorModule.F_smul_tmul, monomial_cons, _root_.map_mul, minusHom_θ,
        mul_smul, F_smul_toVerma, ← monomial_cons, map_add]
      abel
    rw [e, e', List.length_cons]
    exact add_mem (F_smul_mem_tensorDepth i ih)
      (tmul_mem_tensorDepth hp' (K_smul_mem_vermaDegSpan Λ'' _ hb))

omit [Finite I] in
lemma triEquiv_mk_tmul_mk (y x : LusztigF 𝕂 I) :
    triEquiv R hvn_ratFunc Λ Λ'' (Submodule.Quotient.mk y ⊗ₜ Submodule.Quotient.mk x) =
      mkT (tw (VermaModule.toVerma R 𝕧 Λ x) ⊗ₜ[𝕂] VermaModule.toVerma R 𝕧 Λ'' y) := by
  rw [triEquiv_tmul, ChevalleyTwist.smul_toTwist, chevalley_plusHom,
    VermaModule.equivSerreQuotient_mk]
  rfl

omit [Finite I] in
/-- `triAct - triEquiv` lowers the second degree. -/
lemma triAct_sub_triEquiv_mem_tensorDepth {a b : ℕ} {z : fQ ⊗[𝕂] fQ}
    (hz : z ∈ triDepth D a (b + 1)) :
    triAct R hvn_ratFunc Λ Λ'' z - triEquiv R hvn_ratFunc Λ Λ'' z ∈ tensorDepth R Λ Λ'' a b := by
  have h : triDepth D a (b + 1) ≤ (tensorDepth R Λ Λ'' a b).comap
      (triAct R hvn_ratFunc Λ Λ'' - (triEquiv R hvn_ratFunc Λ Λ'').toLinearMap) := by
    refine Submodule.map₂_le.2 fun p hp q hq ↦ ?_
    obtain ⟨y, hy, rfl⟩ := hp
    obtain ⟨x, hx, rfl⟩ := hq
    simp only [TensorProduct.mk_apply, Submodule.mem_comap, LinearMap.sub_apply,
      LinearEquiv.coe_coe, Submodule.mkQ_apply]
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      have hw' : w.length < b + 1 := hw
      rw [triEquiv_mk_tmul_mk]
      change (minusHom R 𝕧 (monomial 𝕂 w) * plusHom R 𝕧 x) • vermaTensorHwv R 𝕧 Λ Λ'' - _ ∈ _
      rw [mul_smul, plusHom_smul_vermaTensorHwv]
      exact tensorDepth_mono le_rfl (by omega)
        (minusHom_monomial_smul_sub_mem_tensorDepth Λ Λ'' w ⟨x, hx, rfl⟩)
    | zero => simp
    | add y y' _ _ hy hy' =>
      rw [Submodule.Quotient.mk_add, add_tmul, map_add, map_add, add_sub_add_comm]
      exact add_mem hy hy'
    | smul c y _ hy =>
      rw [Submodule.Quotient.mk_smul, ← smul_tmul', map_smul, map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hy
  exact h hz

omit [Finite I] in
lemma tensorDepth_le_map_triEquiv (a b : ℕ) :
    tensorDepth R Λ Λ'' a b ≤ (triDepth D a b).map (triEquiv R hvn_ratFunc Λ Λ'').toLinearMap := by
  refine Submodule.map₂_le.2 fun m hm q hq ↦ ?_
  obtain ⟨p, ⟨x, hx, rfl⟩, rfl⟩ := hm
  obtain ⟨y, hy, rfl⟩ := hq
  refine ⟨Submodule.Quotient.mk y ⊗ₜ Submodule.Quotient.mk x,
    Submodule.apply_mem_map₂ _ ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩, ?_⟩
  simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe]
  exact triEquiv_mk_tmul_mk Λ Λ'' y x

omit [Finite I] in
/-- Every element of `tensorDepth a b` is a `y⁻x⁺(ξ ⊗ η)` with `[y] ⊗ [x] ∈ triDepth a b` (our
form of [Lus] 23.3.1 (b) with control of the degrees). -/
theorem exists_triAct_eq (a b : ℕ) {m : TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ))
    (VermaModule R 𝕧 Λ'')} (hm : m ∈ tensorDepth R Λ Λ'' a b) :
    ∃ z ∈ triDepth D a b, triAct R hvn_ratFunc Λ Λ'' z = m := by
  induction b generalizing m with
  | zero =>
    have h0 : vermaDegSpan R 𝕧 Λ'' 0 = ⊥ := by
      rw [vermaDegSpan, degSpan_zero, Submodule.map_bot]
    rw [tensorDepth, h0, Submodule.map₂_bot_right, Submodule.mem_bot] at hm
    exact ⟨0, zero_mem _, by rw [map_zero, hm]⟩
  | succ b ih =>
    obtain ⟨z₀, hz₀, rfl⟩ := tensorDepth_le_map_triEquiv Λ Λ'' a (b + 1) hm
    obtain ⟨z₁, hz₁, e⟩ := ih (triAct_sub_triEquiv_mem_tensorDepth Λ Λ'' hz₀)
    refine ⟨z₀ - z₁, sub_mem hz₀ (triDepth_mono le_rfl (Nat.le_succ b) hz₁), ?_⟩
    rw [map_sub, e, LinearEquiv.coe_coe, sub_sub_cancel]

end TriAct

/-! ### The projection `ʷM_λ ⊗ M_{λ''} → ʷΛ_λ ⊗ Λ_{λ''}` -/

section Proj

variable (Λ Λ'' : Dom R)

set_option quotPrecheck false in
local notation "VT" =>
  TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ.1)) (VermaModule R 𝕧 Λ''.1)

/-- The projection `ʷM_λ ⊗ M_{λ''} → ʷΛ_λ ⊗ Λ_{λ''}`. -/
def tensorIrrProj : VT →ₗ[𝕂] TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ''.1 :=
  tensorMap (ChevalleyTwist.map (VermaModule.maxSubmodule R 𝕧 Λ.1).mkQ)
    (VermaModule.maxSubmodule R 𝕧 Λ''.1).mkQ ∘ₗ (TensorModule.mk _ _).symm.toLinearMap

omit [Finite I] in
lemma tensorIrrProj_mk_tmul (p : VermaModule R 𝕧 Λ.1) (q : VermaModule R 𝕧 Λ''.1) :
    tensorIrrProj Λ Λ'' (TensorModule.mk _ _ (ChevalleyTwist.toTwist R 𝕧 _ p ⊗ₜ[𝕂] q)) =
      ChevalleyTwist.toTwist R 𝕧 _ (Submodule.Quotient.mk p) ⊗ₜ[𝕂] Submodule.Quotient.mk q := by
  simp [tensorIrrProj]

omit [Finite I] in
/-- The projection is a homomorphism of `U`-modules. -/
lemma tensorIrrProj_smul (u : QuantumGroup R 𝕧) (z : VT) :
    tensorIrrProj Λ Λ'' (u • z) = TensorModule.act R 𝕧 _ _ u (tensorIrrProj Λ Λ'' z) := by
  obtain ⟨z, rfl⟩ := (TensorModule.mk _ _).surjective z
  rw [TensorModule.smul_mk]
  simp only [tensorIrrProj, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact (actPair_tensorMap _ _ _ _).symm

omit [Finite I] in
lemma tensorIrrProj_vermaTensorHwv :
    tensorIrrProj Λ Λ'' (vermaTensorHwv R 𝕧 Λ.1 Λ''.1) =
      ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
        IrreducibleModule.hwv R 𝕧 Λ''.1 :=
  tensorIrrProj_mk_tmul Λ Λ'' _ _

omit [Finite I] in
/-- `y⁻x⁺(ξ ⊗ η)` in `ʷΛ_λ ⊗ Λ_{λ''}`. -/
lemma tensorIrrProj_triAct (z : (LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧) ⊗[𝕂]
    (LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧)) :
    tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1 z) =
      TensorModule.act R 𝕧 _ _ (triMul R hvn_ratFunc z)
        (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
          IrreducibleModule.hwv R 𝕧 Λ''.1) := by
  rw [← tensorIrrProj_vermaTensorHwv, ← tensorIrrProj_smul]
  rfl

include hR in
/-- The projection is injective on `tensorDepth n n` if `n ≤ ⟨i, λ⟩` and `n ≤ ⟨i, λ''⟩` for
all `i`. -/
theorem eq_zero_of_tensorIrrProj_eq_zero {n : ℕ} (hΛ : ∀ i, (n : ℤ) ≤ Λ.1 (R.coroot i))
    (hΛ'' : ∀ i, (n : ℤ) ≤ Λ''.1 (R.coroot i)) {z : VT}
    (hz : z ∈ tensorDepth R Λ.1 Λ''.1 n n) (h : tensorIrrProj Λ Λ'' z = 0) : z = 0 := by
  set ι₁ := (ChevalleyTwist.toTwist R 𝕧 (VermaModule R 𝕧 Λ.1)).toLinearMap ∘ₗ
    (vermaDegSpan R 𝕧 Λ.1 n).subtype
  set ι₂ := (vermaDegSpan R 𝕧 Λ''.1 n).subtype
  have hle : tensorDepth R Λ.1 Λ''.1 n n ≤
      LinearMap.range ((TensorModule.mk _ _).toLinearMap ∘ₗ TensorProduct.map ι₁ ι₂) := by
    refine Submodule.map₂_le.2 fun m hm q hq ↦ ?_
    obtain ⟨p, hp, rfl⟩ := hm
    exact ⟨⟨p, hp⟩ ⊗ₜ ⟨q, hq⟩, rfl⟩
  obtain ⟨t, rfl⟩ := hle hz
  set f₁ := ((ChevalleyTwist.map (VermaModule.maxSubmodule R 𝕧 Λ.1).mkQ).restrictScalars 𝕂) ∘ₗ ι₁
  set f₂ := ((VermaModule.maxSubmodule R 𝕧 Λ''.1).mkQ.restrictScalars 𝕂) ∘ₗ ι₂
  have hf₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero _).2 fun p hp ↦ Subtype.ext ?_
    have hp' : ChevalleyTwist.toTwist R 𝕧 _
        ((VermaModule.maxSubmodule R 𝕧 Λ.1).mkQ (p : VermaModule R 𝕧 Λ.1)) = 0 := by
      simpa [f₁, ι₁] using hp
    rw [LinearEquiv.map_eq_zero_iff] at hp'
    exact eq_zero_of_mkQ_eq_zero hR Λ hΛ p.2 hp'
  have hf₂ : Function.Injective f₂ :=
    (injective_iff_map_eq_zero _).2 fun q hq ↦
      Subtype.ext (eq_zero_of_mkQ_eq_zero hR Λ'' hΛ'' q.2 hq)
  have e : tensorIrrProj Λ Λ'' (((TensorModule.mk _ _).toLinearMap ∘ₗ
      TensorProduct.map ι₁ ι₂) t) = TensorProduct.map f₁ f₂ t := by
    rw [tensorIrrProj, TensorProduct.map_comp]
    rfl
  rw [e] at h
  rw [map_injective_of_flat_flat f₁ f₂ hf₁ hf₂ (h.trans (map_zero _).symm), map_zero]

end Proj

/-! ### The action of `U̇` on `ξ_{-λ} ⊗ η_{λ''}` -/

section ModAct

variable (Λ Λ'' : Dom R)

omit [Finite I] in
lemma twHwv_tmul_mem_weightSpace :
    TensorModule.mk (TwL Λ) (IrreducibleModule R 𝕧 Λ''.1)
      (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
        IrreducibleModule.hwv R 𝕧 Λ''.1) ∈ weightSpace R 𝕧 _ (Λ''.1 - Λ.1) := by
  have hξ : ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ∈
      weightSpace R 𝕧 (TwL Λ) (-Λ.1) := fun μ ↦ by
    rw [ChevalleyTwist.smul_toTwist, chevalley_K, hw_K_smul_hwv, LinearEquiv.map_smul, map_neg,
      AddMonoidHom.neg_apply]
  have h := TensorModule.tmul_mem_weightSpace hξ
    (show IrreducibleModule.hwv R 𝕧 Λ''.1 ∈ weightSpace R 𝕧 _ Λ''.1 from
      fun μ ↦ hw_K_smul_hwv Λ'' μ)
  rwa [neg_add_eq_sub] at h

/-- `u ↦ u(ξ_{-λ} ⊗ η_{λ''})`, `U̇ → ʷΛ_λ ⊗ Λ_{λ''}` ([Lus] 23.1.4: `U̇` acts on the vectors of
weight `λ'' - λ`; the components `ₗU_μ` with `μ ≠ λ'' - λ` act by zero). -/
def modTensorAct : Modified R 𝕧 →ₗ[𝕂] TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ''.1 :=
  (TensorModule.mk _ _).symm.toLinearMap ∘ₗ
    weightAct R (Λ''.1 - Λ.1) _ (twHwv_tmul_mem_weightSpace Λ Λ'')

omit [Finite I] in
lemma modTensorAct_leftActOne {ζ : Y →+ ℤ} (hζ : Λ''.1 - Λ.1 = ζ) (u : QuantumGroup R 𝕧) :
    modTensorAct Λ Λ'' (leftActOne R hvn_ratFunc ζ u) =
      TensorModule.act R 𝕧 _ _ u (ChevalleyTwist.toTwist R 𝕧 _ (IrreducibleModule.hwv R 𝕧 Λ.1) ⊗ₜ[𝕂]
        IrreducibleModule.hwv R 𝕧 Λ''.1) := by
  subst hζ
  rw [modTensorAct, LinearMap.comp_apply, weightAct_leftActOne, TensorModule.smul_mk]
  rfl

omit [Finite I] in
lemma modTensorAct_leftActOne_triMul {ζ : Y →+ ℤ} (hζ : Λ''.1 - Λ.1 = ζ)
    (z : (LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧) ⊗[𝕂] (LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧)) :
    modTensorAct Λ Λ'' (leftActOne R hvn_ratFunc ζ (triMul R hvn_ratFunc z)) =
      tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1 z) := by
  rw [modTensorAct_leftActOne Λ Λ'' hζ, tensorIrrProj_triAct]

end ModAct

/-! ### Existence and uniqueness -/

section Main

local notation "fQ" => LusztigF 𝕂 I ⧸ serreSubmodule D 𝕧

omit [Finite I] [DecidableEq I] in
lemma weightSpace_le_degSpan {ν : I →₀ ℕ} {N : ℕ} (hν : ν.degree < N) :
    LusztigF.weightSpace 𝕂 ν ≤ degSpan 𝕂 I N := by
  rw [LusztigF.weightSpace_eq_span, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  change FreeAlgebra.wordBasis 𝕂 I w.1 ∈ _
  rw [← monomial_eq_wordBasis]
  refine monomial_mem_degSpan ?_
  rw [← degree_wordWeight, w.2]
  exact hν

variable (R) in
/-- `x ↦ x⁻η_λ`, `U⁻ → M_λ`. -/
def vermaMinus (Λ : Y →+ ℤ) (x : Um D 𝕧) : VermaModule R 𝕧 Λ :=
  quotientMinus R (negativeQuotientEquiv D x) • VermaModule.hwv R 𝕧 Λ

lemma vermaMinus_mk (Λ : Y →+ ℤ) (y : LusztigF 𝕂 I) :
    vermaMinus R Λ (Submodule.Quotient.mk y : Um D 𝕧) = VermaModule.toVerma R 𝕧 Λ y := by
  rw [VermaModule.toVerma_apply]
  rfl

lemma mkQ_vermaMinus (Λ : Dom R) (x : Um D 𝕧) :
    (VermaModule.maxSubmodule R 𝕧 Λ.1).mkQ (vermaMinus R Λ.1 x) = evq hvt Λ x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [vermaMinus_mk]
  rfl

/-- `x⁻η_λ` for `x ∈ U⁻_ν` with `tr ν < N` lies in `vermaDegSpan N`. -/
lemma vermaMinus_mem_vermaDegSpan (Λ : Y →+ ℤ) {ν : I →₀ ℕ} {N : ℕ} (hν : ν.degree < N)
    {x : Um D 𝕧} (hx : x ∈ Uw D 𝕧 ν) : vermaMinus R Λ x ∈ vermaDegSpan R 𝕧 Λ N := by
  obtain ⟨y, hy, rfl⟩ := hx
  change vermaMinus R Λ (Submodule.Quotient.mk y) ∈ _
  rw [vermaMinus_mk]
  exact ⟨y, weightSpace_le_degSpan hν hy, rfl⟩

/-- `x⁻η_λ` for `x ∈ 𝒜f` lies in `𝒜M_λ`. -/
lemma vermaMinus_mem_vermaLattice (Λ : Y →+ ℤ) {x : Um D 𝕧} (hx : x ∈ negIntegral D) :
    vermaMinus R Λ x ∈ vermaLattice R Λ := by
  have key : ∀ z ∈ quotientIntegralForm D, ∀ m ∈ vermaLattice R Λ,
      quotientMinus R z • m ∈ vermaLattice R Λ := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i, n, rfl⟩ := hz
      intro m hm
      rw [quotientIntegralGenerator, map_qDivPow', quotientMinus_θ]
      exact qDivPow_F_smul_mem_vermaLattice i n hm
    | algebraMap c =>
      intro m hm
      rw [show algebraMap (LaurentPolynomial ℤ) (Quotient D 𝕧) c =
        algebraMap 𝕂 (Quotient D 𝕧) (integralLaurentEval c) from rfl, AlgHom.commutes,
        algebraMap_smul]
      exact laurent_smul_mem_laurentSpan ⟨c, rfl⟩ hm
    | add a b _ _ ha hb =>
      intro m hm
      rw [map_add, add_smul]
      exact add_mem (ha m hm) (hb m hm)
    | mul a b _ _ ha hb =>
      intro m hm
      rw [_root_.map_mul, mul_smul]
      exact ha _ (hb m hm)
  exact key _ hx _ (mem_laurentSpan_of_mem ⟨[], by rw [fPow_nil, one_smul]⟩)

include hR in
/-- `b⁺ξ_{-λ} ⊗ b''⁻η_{λ''}` is the image of `ʷ(b⁻ξ) ⊗ b''⁻η` in `ʷM_λ ⊗ M_{λ''}`. -/
lemma tensorBasis_eq_tensorIrrProj (Λ Λ'' : Dom R)
    (h : canonicalBasisHW D Λ × canonicalBasisHW D Λ'') :
    tensorBasis hR Λ Λ'' h = tensorIrrProj Λ Λ'' (TensorModule.mk _ _
      (ChevalleyTwist.toTwist R 𝕧 _ (vermaMinus R Λ.1 h.1) ⊗ₜ[𝕂] vermaMinus R Λ''.1 h.2)) := by
  rw [tensorIrrProj_mk_tmul, tensorBasis_apply, ← mkQ_vermaMinus, ← mkQ_vermaMinus]
  rfl

include hR in
/-- `(b ◇ b'')_{λ,λ''}` is a `y⁻x⁺(ξ_{-λ} ⊗ η_{λ''})` with `[y] ⊗ [x] ∈ triDepth N N`, if
`tr |b|, tr |b''| < N`, and `y⁻x⁺(ξ_{-λ} ⊗ η_{λ''})` can be taken in `ʷ𝒜M_λ ⊗_𝒜 𝒜M_{λ''}`. -/
lemma exists_triAct_tensorCanonical (Λ Λ'' : Dom R) {N : ℕ}
    (h₀ : canonicalBasisHW D Λ × canonicalBasisHW D Λ'') (h₁ : (hwbWt Λ h₀.1).degree < N)
    (h₂ : (hwbWt Λ'' h₀.2).degree < N) :
    ∃ z ∈ triDepth D N N,
      triAct R hvn_ratFunc Λ.1 Λ''.1 z ∈ vermaTensorLattice R Λ.1 Λ''.1 ∧
      tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1 z) = tensorCanonical hR Λ Λ'' h₀ := by
  set c := (tensorBasisIdx hR Λ Λ'').repr (tensorCanonical hR Λ Λ'' h₀)
  set L : TensorIdx Λ Λ'' → TensorModule 𝕂 (ChevalleyTwist R 𝕧 (VermaModule R 𝕧 Λ.1))
      (VermaModule R 𝕧 Λ''.1) := fun h ↦ TensorModule.mk _ _
    (ChevalleyTwist.toTwist R 𝕧 _ (vermaMinus R Λ.1 h.1) ⊗ₜ[𝕂] vermaMinus R Λ''.1 h.2)
  have hsupp : ∀ h ∈ c.support,
      (hwbWt Λ h.1).degree < N ∧ (hwbWt Λ'' h.2).degree < N := by
    intro h hh
    have hd : (hwbWt Λ h.1).degree ≤ (hwbWt Λ h₀.1).degree ∧
        (hwbWt Λ'' h.2).degree ≤ (hwbWt Λ'' h₀.2).degree := by
      by_cases he : h = h₀
      · subst he
        exact ⟨le_rfl, le_rfl⟩
      · have hl := tensorLt_of_repr_tensorCanonical_ne_zero hR Λ Λ'' he
          (Finsupp.mem_support_iff.1 hh)
        exact ⟨hl.2.1.le, hl.2.2.le⟩
    exact ⟨hd.1.trans_lt h₁, hd.2.trans_lt h₂⟩
  have hm : c.sum (fun h a ↦ a • L h) ∈ tensorDepth R Λ.1 Λ''.1 N N :=
    Submodule.sum_mem _ fun h hh ↦ Submodule.smul_mem _ _
      (tmul_mem_tensorDepth (vermaMinus_mem_vermaDegSpan _ (hsupp h hh).1 (mem_Uw_cbWt _))
        (vermaMinus_mem_vermaDegSpan _ (hsupp h hh).2 (mem_Uw_cbWt _)))
  have hmL : c.sum (fun h a ↦ a • L h) ∈ vermaTensorLattice R Λ.1 Λ''.1 := by
    refine Submodule.sum_mem _ fun h _ ↦ ?_
    have hc : IsLaurent (c h) := by
      rw [show c h = _ from repr_tensorCanonical hR Λ Λ'' h₀ h]
      split_ifs
      · exact ⟨_, rfl⟩
      · exact ⟨0, map_zero _⟩
    exact laurent_smul_mem_laurentSpan hc (tmul_mem_vermaTensorLattice
      (vermaMinus_mem_vermaLattice _ (negIntegral_of_mem_canonicalBasis
        (canonicalBasisHW_subset D Λ h.1.2)))
      (vermaMinus_mem_vermaLattice _ (negIntegral_of_mem_canonicalBasis
        (canonicalBasisHW_subset D Λ'' h.2.2))))
  have hproj : tensorIrrProj Λ Λ'' (c.sum fun h a ↦ a • L h) =
      tensorCanonical hR Λ Λ'' h₀ := by
    conv_rhs => rw [← (tensorBasisIdx hR Λ Λ'').linearCombination_repr
      (tensorCanonical hR Λ Λ'' h₀)]
    rw [Finsupp.linearCombination_apply]
    simp only [Finsupp.sum, map_sum, map_smul, L]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    exact congrArg (c h • ·) (tensorBasis_eq_tensorIrrProj hR Λ Λ'' h).symm
  obtain ⟨z, hz, ez⟩ := exists_triAct_eq Λ.1 Λ''.1 N N hm
  exact ⟨z, hz, ez ▸ hmL, ez ▸ hproj⟩

/-- `t(y⁻x⁺(ξ_{-λ'-λ} ⊗ η_{λ'+λ''})) = y⁻x⁺(ξ_{-λ} ⊗ η_{λ''})`. -/
lemma tensorTransition_tensorIrrProj_triAct (Λ Λ' Λ'' : Dom R) (z : fQ ⊗[𝕂] fQ) :
    tensorTransition hR Λ Λ' Λ'' (tensorIrrProj (Λ' + Λ) (Λ' + Λ'')
      (triAct R hvn_ratFunc (Λ' + Λ).1 (Λ' + Λ'').1 z)) =
      tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1 z) := by
  rw [tensorIrrProj_triAct, tensorIrrProj_triAct, tensorTransition_act, tensorTransition_hwv]

include hR in
/-- If `y⁻x⁺(ξ_{-λ} ⊗ η_{λ''}) = 0` in `ʷΛ_λ ⊗ Λ_{λ''}` with `[y] ⊗ [x] ∈ triDepth n n` and
`n ≤ ⟨i, λ⟩, ⟨i, λ''⟩` for all `i`, then `y⁻x⁺1_{λ''-λ} = 0`. -/
lemma leftActOne_triMul_eq_zero (Λ Λ'' : Dom R) {n : ℕ} (hΛ : ∀ i, (n : ℤ) ≤ Λ.1 (R.coroot i))
    (hΛ'' : ∀ i, (n : ℤ) ≤ Λ''.1 (R.coroot i)) {z : fQ ⊗[𝕂] fQ} (hz : z ∈ triDepth D n n)
    (h : tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1 z) = 0) :
    leftActOne R hvn_ratFunc (Λ''.1 - Λ.1) (triMul R hvn_ratFunc z) = 0 :=
  (smul_vermaTensorHwv_eq_zero_iff hvn_ratFunc Λ.1 Λ''.1 _).1
    (eq_zero_of_tensorIrrProj_eq_zero hR Λ Λ'' hΛ hΛ'' (triAct_mem_tensorDepth Λ.1 Λ''.1 hz) h)

/-- An element `b ∈ B` lies in `B(λ)` as soon as `tr |b| ≤ ⟨i, λ⟩` for all `i`. -/
lemma mem_canonicalBasisHW_of_cbWt (Λ : Dom R) {b : Um D 𝕧} (hb : b ∈ canonicalBasis D)
    (hΛ : ∀ i, ((cbWt D ⟨b, hb⟩).degree : ℤ) ≤ Λ.1 (R.coroot i)) : b ∈ canonicalBasisHW D Λ :=
  mem_canonicalBasisHW_of_degree_le Λ hb (mem_Uw_cbWt ⟨b, hb⟩) hΛ

variable (hY : ∀ N : ℕ, ∃ Λ : Dom R, ∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i))

omit [DecidableEq I] in
include hY in
/-- Dominant `λ, λ''` with `λ'' - λ = ζ` and all `⟨i, λ⟩, ⟨i, λ''⟩ ≥ M`. -/
lemma exists_dom_pair (ζ : Y →+ ℤ) (M : ℕ) :
    ∃ Λ Λ'' : Dom R, Λ''.1 - Λ.1 = ζ ∧ (∀ i, (M : ℤ) ≤ Λ.1 (R.coroot i)) ∧
      ∀ i, (M : ℤ) ≤ Λ''.1 (R.coroot i) := by
  obtain ⟨C, hC⟩ := Finite.exists_le fun i ↦ -ζ (R.coroot i)
  obtain ⟨Λ, hΛ⟩ := hY (M + C.toNat)
  have h : ∀ i, (M : ℤ) ≤ (Λ.1 + ζ) (R.coroot i) := fun i ↦ by
    have h1 := hΛ i
    have h2 := hC i
    have h3 := Int.self_le_toNat C
    rw [AddMonoidHom.add_apply]
    push_cast at h1
    omega
  exact ⟨Λ, ⟨Λ.1 + ζ, fun i ↦ (Int.natCast_nonneg M).trans (h i)⟩, add_sub_cancel_left _ _,
    fun i ↦ by have := hΛ i; push_cast at this; omega, h⟩

include hR hY in
/-- An element `u ∈ U̇1_ζ` with `u(ξ_{-λ} ⊗ η_{λ''}) = 0` in `ʷΛ_λ ⊗ Λ_{λ''}` for all large
`λ, λ''` with `λ'' - λ = ζ` is zero. -/
theorem eq_zero_of_modTensorAct_eq_zero {ζ : Y →+ ℤ} {u : Modified R 𝕧}
    (hu : u ∈ LinearMap.range (leftActOne R hvn_ratFunc ζ)) (M : ℕ)
    (h : ∀ Λ Λ'' : Dom R, Λ''.1 - Λ.1 = ζ → (∀ i, (M : ℤ) ≤ Λ.1 (R.coroot i)) →
      (∀ i, (M : ℤ) ≤ Λ''.1 (R.coroot i)) → modTensorAct Λ Λ'' u = 0) : u = 0 := by
  obtain ⟨w, rfl⟩ := hu
  obtain ⟨z, hz⟩ := exists_leftActOne_eq_triMul hvn_ratFunc ζ w
  obtain ⟨n, hn⟩ := exists_mem_triDepth z
  obtain ⟨Λ, Λ'', hζ, hΛ, hΛ''⟩ := exists_dom_pair hY ζ (max n M)
  have hle : ∀ m, m ≤ max n M → ∀ x : ℤ, ((max n M : ℕ) : ℤ) ≤ x → (m : ℤ) ≤ x :=
    fun m hm x hx ↦ (Int.ofNat_le.2 hm).trans hx
  have h0 := h Λ Λ'' hζ (fun i ↦ hle M (le_max_right _ _) _ (hΛ i))
    (fun i ↦ hle M (le_max_right _ _) _ (hΛ'' i))
  rw [hz, modTensorAct_leftActOne_triMul Λ Λ'' hζ] at h0
  rw [hz, ← hζ]
  exact leftActOne_triMul_eq_zero hR Λ Λ'' (fun i ↦ hle n (le_max_left _ _) _ (hΛ i))
    (fun i ↦ hle n (le_max_left _ _) _ (hΛ'' i)) hn h0

include hR hY in
/-- **[Lus] Thm. 25.2.1 (a), (b)**, existence: there is `u ∈ U̇1_ζ ∩ 𝒜U̇` with
`u(ξ_{-λ} ⊗ η_{λ''}) = (b ◇ b'')_{λ,λ''}` for all dominant `λ, λ''` with `λ'' - λ = ζ`,
`b ∈ B(λ)`, `b'' ∈ B(λ'')`, and `u(ξ_{-λ} ⊗ η_{λ''}) = 0` if `b ∉ B(λ)` or `b'' ∉ B(λ'')`. -/
theorem exists_modifiedCanonical (ζ : Y →+ ℤ) {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D)
    (hb'' : b'' ∈ canonicalBasis D) :
    ∃ u ∈ LinearMap.range (leftActOne R hvn_ratFunc ζ), u ∈ aForm R ∧
      (∀ (Λ Λ'' : Dom R) (_ : Λ''.1 - Λ.1 = ζ) (h₁ : b ∈ canonicalBasisHW D Λ)
        (h₂ : b'' ∈ canonicalBasisHW D Λ''),
        modTensorAct Λ Λ'' u = tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩)) ∧
      ∀ (Λ Λ'' : Dom R), Λ''.1 - Λ.1 = ζ →
        (b ∉ canonicalBasisHW D Λ ∨ b'' ∉ canonicalBasisHW D Λ'') →
          modTensorAct Λ Λ'' u = 0 := by
  set N := max (cbWt D ⟨b, hb⟩).degree (cbWt D ⟨b'', hb''⟩).degree + 1
  have hN₁ : (cbWt D ⟨b, hb⟩).degree < N := Nat.lt_succ_of_le (le_max_left _ _)
  have hN₂ : (cbWt D ⟨b'', hb''⟩).degree < N := Nat.lt_succ_of_le (le_max_right _ _)
  have hmem : ∀ Λ : Dom R, (∀ i, (N : ℤ) ≤ Λ.1 (R.coroot i)) →
      b ∈ canonicalBasisHW D Λ ∧ b'' ∈ canonicalBasisHW D Λ := fun Λ hΛ ↦
    ⟨mem_canonicalBasisHW_of_cbWt Λ hb fun i ↦ by have := hΛ i; omega,
      mem_canonicalBasisHW_of_cbWt Λ hb'' fun i ↦ by have := hΛ i; omega⟩
  have works : ∀ Λ Λ'' : Dom R, ∀ (h₁ : b ∈ canonicalBasisHW D Λ)
      (h₂ : b'' ∈ canonicalBasisHW D Λ''), ∃ z ∈ triDepth D N N,
        triAct R hvn_ratFunc Λ.1 Λ''.1 z ∈ vermaTensorLattice R Λ.1 Λ''.1 ∧
        tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1 z) =
          tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩) := fun Λ Λ'' h₁ h₂ ↦
    exists_triAct_tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩) hN₁ hN₂
  obtain ⟨Λ₀, Λ₀'', hζ₀, hΛ₀, hΛ₀''⟩ := exists_dom_pair hY ζ N
  have hb₀ := (hmem Λ₀ hΛ₀).1
  have hb₀'' := (hmem Λ₀'' hΛ₀'').2
  obtain ⟨z₀, hz₀, hL₀, e₀⟩ := works Λ₀ Λ₀'' hb₀ hb₀''
  refine ⟨leftActOne R hvn_ratFunc ζ (triMul R hvn_ratFunc z₀), ⟨_, rfl⟩, ?_, ?_⟩
  · rw [← hζ₀]
    exact (leftActOne_mem_aForm_iff Λ₀.1 Λ₀''.1 _).2 hL₀
  have key : ∀ Λ Λ'' : Dom R, Λ''.1 - Λ.1 = ζ → ∃ z₁ : fQ ⊗[𝕂] fQ,
      ∃ (h₁ : b ∈ canonicalBasisHW D (Λ₀ + Λ)) (h₂ : b'' ∈ canonicalBasisHW D (Λ₀ + Λ'')),
        tensorIrrProj (Λ₀ + Λ) (Λ₀ + Λ'') (triAct R hvn_ratFunc (Λ₀ + Λ).1 (Λ₀ + Λ'').1 z₁) =
          tensorCanonical hR (Λ₀ + Λ) (Λ₀ + Λ'') (⟨b, h₁⟩, ⟨b'', h₂⟩) ∧
        modTensorAct Λ Λ'' (leftActOne R hvn_ratFunc ζ (triMul R hvn_ratFunc z₀)) =
          tensorIrrProj Λ Λ'' (triAct R hvn_ratFunc Λ.1 Λ''.1 z₁) := by
    intro Λ Λ'' hζ
    have hlarge : ∀ Λ' : Dom R, ∀ i, (N : ℤ) ≤ (Λ₀ + Λ').1 (R.coroot i) := fun Λ' i ↦ by
      have := hΛ₀ i
      have := Λ'.2 i
      rw [Dom.add_val, AddMonoidHom.add_apply]
      omega
    have h₁ : b ∈ canonicalBasisHW D (Λ₀ + Λ) := (hmem _ (hlarge Λ)).1
    have h₂ : b'' ∈ canonicalBasisHW D (Λ₀ + Λ'') := (hmem _ (hlarge Λ'')).2
    obtain ⟨z₁, hz₁, -, e₁⟩ := works (Λ₀ + Λ) (Λ₀ + Λ'') h₁ h₂
    refine ⟨z₁, h₁, h₂, e₁, ?_⟩
    have eP : Λ₀ + Λ = Λ + Λ₀ := Subtype.ext (by rw [Dom.add_val, Dom.add_val, add_comm])
    have eQ : Λ₀ + Λ'' = Λ + Λ₀'' := Subtype.ext (by
      rw [Dom.add_val, Dom.add_val, ← sub_add_cancel Λ''.1 Λ.1, ← sub_add_cancel Λ₀''.1 Λ₀.1,
        hζ, hζ₀]
      abel)
    have e₁' : tensorIrrProj Λ₀ Λ₀'' (triAct R hvn_ratFunc Λ₀.1 Λ₀''.1 z₁) =
        tensorCanonical hR Λ₀ Λ₀'' (⟨b, hb₀⟩, ⟨b'', hb₀''⟩) := by
      have h₁' : b ∈ canonicalBasisHW D (Λ + Λ₀) := canonicalBasisHW_subset_add D Λ₀ Λ hb₀
      have h₂' : b'' ∈ canonicalBasisHW D (Λ + Λ₀'') := canonicalBasisHW_subset_add D Λ₀'' Λ hb₀''
      have e : tensorIrrProj (Λ + Λ₀) (Λ + Λ₀'')
          (triAct R hvn_ratFunc (Λ + Λ₀).1 (Λ + Λ₀'').1 z₁) =
            tensorCanonical hR (Λ + Λ₀) (Λ + Λ₀'') (⟨b, h₁'⟩, ⟨b'', h₂'⟩) := by
        clear_value N
        revert h₁ h₂ e₁ h₁' h₂'
        rw [eP, eQ]
        intro h₁ h₂ e₁ _ _
        exact e₁
      rw [← tensorTransition_tensorIrrProj_triAct hR Λ₀ Λ Λ₀'', e]
      exact tensorTransition_tensorCanonical hR Λ₀ Λ Λ₀'' ⟨b, hb₀⟩ ⟨b'', hb₀''⟩
    have hzero : leftActOne R hvn_ratFunc ζ (triMul R hvn_ratFunc (z₁ - z₀)) = 0 := by
      rw [← hζ₀]
      refine leftActOne_triMul_eq_zero hR Λ₀ Λ₀'' hΛ₀ hΛ₀'' (sub_mem hz₁ hz₀) ?_
      rw [map_sub, map_sub, e₁', e₀, sub_self]
    rw [map_sub, map_sub, sub_eq_zero] at hzero
    rw [← hzero, modTensorAct_leftActOne_triMul Λ Λ'' hζ]
  refine ⟨fun Λ Λ'' hζ h₁ h₂ ↦ ?_, fun Λ Λ'' hζ h ↦ ?_⟩
  · obtain ⟨z₁, h₁', h₂', e₁, e⟩ := key Λ Λ'' hζ
    rw [e, ← tensorTransition_tensorIrrProj_triAct hR Λ Λ₀ Λ'', e₁]
    exact tensorTransition_tensorCanonical hR Λ Λ₀ Λ'' ⟨b, h₁⟩ ⟨b'', h₂⟩
  · obtain ⟨z₁, h₁', h₂', e₁, e⟩ := key Λ Λ'' hζ
    rw [e, ← tensorTransition_tensorIrrProj_triAct hR Λ Λ₀ Λ'', e₁]
    exact tensorTransition_tensorCanonical_eq_zero hR Λ Λ₀ Λ'' ⟨b, h₁'⟩ ⟨b'', h₂'⟩ h

include hR hY in
/-- **[Lus] Thm. 25.2.1 (a)**: for `ζ ∈ X` and `b, b'' ∈ B` there is a unique `u ∈ U̇1_ζ` with
`u(ξ_{-λ} ⊗ η_{λ''}) = (b ◇ b'')_{λ,λ''}` for all dominant `λ, λ''` with `λ'' - λ = ζ`,
`b ∈ B(λ)` and `b'' ∈ B(λ'')`. Lusztig assumes the root datum `Y`-regular; `hY` is what the
proof uses of it (see the module docstring). -/
theorem existsUnique_modifiedCanonical (ζ : Y →+ ℤ) {b b'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) :
    ∃! u, u ∈ LinearMap.range (leftActOne R hvn_ratFunc ζ) ∧
      ∀ (Λ Λ'' : Dom R) (_ : Λ''.1 - Λ.1 = ζ) (h₁ : b ∈ canonicalBasisHW D Λ)
        (h₂ : b'' ∈ canonicalBasisHW D Λ''),
        modTensorAct Λ Λ'' u = tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩) := by
  obtain ⟨u, hu, -, ha, -⟩ := exists_modifiedCanonical hR hY ζ hb hb''
  refine ⟨u, ⟨hu, ha⟩, fun u' ⟨hu', ha'⟩ ↦ ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_modTensorAct_eq_zero hR hY (sub_mem hu' hu)
    (max (cbWt D ⟨b, hb⟩).degree (cbWt D ⟨b'', hb''⟩).degree) fun Λ Λ'' hζ hΛ hΛ'' ↦ ?_
  have h₁ := mem_canonicalBasisHW_of_cbWt Λ hb fun i ↦ by
    have := hΛ i
    push_cast at this
    omega
  have h₂ := mem_canonicalBasisHW_of_cbWt Λ'' hb'' fun i ↦ by
    have := hΛ'' i
    push_cast at this
    omega
  rw [map_sub, ha Λ Λ'' hζ h₁ h₂, ha' Λ Λ'' hζ h₁ h₂, sub_self]

/-- **[Lus] 25.2.1**: the element `b ◇_ζ b''` of `U̇1_ζ`, for `b, b'' ∈ B`. -/
def modifiedCanonical (ζ : Y →+ ℤ) {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D)
    (hb'' : b'' ∈ canonicalBasis D) : Modified R 𝕧 :=
  (exists_modifiedCanonical hR hY ζ hb hb'').choose

theorem modifiedCanonical_mem_range (ζ : Y →+ ℤ) {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D)
    (hb'' : b'' ∈ canonicalBasis D) :
    modifiedCanonical hR hY ζ hb hb'' ∈ LinearMap.range (leftActOne R hvn_ratFunc ζ) :=
  (exists_modifiedCanonical hR hY ζ hb hb'').choose_spec.1

/-- **[Lus] Thm. 25.2.1 (a)**: `b ◇_ζ b'' ∈ 𝒜U̇`. -/
theorem modifiedCanonical_mem_aForm (ζ : Y →+ ℤ) {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D)
    (hb'' : b'' ∈ canonicalBasis D) : modifiedCanonical hR hY ζ hb hb'' ∈ aForm R :=
  (exists_modifiedCanonical hR hY ζ hb hb'').choose_spec.2.1

/-- **[Lus] Thm. 25.2.1 (a)**: `(b ◇_ζ b'')(ξ_{-λ} ⊗ η_{λ''}) = (b ◇ b'')_{λ,λ''}` for
`λ'' - λ = ζ`, `b ∈ B(λ)`, `b'' ∈ B(λ'')`. -/
theorem modTensorAct_modifiedCanonical (ζ : Y →+ ℤ) {b b'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) (Λ Λ'' : Dom R)
    (hζ : Λ''.1 - Λ.1 = ζ) (h₁ : b ∈ canonicalBasisHW D Λ) (h₂ : b'' ∈ canonicalBasisHW D Λ'') :
    modTensorAct Λ Λ'' (modifiedCanonical hR hY ζ hb hb'') =
      tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩) :=
  (exists_modifiedCanonical hR hY ζ hb hb'').choose_spec.2.2.1 Λ Λ'' hζ h₁ h₂

/-- **[Lus] Thm. 25.2.1 (b)**: `(b ◇_ζ b'')(ξ_{-λ} ⊗ η_{λ''}) = 0` for `λ'' - λ = ζ` if
`b ∉ B(λ)` or `b'' ∉ B(λ'')`. -/
theorem modTensorAct_modifiedCanonical_eq_zero (ζ : Y →+ ℤ) {b b'' : Um D 𝕧}
    (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) (Λ Λ'' : Dom R)
    (hζ : Λ''.1 - Λ.1 = ζ) (h : b ∉ canonicalBasisHW D Λ ∨ b'' ∉ canonicalBasisHW D Λ'') :
    modTensorAct Λ Λ'' (modifiedCanonical hR hY ζ hb hb'') = 0 :=
  (exists_modifiedCanonical hR hY ζ hb hb'').choose_spec.2.2.2 Λ Λ'' hζ h

/-- `ū(ξ_{-λ} ⊗ η_{λ''}) = Ψ(u(ξ_{-λ} ⊗ η_{λ''}))` for `u ∈ U̇1_ζ` and `λ'' - λ = ζ`, with `ū` the
bar involution of `U̇` ([Lus] 23.1.8) and `Ψ` that of `ʷΛ_λ ⊗ Λ_{λ''}` ([Lus] 24.3.2); this is the
computation in Lusztig's proof of 25.2.1 (c). -/
theorem modTensorAct_bar {ζ : Y →+ ℤ} (Λ Λ'' : Dom R) (hζ : Λ''.1 - Λ.1 = ζ)
    {u : Modified R 𝕧} (hu : u ∈ LinearMap.range (leftActOne R hvn_ratFunc ζ)) :
    modTensorAct Λ Λ'' (Modified.bar R u) = tensorPsi hR Λ Λ'' (modTensorAct Λ Λ'' u) := by
  obtain ⟨x, rfl⟩ := hu
  rw [Modified.bar_leftActOne, modTensorAct_leftActOne Λ Λ'' hζ,
    modTensorAct_leftActOne Λ Λ'' hζ, tensorPsi_act_hwv]

/-- **[Lus] Thm. 25.2.1 (c)**: `b ◇_ζ b''` is fixed by the bar involution of `U̇`. -/
theorem bar_modifiedCanonical (ζ : Y →+ ℤ) {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D)
    (hb'' : b'' ∈ canonicalBasis D) :
    Modified.bar R (modifiedCanonical hR hY ζ hb hb'') = modifiedCanonical hR hY ζ hb hb'' := by
  have hu := modifiedCanonical_mem_range hR hY ζ hb hb''
  refine (existsUnique_modifiedCanonical hR hY ζ hb hb'').unique ⟨?_, fun Λ Λ'' hζ h₁ h₂ ↦ ?_⟩
    ⟨hu, fun Λ Λ'' hζ h₁ h₂ ↦ modTensorAct_modifiedCanonical hR hY ζ hb hb'' Λ Λ'' hζ h₁ h₂⟩
  · obtain ⟨x, hx⟩ := hu
    exact ⟨barHom R x, by rw [← hx, Modified.bar_leftActOne]⟩
  · rw [modTensorAct_bar hR Λ Λ'' hζ hu,
      modTensorAct_modifiedCanonical hR hY ζ hb hb'' Λ Λ'' hζ h₁ h₂]
    exact tensorPsi_tensorCanonical hR Λ Λ'' (⟨b, h₁⟩, ⟨b'', h₂⟩)

end Main

end LieLean.QuantumGroup

/-! ### Fixed-column comparison for the reduction in [Lus] 25.2.2 -/

namespace LieLean.QuantumGroup.Modified

open TensorProduct

variable {k I Y Y' : Type*} [Field k] [AddCommGroup Y] [AddCommGroup Y']
  [DecidableEq I] {D : LusztigCartanDatum I} (R : D.RootDatum Y) (R' : D.RootDatum Y')
  {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

local notation "fQ" => LusztigF k I ⧸ serreSubmodule D v

/-- Triangular coordinates on a fixed right column of the modified quantum group. -/
def columnTriangularEquiv (ζ : Y →+ ℤ) :
    fQ ⊗[k] fQ ≃ₗ[k] LinearMap.range (leftActOne R hv ζ) :=
  LinearEquiv.ofBijective
    (((leftActOne R hv ζ).rangeRestrict).comp (triMul R hv)) <| by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, ?_⟩
    · intro z hz
      have hz' : leftActOne R hv ζ (triMul R hv z) = 0 := congrArg Subtype.val hz
      have hact : triAct R hv 0 ζ z = 0 := by
        apply (smul_vermaTensorHwv_eq_zero_iff hv 0 ζ _).2
        simpa using hz'
      exact (injective_iff_map_eq_zero _).1 (bijective_triAct hv 0 ζ).1 z hact
    · rintro ⟨_, u, rfl⟩
      obtain ⟨z, hz⟩ := exists_leftActOne_eq_triMul hv ζ u
      exact ⟨z, Subtype.ext hz.symm⟩

@[simp] theorem columnTriangularEquiv_apply (ζ : Y →+ ℤ) (z : fQ ⊗[k] fQ) :
    (columnTriangularEquiv R hv ζ z : Modified R v) = leftActOne R hv ζ (triMul R hv z) :=
  rfl

/-- The fixed-column comparison of Lusztig §23.2.5. The source weight is the pullback of
`ζ`; no injectivity or surjectivity on the set of all weights is required. Lusztig uses a
simply connected source over `ℚ(v)`; triangular coordinates give the same comparison for
any morphism of the existing root data over a field at a non-root-of-unity parameter. -/
def columnEquiv (φ : R.Hom R') (ζ : Y' →+ ℤ) :
    LinearMap.range (leftActOne R hv (ζ.comp φ.toHom)) ≃ₗ[k]
      LinearMap.range (leftActOne R' hv ζ) :=
  (columnTriangularEquiv R hv (ζ.comp φ.toHom)).symm.trans
    (columnTriangularEquiv R' hv ζ)

@[simp] theorem columnEquiv_triMul (φ : R.Hom R') (ζ : Y' →+ ℤ) (z : fQ ⊗[k] fQ) :
    (columnEquiv R R' hv φ ζ
      ⟨leftActOne R hv (ζ.comp φ.toHom) (triMul R hv z), _, rfl⟩ : Modified R' v) =
      leftActOne R' hv ζ (triMul R' hv z) := by
  change ((columnTriangularEquiv R' hv ζ)
    ((columnTriangularEquiv R hv (ζ.comp φ.toHom)).symm
      (columnTriangularEquiv R hv (ζ.comp φ.toHom) z)) : Modified R' v) = _
  rw [LinearEquiv.symm_apply_apply, columnTriangularEquiv_apply]

omit [NeZero v] in
/-- The root-datum map preserves the positive and negative word embeddings. -/
lemma mapHom_minus_plus (φ : R.Hom R') (y x : LusztigF k I) :
    QuantumGroup.mapHom v φ (minusHom R v y * plusHom R v x) =
      minusHom R' v y * plusHom R' v x := by
  have hm : (QuantumGroup.mapHom v φ).comp (minusHom R v) = minusHom R' v := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [minusHom]
  have hp : (QuantumGroup.mapHom v φ).comp (plusHom R v) = plusHom R' v := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [plusHom]
  rw [_root_.map_mul (QuantumGroup.mapHom v φ), ← AlgHom.comp_apply, hm, ← AlgHom.comp_apply, hp]

/-- The column comparison is induced by the root-datum algebra homomorphism, as in
Lusztig §23.2.5. In particular, it is not merely an arbitrary vector-space equivalence. -/
theorem columnEquiv_leftActOne (φ : R.Hom R') (ζ : Y' →+ ℤ) (u : QuantumGroup R v) :
    (columnEquiv R R' hv φ ζ ⟨leftActOne R hv (ζ.comp φ.toHom) u, u, rfl⟩ :
      Modified R' v) = leftActOne R' hv ζ (QuantumGroup.mapHom v φ u) := by
  let T : QuantumGroup R v →ₗ[k] Modified R' v :=
    (LinearMap.range (leftActOne R' hv ζ)).subtype.comp
      ((columnEquiv R R' hv φ ζ).toLinearMap.comp
        (leftActOne R hv (ζ.comp φ.toHom)).rangeRestrict)
  change T u = _
  induction VermaModule.mem_triangularSpan_of u (NeZero.ne v) using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, μ, w', rfl⟩ := hu
    have hroot : R'.rootSum (LusztigF.wordWeight w') (φ.toHom μ) =
        R.rootSum (LusztigF.wordWeight w') μ := by
      simp [LusztigCartanDatum.RootDatum.rootSum, φ.root_map]
    have hnorm (S : D.RootDatum Y) (ξ : Y →+ ℤ) :
        leftActOne S hv ξ
          (minusHom S v (LusztigF.monomial k w) * K S v μ *
            plusHom S v (LusztigF.monomial k w')) =
        (v ^ S.rootSum (LusztigF.wordWeight w') μ * v ^ ξ μ) •
          leftActOne S hv ξ (minusHom S v (LusztigF.monomial k w) *
            plusHom S v (LusztigF.monomial k w')) := by
      rw [mul_assoc, K_mul_plusHom_of_mem (LusztigF.monomial_mem_weightSpace w') μ,
        mul_smul_comm, map_smul, ← mul_assoc, leftActOne_mul_K, smul_smul]
    have ht : T (minusHom R v (LusztigF.monomial k w) *
        plusHom R v (LusztigF.monomial k w')) =
        leftActOne R' hv ζ (minusHom R' v (LusztigF.monomial k w) *
          plusHom R' v (LusztigF.monomial k w')) :=
      columnEquiv_triMul R R' hv φ ζ
        (Submodule.Quotient.mk (LusztigF.monomial k w) ⊗ₜ
          Submodule.Quotient.mk (LusztigF.monomial k w'))
    have hT : T (minusHom R v (LusztigF.monomial k w) * K R v μ *
        plusHom R v (LusztigF.monomial k w')) =
        (v ^ R.rootSum (LusztigF.wordWeight w') μ * v ^ ζ (φ.toHom μ)) •
          T (minusHom R v (LusztigF.monomial k w) *
            plusHom R v (LusztigF.monomial k w')) := by
      have he : (leftActOne R hv (ζ.comp φ.toHom)).rangeRestrict
          (minusHom R v (LusztigF.monomial k w) * K R v μ *
            plusHom R v (LusztigF.monomial k w')) =
          (v ^ R.rootSum (LusztigF.wordWeight w') μ * v ^ ζ (φ.toHom μ)) •
          (leftActOne R hv (ζ.comp φ.toHom)).rangeRestrict
            (minusHom R v (LusztigF.monomial k w) *
              plusHom R v (LusztigF.monomial k w')) :=
        Subtype.ext (hnorm R (ζ.comp φ.toHom))
      change (columnEquiv R R' hv φ ζ _ : Modified R' v) = _
      rw [he, map_smul]
      rfl
    rw [hT, ht]
    have hm : QuantumGroup.mapHom v φ (minusHom R v (LusztigF.monomial k w)) =
        minusHom R' v (LusztigF.monomial k w) := by
      simpa using mapHom_minus_plus R R' φ (LusztigF.monomial k w) 1
    have hp : QuantumGroup.mapHom v φ (plusHom R v (LusztigF.monomial k w')) =
        plusHom R' v (LusztigF.monomial k w') := by
      simpa using mapHom_minus_plus R R' φ 1 (LusztigF.monomial k w')
    rw [_root_.map_mul (QuantumGroup.mapHom v φ), _root_.map_mul (QuantumGroup.mapHom v φ), hm, hp,
      mapHom_K, mul_assoc,
      K_mul_plusHom_of_mem (LusztigF.monomial_mem_weightSpace w') (φ.toHom μ),
      mul_smul_comm, map_smul, ← mul_assoc, leftActOne_mul_K, smul_smul, hroot]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [map_smul, hx]

/-- The column comparison intertwines the left action through the root-datum algebra map. -/
theorem columnEquiv_mul (φ : R.Hom R') (ζ : Y' →+ ℤ) (a u : QuantumGroup R v) :
    (columnEquiv R R' hv φ ζ
      ⟨leftActOne R hv (ζ.comp φ.toHom) (a * u), a * u, rfl⟩ : Modified R' v) =
      leftAct R' v hv (QuantumGroup.mapHom v φ a)
        (columnEquiv R R' hv φ ζ
          ⟨leftActOne R hv (ζ.comp φ.toHom) u, u, rfl⟩ : Modified R' v) := by
  rw [columnEquiv_leftActOne, columnEquiv_leftActOne, _root_.map_mul (QuantumGroup.mapHom v φ),
    leftActOne_apply, leftAct_mul, leftActOne_apply]

/-- The root-datum algebra map reflects vanishing in each corresponding right column. -/
theorem leftActOne_mapHom_eq_zero_iff (φ : R.Hom R') (ζ : Y' →+ ℤ)
    (u : QuantumGroup R v) :
    leftActOne R' hv ζ (QuantumGroup.mapHom v φ u) = 0 ↔
      leftActOne R hv (ζ.comp φ.toHom) u = 0 := by
  rw [← columnEquiv_leftActOne R R' hv φ ζ u]
  constructor
  · intro h
    have he : columnEquiv R R' hv φ ζ
        ⟨leftActOne R hv (ζ.comp φ.toHom) u, u, rfl⟩ = 0 := Subtype.ext h
    have hz := (columnEquiv R R' hv φ ζ).injective
      (he.trans (map_zero _).symm)
    exact congrArg Subtype.val hz
  · intro h
    have hz : (⟨leftActOne R hv (ζ.comp φ.toHom) u, u, rfl⟩ :
        LinearMap.range (leftActOne R hv (ζ.comp φ.toHom))) = 0 := Subtype.ext h
    rw [hz, map_zero, Submodule.coe_zero]

end LieLean.QuantumGroup.Modified

/-! ### Integral columns and transport from the free-coroot datum -/

namespace LieLean.QuantumGroup.Modified

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ
attribute [local instance] neZero_ratFunc_X

variable {I Y Y' : Type*} [AddCommGroup Y] [AddCommGroup Y'] [DecidableEq I]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y) (R' : D.RootDatum Y')

/-- The root-datum map preserves the divided-power triangular generators. -/
lemma mapHom_fePow (φ : R.Hom R') (w w' : List (I × ℕ)) :
    QuantumGroup.mapHom 𝕧 φ (fPow R w * ePow R w') = fPow R' w * ePow R' w' := by
  simp [fPow, ePow, qDivPow, map_list_prod, List.map_map, Function.comp_def]

/-- The root-datum map sends the integral triangular span onto its target counterpart. -/
lemma mapHom_fePowSpan (φ : R.Hom R') :
    (fePowSpan R).map (QuantumGroup.mapHom 𝕧 φ).toLinearMap.toAddMonoidHom.toIntLinearMap =
      fePowSpan R' := by
  rw [fePowSpan, laurentSpan, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨n, _, ⟨w, w', rfl⟩, rfl⟩, rfl⟩
    exact ⟨n, _, ⟨w, w', rfl⟩, by simp [mapHom_fePow]⟩
  · rintro ⟨n, _, ⟨w, w', rfl⟩, rfl⟩
    refine ⟨(𝕧 ^ n) • (fPow R w * ePow R w'), ⟨n, _, ⟨w, w', rfl⟩, rfl⟩, ?_⟩
    simp [mapHom_fePow]

/-- Every integral element in a column has a lift in the divided-power triangular span. -/
lemma exists_fePowSpan_leftActOne (ζ : Y →+ ℤ) {x : Modified R 𝕧}
    (hx : x ∈ LinearMap.range (leftActOne R ratFunc_X_not_root ζ)) (ha : x ∈ aForm R) :
    ∃ u ∈ fePowSpan R, leftActOne R ratFunc_X_not_root ζ u = x := by
  obtain ⟨u, rfl⟩ := hx
  have ht : u • vermaTensorHwv R 𝕧 0 ζ ∈ vermaTensorLattice R 0 ζ := by
    apply (leftActOne_mem_aForm_iff 0 ζ u).1
    simpa using ha
  obtain ⟨u', hu', he⟩ := mem_fePowImage.1 (vermaTensorLattice_le_fePowImage ht)
  refine ⟨u', hu', ?_⟩
  have hz : (u' - u) • vermaTensorHwv R 𝕧 0 ζ = 0 := by rw [sub_smul, he, sub_self]
  have := (smul_vermaTensorHwv_eq_zero_iff ratFunc_X_not_root 0 ζ _).1 hz
  simpa only [sub_zero, map_sub, sub_eq_zero] using this

/-- **Lusztig §23.2.5**: the column comparison preserves and reflects integrality.
The source uses a simply connected datum; the same triangular-span argument applies to any
morphism of the existing root data. Neither regularity nor `hY` is required. -/
theorem columnEquiv_mem_aForm_iff (φ : R.Hom R') (ζ : Y' →+ ℤ)
    (x : LinearMap.range (leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom))) :
    (columnEquiv R R' ratFunc_X_not_root φ ζ x : Modified R' 𝕧) ∈ aForm R' ↔
      (x : Modified R 𝕧) ∈ aForm R := by
  constructor
  · intro hx
    obtain ⟨u', hu', he⟩ := exists_fePowSpan_leftActOne R' ζ
      (columnEquiv R R' ratFunc_X_not_root φ ζ x).property hx
    rw [← mapHom_fePowSpan R R' φ] at hu'
    obtain ⟨u, hu, rfl⟩ := hu'
    have hcol : columnEquiv R R' ratFunc_X_not_root φ ζ
        ((leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom)).rangeRestrict u) =
          columnEquiv R R' ratFunc_X_not_root φ ζ x := by
      apply Subtype.ext
      exact (columnEquiv_leftActOne R R' ratFunc_X_not_root φ ζ u).trans he
    have he' := (columnEquiv R R' ratFunc_X_not_root φ ζ).injective hcol
    rw [← he']
    exact leftActOne_mem_aForm_of_mem_fePowSpan _ hu
  · intro hx
    obtain ⟨u, hu, he⟩ := exists_fePowSpan_leftActOne R (ζ.comp φ.toHom) x.property hx
    have he' : (leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom)).rangeRestrict u = x :=
      Subtype.ext he
    rw [← he']
    change (columnEquiv R R' ratFunc_X_not_root φ ζ
      ⟨leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom) u, u, rfl⟩ : Modified R' 𝕧) ∈ _
    rw [columnEquiv_leftActOne]
    apply leftActOne_mem_aForm_of_mem_fePowSpan
    rw [← mapHom_fePowSpan R R' φ]
    exact ⟨u, hu, rfl⟩

local instance columnLaurentAlgebra : Algebra 𝒜 𝕂 := LusztigF.integralLaurentEval.toAlgebra

local instance columnLaurentTower (S : D.RootDatum Y) : IsScalarTower 𝒜 𝕂 (Modified S 𝕧) :=
  ⟨fun a c x ↦ mul_smul (LusztigF.integralLaurentEval a) c x⟩

/-- The intersection of the integral form with a right column. -/
def aColumn (ζ : Y →+ ℤ) :
    Submodule 𝒜 (LinearMap.range (leftActOne R ratFunc_X_not_root ζ)) :=
  (aForm R).toSubmodule.comap
    ((LinearMap.range (leftActOne R ratFunc_X_not_root ζ)).subtype.restrictScalars 𝒜)

/-- The integral restriction of the column comparison, Lusztig §23.2.5. -/
def aColumnEquiv (φ : R.Hom R') (ζ : Y' →+ ℤ) :
    aColumn R (ζ.comp φ.toHom) ≃ₗ[𝒜] aColumn R' ζ :=
  ((columnEquiv R R' ratFunc_X_not_root φ ζ).restrictScalars 𝒜).ofSubmodules
    (aColumn R (ζ.comp φ.toHom)) (aColumn R' ζ) <| by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (columnEquiv_mem_aForm_iff R R' φ ζ x).2 hx
      · intro hy
        change (y : Modified R' 𝕧) ∈ aForm R' at hy
        refine ⟨(columnEquiv R R' ratFunc_X_not_root φ ζ).symm y, ?_,
          (columnEquiv R R' ratFunc_X_not_root φ ζ).apply_symm_apply y⟩
        apply (columnEquiv_mem_aForm_iff R R' φ ζ _).1
        simpa using hy

@[simp] theorem aColumnEquiv_apply (φ : R.Hom R') (ζ : Y' →+ ℤ)
    (x : aColumn R (ζ.comp φ.toHom)) :
    (aColumnEquiv R R' φ ζ x : LinearMap.range (leftActOne R' ratFunc_X_not_root ζ)) =
      columnEquiv R R' ratFunc_X_not_root φ ζ x := rfl

/-- The root-datum map commutes with the bar involution. -/
lemma mapHom_barHom (φ : R.Hom R') (u : QuantumGroup R 𝕧) :
    QuantumGroup.mapHom 𝕧 φ (barHom R u) = barHom R' (QuantumGroup.mapHom 𝕧 φ u) := by
  induction u using QuantumGroup.induction_on with
  | algebraMap c => simp [barHom_algebraMap]
  | E i => simp
  | F i => simp
  | K μ => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [_root_.map_mul, hx, hy]

/-- The column comparison sends bar-fixed elements to bar-fixed elements. -/
theorem bar_columnEquiv_of_bar_eq (φ : R.Hom R') (ζ : Y' →+ ℤ)
    (x : LinearMap.range (leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom)))
    (hx : bar R x = x) :
    bar R' (columnEquiv R R' ratFunc_X_not_root φ ζ x) =
      (columnEquiv R R' ratFunc_X_not_root φ ζ x : Modified R' 𝕧) := by
  obtain ⟨_, u, rfl⟩ := x
  rw [bar_leftActOne] at hx
  have he : (⟨leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom) (barHom R u), _, rfl⟩ :
      LinearMap.range (leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom))) =
      ⟨leftActOne R ratFunc_X_not_root (ζ.comp φ.toHom) u, _, rfl⟩ := Subtype.ext hx
  have ht := congrArg (fun y ↦
    (columnEquiv R R' ratFunc_X_not_root φ ζ y : Modified R' 𝕧)) he
  rw [columnEquiv_leftActOne, columnEquiv_leftActOne, mapHom_barHom] at ht
  rw [columnEquiv_leftActOne, bar_leftActOne]
  exact ht

end LieLean.QuantumGroup.Modified

namespace LieLean.QuantumGroup
open GrandLoop LusztigF Modified
local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
attribute [local instance] neZero_ratFunc_X
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

omit [Finite I] [DecidableEq I] in
/-- The auxiliary free-coroot datum has arbitrarily large dominant weights. -/
lemma exists_dom_freeCoroot (N : ℕ) :
    ∃ Λ : Dom R.freeCoroot, ∀ i, (N : ℤ) ≤ Λ.1 (R.freeCoroot.coroot i) := by
  obtain ⟨Λ, hΛ⟩ := R.exists_le_freeCoroot N
  exact ⟨⟨Λ, fun i ↦ le_trans (Int.natCast_nonneg N) (hΛ i)⟩, hΛ⟩

/-- Column transport of the canonical element from the free-coroot auxiliary datum,
following the construction in Lusztig §25.2.2. This auxiliary datum is not the printed simply
connected datum: it preserves `IsXRegular`, and the generalized column comparison applies to
its projection to `R`. No sufficiently-large-dominant-weight hypothesis is required on `R`.
Agreement with `modifiedCanonical` is a separate comparison statement. -/
def Modified.columnCanonical (hR : R.IsXRegular) (ζ : Y →+ ℤ)
    {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) : Modified R 𝕧 :=
  columnEquiv R.freeCoroot R ratFunc_X_not_root R.freeCorootHom ζ
    ⟨modifiedCanonical (isXRegular_freeCoroot hR) exists_dom_freeCoroot
      (ζ.comp R.freeCorootHom.toHom) hb hb'',
      modifiedCanonical_mem_range (isXRegular_freeCoroot hR) exists_dom_freeCoroot
        (ζ.comp R.freeCorootHom.toHom) hb hb''⟩

/-- The transported element belongs to the specified right column. -/
theorem Modified.columnCanonical_mem_range (hR : R.IsXRegular) (ζ : Y →+ ℤ)
    {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) :
    columnCanonical hR ζ hb hb'' ∈ LinearMap.range (leftActOne R ratFunc_X_not_root ζ) :=
  (columnEquiv R.freeCoroot R ratFunc_X_not_root R.freeCorootHom ζ _).property

/-- The transported element is integral, by the integral restriction in §23.2.5. -/
theorem Modified.columnCanonical_mem_aForm (hR : R.IsXRegular) (ζ : Y →+ ℤ)
    {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) :
    columnCanonical hR ζ hb hb'' ∈ aForm R :=
  (columnEquiv_mem_aForm_iff R.freeCoroot R R.freeCorootHom ζ _).2
    (modifiedCanonical_mem_aForm (isXRegular_freeCoroot hR) exists_dom_freeCoroot _ hb hb'')

/-- The transported element is fixed by bar. -/
theorem Modified.bar_columnCanonical (hR : R.IsXRegular) (ζ : Y →+ ℤ)
    {b b'' : Um D 𝕧} (hb : b ∈ canonicalBasis D) (hb'' : b'' ∈ canonicalBasis D) :
    bar R (columnCanonical hR ζ hb hb'') = columnCanonical hR ζ hb hb'' :=
  bar_columnEquiv_of_bar_eq R.freeCoroot R R.freeCorootHom ζ _
    (bar_modifiedCanonical (isXRegular_freeCoroot hR) exists_dom_freeCoroot _ hb hb'')

end LieLean.QuantumGroup
