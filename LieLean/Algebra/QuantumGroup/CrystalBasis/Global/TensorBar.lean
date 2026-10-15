/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.CanonicalHighestWeight
import LieLean.Algebra.QuantumGroup.Modified.TensorQuotientQuasiR
import LieLean.Algebra.QuantumGroup.Modified.FormFunctional
import LieLean.Algebra.QuantumGroup.QuasiR.TensorInvolution

/-!
# The involution `Ψ` of `ʷΛ_λ ⊗ Λ_{λ'}`

For dominant `λ, λ'`, Lusztig defines a semilinear involution `Ψ = Θ ∘ (¯ ⊗ ¯)` of
`ʷΛ_λ ⊗ Λ_{λ'}` ([Lus] 24.3.1–24.3.2), from which he obtains the canonical basis of
`ʷΛ_λ ⊗ Λ_{λ'}` (24.3.3). This file constructs `Ψ` on `ʷL_q(λ) ⊗ L_q(λ')` and proves its
properties.

## Main definitions

* `twBar`: the bar involution `uξ ↦ ūξ` of `ʷL_q(λ)` ([Lus] 24.3.1).
* `tensorPsi`: `Ψ(x) = Θ(x̄)` on `ʷL_q(λ) ⊗ L_q(λ')` ([Lus] 24.3.2).

## Main results

* `hwBar_smul_U`: [Lus] 19.3.4, the bar involution of `L_q(λ)` satisfies `(u m)‾ = ū m̄` for all
  `u ∈ U`; `twBar_smul_U`: the same for `ʷL_q(λ)`.
* [Lus] 24.3.2: `tensorPsi_tensorPsi` (`Ψ² = 1`), `tensorPsi_smul` (`Ψ(c z) = c̄ Ψ(z)`),
  `act_tensorPsi` (`u Ψ(z) = Ψ(ū z)`).
* `actPair_quasiR_mem_tensorWt`, `actPair_quasiR_eq_zero`: the component `Θ_ν` maps
  `(ʷL_q(λ))_{-λ+μ} ⊗ L_q(λ')_{λ'-μ'}` into `(ʷL_q(λ))_{-λ+μ-ν} ⊗ L_q(λ')_{λ'-μ'+ν}`, and kills
  it unless `ν ≤ μ` and `ν ≤ μ'`: the triangularity used in [Lus] 24.3.2.

## Implementation notes

Lusztig's `ξ_{-λ} ∈ ʷΛ_λ` is `η_λ` viewed in the twist, so `b⁺ξ_{-λ} = b⁻η_λ` as vectors and
the weight spaces of `ʷL_q(λ)` are those of `L_q(λ)` (`hwWt`). The proof of 19.3.4 is our own: it
checks `(u m)‾ = ū m̄` on the generators of `U`, for `Eᵢ` by induction along `F`-words. As in
`(G.2)`, the root datum is `X`-regular, where Lusztig assumes it `Y`-regular.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 19.3.4, 24.1, 24.3.
-/

open scoped RatFunc
open TensorProduct

noncomputable section

universe u

namespace LieLean.QuantumGroup

open Sl2.RankOne GrandLoop LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "hvt" => transcendental_ratFunc_X

local instance : NeZero 𝕧 := ⟨RatFunc.X_ne_zero⟩

variable {I : Type u} [Finite I] [DecidableEq I] {D : LusztigCartanDatum I}
  {Y : Type*} [AddCommGroup Y] {R : D.RootDatum Y} (hR : R.IsXRegular)

/-! ### [Lus] 19.3.4 -/

section BarCompat

omit [Finite I] in
lemma bar_X_zpow (n : ℤ) : RatFunc.bar (𝕧 ^ n) = 𝕧 ^ (-n) := by
  rw [map_zpow₀, RatFunc.bar_X, inv_zpow']

omit [Finite I] in
/-- Induction along `F`-words on `L_q(λ)`. -/
lemma hw_induction (Λ : Y →+ ℤ) {P : IrreducibleModule R 𝕧 Λ → Prop}
    (m : IrreducibleModule R 𝕧 Λ) (zero : P 0) (add : ∀ a b, P a → P b → P (a + b))
    (smul : ∀ (c : 𝕂) a, P a → P (c • a)) (hwv : P (IrreducibleModule.hwv R 𝕧 Λ))
    (F : ∀ i a, P a → P (F R 𝕧 i • a)) : P m := by
  obtain ⟨y, rfl⟩ := (Submodule.mkQ_surjective _).comp
    (VermaModule.toVerma_surjective (R := R) (Λ := Λ) hvn_ratFunc) m
  have hy : y ∈ Submodule.span 𝕂 (Set.range (FreeAlgebra.wordBasis 𝕂 I)) := by
    rw [(FreeAlgebra.wordBasis 𝕂 I).span_eq]
    trivial
  change P (ev R 𝕧 Λ y)
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    rw [← monomial_eq_wordBasis]
    induction w with
    | nil =>
      change P (ev R 𝕧 Λ 1)
      rw [ev_one]
      exact hwv
    | cons i w ih =>
      rw [ev_monomial_cons]
      exact F i _ ih
  | zero => rw [map_zero]; exact zero
  | add a b _ _ ha hb => rw [map_add]; exact add _ _ ha hb
  | smul c a _ ha => rw [map_smul]; exact smul c _ ha

variable (Λ : Dom R)

omit [Finite I] in
lemma hw_K_smul_hwv (μ : Y) :
    K R 𝕧 μ • IrreducibleModule.hwv R 𝕧 Λ.1 = 𝕧 ^ Λ.1 μ • IrreducibleModule.hwv R 𝕧 Λ.1 := by
  rw [IrreducibleModule.hwv, ← Submodule.Quotient.mk_smul, VermaModule.K_smul_hwv,
    Submodule.Quotient.mk_smul]

lemma hwBar_F_smul (i : I) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwBar hR Λ (F R 𝕧 i • m) = F R 𝕧 i • hwBar hR Λ m := by
  obtain ⟨y, rfl⟩ := ev_surjective Λ m
  rw [← ev_ι_mul, hwBar_ev, hwBar_ev, map_mul, ← θ, bar_θ, θ, ev_ι_mul]

lemma hwBar_K_smul (μ : Y) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwBar hR Λ (K R 𝕧 μ • m) = K R 𝕧 (-μ) • hwBar hR Λ m := by
  induction m using hw_induction with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | smul c a ha => rw [smul_comm, hwBar_smul, ha, hwBar_smul, smul_comm]
  | hwv =>
    rw [hw_K_smul_hwv, hwBar_smul, hwBar_hwv, hw_K_smul_hwv, bar_X_zpow, map_neg]
  | F i a ha =>
    rw [← mul_smul, K_mul_F, smul_assoc, mul_smul, hwBar_smul, hwBar_F_smul, ha,
      hwBar_F_smul, ← mul_smul (K R 𝕧 (-μ)), K_mul_F, smul_assoc, mul_smul, bar_X_zpow,
      map_neg]

omit [Finite I] [DecidableEq I] in
lemma bar_qInv (i : I) :
    RatFunc.bar ((𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹) = -(𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ := by
  rw [map_inv₀, map_sub, map_inv₀, map_pow, RatFunc.bar_X, inv_pow, inv_inv, ← neg_sub,
    inv_neg]

lemma hwBar_E_smul (i : I) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwBar hR Λ (E R 𝕧 i • m) = E R 𝕧 i • hwBar hR Λ m := by
  induction m using hw_induction with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | smul c a ha => rw [smul_comm, hwBar_smul, ha, hwBar_smul, smul_comm]
  | hwv => rw [IrreducibleModule.E_smul_hwv, hwBar_hwv, map_zero, IrreducibleModule.E_smul_hwv]
  | F j a ha =>
    have key : ∀ x : IrreducibleModule R 𝕧 Λ.1, E R 𝕧 i • F R 𝕧 j • x =
        F R 𝕧 j • E R 𝕧 i • x + (if i = j then
          (𝕧 ^ D.d i - (𝕧 ^ D.d i)⁻¹)⁻¹ • (Kt R 𝕧 i • x - K R 𝕧 (-ktilde R i) • x) else 0) := by
      intro x
      rw [← mul_smul, ← mul_smul, ← sub_eq_iff_eq_add', ← sub_smul, E_mul_F_sub]
      split_ifs
      · rw [smul_assoc, sub_smul]
      · rw [zero_smul]
    rw [key, map_add, hwBar_F_smul hR Λ j (E R 𝕧 i • a), ha, hwBar_F_smul hR Λ j a, key]
    congr 1
    split_ifs
    · rw [Kt, hwBar_smul, map_sub, hwBar_K_smul, hwBar_K_smul, bar_qInv, neg_neg, neg_smul,
        ← smul_neg, neg_sub]
    · rw [map_zero]

/-- **[Lus] 19.3.4**: the bar involution of `L_q(λ)` satisfies `(u m)‾ = ū m̄` for all `u ∈ U`.
Lusztig defines the involution by this property; here it is defined by `(y⁻η)‾ = ȳ⁻η`
(`hwBar_ev`), and the property is our own proof. -/
theorem hwBar_smul_U (u : QuantumGroup R 𝕧) (m : IrreducibleModule R 𝕧 Λ.1) :
    hwBar hR Λ (u • m) = barHom R u • hwBar hR Λ m := by
  induction u using QuantumGroup.induction_on generalizing m with
  | algebraMap c => rw [algebraMap_smul, hwBar_smul, barHom_algebraMap, algebraMap_smul]
  | E i => rw [hwBar_E_smul, barHom_E]
  | F i => rw [hwBar_F_smul, barHom_F]
  | K μ => rw [hwBar_K_smul, barHom_K]
  | add x y hx hy => rw [add_smul, map_add, hx, hy, map_add, add_smul]
  | mul x y hx hy => rw [mul_smul, hx, hy, map_mul, mul_smul]

end BarCompat

/-! ### The bar involution of `ʷL_q(λ)` -/

section Twist

variable (Λ : Dom R)

/-- `ʷL_q(λ)`, the twist of `L_q(λ)` by the Chevalley involution: Lusztig's `ʷΛ_λ`. -/
abbrev TwL : Type _ := ChevalleyTwist R 𝕧 (IrreducibleModule R 𝕧 Λ.1)

/-- The bar involution `uξ ↦ ūξ` of `ʷL_q(λ)` ([Lus] 24.3.1). -/
def twBar : TwL Λ →+ TwL Λ :=
  (ChevalleyTwist.toTwist R 𝕧 _).toAddMonoidHom.comp
    ((hwBar hR Λ).toAddMonoidHom.comp (ChevalleyTwist.toTwist R 𝕧 _).symm.toAddMonoidHom)

lemma twBar_toTwist (m : IrreducibleModule R 𝕧 Λ.1) :
    twBar hR Λ (ChevalleyTwist.toTwist R 𝕧 _ m) = ChevalleyTwist.toTwist R 𝕧 _ (hwBar hR Λ m) :=
  rfl

lemma twBar_twBar (m : TwL Λ) : twBar hR Λ (twBar hR Λ m) = m := by
  obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 _).surjective m
  rw [twBar_toTwist, twBar_toTwist, hwBar_hwBar]

/-- `(u x)‾ = ū x̄` on `ʷL_q(λ)`. -/
theorem twBar_smul_U (u : QuantumGroup R 𝕧) (m : TwL Λ) :
    twBar hR Λ (u • m) = barHom R u • twBar hR Λ m := by
  obtain ⟨m, rfl⟩ := (ChevalleyTwist.toTwist R 𝕧 _).surjective m
  rw [ChevalleyTwist.smul_toTwist, twBar_toTwist, hwBar_smul_U, barHom_chevalley, twBar_toTwist,
    ChevalleyTwist.smul_toTwist]

end Twist

/-! ### The involution `Ψ` -/

section Psi

variable (Λ Λ' : Dom R)

/-- `L_q(λ')` has the finiteness property of [Lus] 3.4.7 needed to define `Θ`. -/
lemma isPlusLocallyNilpotent_hw : IsPlusLocallyNilpotent R (IrreducibleModule R 𝕧 Λ'.1) :=
  Modified.isPlusLocallyNilpotent_quot (R := R) _

lemma hwBar_smul_U' (u : QuantumGroup R 𝕧) (m : IrreducibleModule R 𝕧 Λ'.1) :
    (hwBar hR Λ').toAddMonoidHom (u • m) = barHom R u • (hwBar hR Λ').toAddMonoidHom m :=
  hwBar_smul_U hR Λ' u m

/-- **[Lus] 24.3.2**: the map `Ψ(x) = Θ(x̄)` of `ʷL_q(λ) ⊗ L_q(λ')`, where `¯ = ¯ ⊗ ¯`. -/
def tensorPsi : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1 →+ TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1 :=
  (quasiRAct (isPlusLocallyNilpotent_hw Λ')).toAddMonoidHom.comp
    (barPair (twBar hR Λ) (hwBar hR Λ').toAddMonoidHom (twBar_smul_U hR Λ)
      (hwBar_smul_U' hR Λ'))

lemma tensorPsi_apply (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :
    tensorPsi hR Λ Λ' z = quasiRAct (isPlusLocallyNilpotent_hw Λ')
      (barPair (twBar hR Λ) (hwBar hR Λ').toAddMonoidHom (twBar_smul_U hR Λ)
        (hwBar_smul_U' hR Λ') z) := rfl

/-- **[Lus] 24.3.2**: `Ψ² = 1`. -/
theorem tensorPsi_tensorPsi (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :
    tensorPsi hR Λ Λ' (tensorPsi hR Λ Λ' z) = z :=
  quasiRAct_barPair_involutive _ _ _ _ (isPlusLocallyNilpotent_hw Λ') (twBar_twBar hR Λ)
    (hwBar_hwBar hR Λ') z

/-- **[Lus] 24.3.2**: `Ψ(c z) = c̄ Ψ(z)`. -/
theorem tensorPsi_smul (c : 𝕂) (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :
    tensorPsi hR Λ Λ' (c • z) = RatFunc.bar c • tensorPsi hR Λ Λ' z := by
  rw [tensorPsi_apply, tensorPsi_apply, ← LinearMap.map_smul]
  congr 1
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul x y =>
    rw [smul_tmul', barPair_tmul, barPair_tmul, smul_tmul',
      map_smul_of_barHom _ (twBar_smul_U hR Λ)]

/-- **[Lus] 24.3.2** (via 24.1.3): `u Ψ(z) = Ψ(ū z)` for `u ∈ U`. -/
theorem act_tensorPsi (u : QuantumGroup R 𝕧) (z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :
    TensorModule.act R 𝕧 _ _ u (tensorPsi hR Λ Λ' z) =
      tensorPsi hR Λ Λ' (TensorModule.act R 𝕧 _ _ (barHom R u) z) :=
  act_quasiRAct_barPair _ _ _ _ (isPlusLocallyNilpotent_hw Λ') u z

end Psi

/-! ### Triangularity of `Θ` -/

section Weights

variable (Λ : Dom R)

/-- The weight space `L_q(λ)_{λ-μ}`; in `ʷL_q(λ)` it is the weight space of weight `-λ+μ`. -/
abbrev hwWt (μ : I →₀ ℕ) : Submodule 𝕂 (IrreducibleModule R 𝕧 Λ.1) :=
  weightSpace R 𝕧 (IrreducibleModule R 𝕧 Λ.1) (Λ.1 - R.rootSum μ)

omit [Finite I] in
lemma plusHom_mem_adWeightSpace {ν : I →₀ ℕ} {x : LusztigF 𝕂 I}
    (hx : x ∈ LusztigF.weightSpace 𝕂 ν) : plusHom R 𝕧 x ∈ adWeightSpace R 𝕧 (R.rootSum ν) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl, rfl⟩ := hy
    rw [← wordChar_eq_rootSum]
    exact plusHom_monomial_mem_adWeightSpace w
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

omit [Finite I] in
lemma hwWt_eq_bot {Λ' : Y →+ ℤ} (h : ∀ ν, Λ' ≠ Λ.1 - R.rootSum ν) :
    weightSpace R 𝕧 (IrreducibleModule R 𝕧 Λ.1) Λ' = ⊥ := by
  refine eq_bot_iff.2 ((weightSpace_quotient_le_map hvn_ratFunc
    VermaModule.iSup_weightSpace_eq_top _ Λ').trans ?_)
  rw [VermaModule.weightSpace_eq_bot hvn_ratFunc h, Submodule.map_bot]

omit [Finite I] in
/-- `x⁺ L_q(λ)_{λ-μ} ⊆ L_q(λ)_{λ-μ+ν}` for `x ∈ f_ν`, `ν ≤ μ`. -/
lemma plusHom_smul_mem_hwWt {ν μ : I →₀ ℕ} (hνμ : ν ≤ μ) {x : LusztigF 𝕂 I}
    (hx : x ∈ LusztigF.weightSpace 𝕂 ν) {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwWt Λ μ) :
    plusHom R 𝕧 x • m ∈ hwWt Λ (μ - ν) := by
  have h := Modified.smul_mem_weightSpace_of_mem_adWeightSpace (plusHom_mem_adWeightSpace hx) hm
  have hμ : R.rootSum μ = R.rootSum (μ - ν) + R.rootSum ν := by
    rw [← R.rootSum_add, tsub_add_cancel_of_le hνμ]
  have e : R.rootSum ν + (Λ.1 - R.rootSum μ) = Λ.1 - R.rootSum (μ - ν) := by
    rw [hμ]; abel
  rwa [e] at h

omit [Finite I] in
include hR in
/-- `x⁺ L_q(λ)_{λ-μ} = 0` for `x ∈ f_ν` unless `ν ≤ μ`. -/
lemma plusHom_smul_hwWt_eq_zero {ν μ : I →₀ ℕ} (hνμ : ¬ ν ≤ μ) {x : LusztigF 𝕂 I}
    (hx : x ∈ LusztigF.weightSpace 𝕂 ν) {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwWt Λ μ) :
    plusHom R 𝕧 x • m = 0 := by
  have h := Modified.smul_mem_weightSpace_of_mem_adWeightSpace (plusHom_mem_adWeightSpace hx) hm
  rwa [hwWt_eq_bot Λ fun κ hκ ↦ hνμ ?_, Submodule.mem_bot] at h
  have : R.rootSum (κ + ν) = R.rootSum μ := by
    rw [R.rootSum_add, ← sub_eq_zero]
    rw [← sub_eq_zero] at hκ
    rw [← hκ]
    abel
  rw [← LusztigCartanDatum.RootDatum.rootSum_injective hR this]
  exact le_add_self

variable (Λ' : Dom R)

/-- The subspace `(ʷL_q(λ))_{-λ+μ} ⊗ L_q(λ')_{λ'-μ'}` of `ʷL_q(λ) ⊗ L_q(λ')`. -/
def tensorWt (μ μ' : I →₀ ℕ) : Submodule 𝕂 (TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1) :=
  LinearMap.range (TensorProduct.map
    ((ChevalleyTwist.toTwist R 𝕧 _).toLinearMap ∘ₗ (hwWt Λ μ).subtype) (hwWt Λ' μ').subtype)

omit [Finite I] in
lemma tmul_mem_tensorWt {μ μ' : I →₀ ℕ} {m : IrreducibleModule R 𝕧 Λ.1} (hm : m ∈ hwWt Λ μ)
    {m' : IrreducibleModule R 𝕧 Λ'.1} (hm' : m' ∈ hwWt Λ' μ') :
    ChevalleyTwist.toTwist R 𝕧 _ m ⊗ₜ[𝕂] m' ∈ tensorWt Λ Λ' μ μ' :=
  ⟨⟨m, hm⟩ ⊗ₜ ⟨m', hm'⟩, rfl⟩

/-- `Θ_ν` is a sum of `x⁻ ⊗ y⁺` with `x, y ∈ 'f_ν`. -/
lemma quasiR_mem_span (ν : I →₀ ℕ) :
    quasiR R ν ∈ Submodule.span 𝕂 {t | ∃ x ∈ LusztigF.weightSpace 𝕂 ν,
      ∃ y ∈ LusztigF.weightSpace 𝕂 ν, t = minusHom R 𝕧 x ⊗ₜ[𝕂] plusHom R 𝕧 y} := by
  obtain ⟨t, ht⟩ := quasiR_mem_range R ν
  rw [← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | tmul a b =>
    obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    exact Submodule.subset_span ⟨x, hx, y, hy, by simp⟩

/-- **Triangularity of `Θ`** ([Lus] 24.3.2): for `ν ≤ μ`, `ν ≤ μ'`, `Θ_ν` maps
`(ʷL_q(λ))_{-λ+μ} ⊗ L_q(λ')_{λ'-μ'}` into `(ʷL_q(λ))_{-λ+μ-ν} ⊗ L_q(λ')_{λ'-μ'+ν}`. -/
theorem actPair_quasiR_mem_tensorWt {ν μ μ' : I →₀ ℕ} (hμ : ν ≤ μ) (hμ' : ν ≤ μ')
    {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} (hz : z ∈ tensorWt Λ Λ' μ μ') :
    TensorModule.actPair R 𝕧 (TwL Λ) (IrreducibleModule R 𝕧 Λ'.1) (quasiR R ν) z ∈
      tensorWt Λ Λ' (μ - ν) (μ' - ν) := by
  obtain ⟨z, rfl⟩ := hz
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
  | tmul m m' =>
    have hq := quasiR_mem_span (R := R) ν
    generalize quasiR R ν = q at hq ⊢
    induction hq using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ht
      simp only [TensorProduct.map_tmul, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, LinearEquiv.coe_coe]
      rw [TensorModule.act_tmul, ChevalleyTwist.smul_toTwist, chevalley_minusHom]
      exact tmul_mem_tensorWt Λ Λ' (plusHom_smul_mem_hwWt Λ hμ hx m.2)
        (plusHom_smul_mem_hwWt Λ' hμ' hy m'.2)
    | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c ha

include hR in
/-- `Θ_ν` kills `(ʷL_q(λ))_{-λ+μ} ⊗ L_q(λ')_{λ'-μ'}` unless `ν ≤ μ` and `ν ≤ μ'`. -/
theorem actPair_quasiR_eq_zero {ν μ μ' : I →₀ ℕ} (h : ¬ (ν ≤ μ ∧ ν ≤ μ'))
    {z : TwL Λ ⊗[𝕂] IrreducibleModule R 𝕧 Λ'.1} (hz : z ∈ tensorWt Λ Λ' μ μ') :
    TensorModule.actPair R 𝕧 (TwL Λ) (IrreducibleModule R 𝕧 Λ'.1) (quasiR R ν) z = 0 := by
  obtain ⟨z, rfl⟩ := hz
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul m m' =>
    have hq := quasiR_mem_span (R := R) ν
    generalize quasiR R ν = q at hq ⊢
    induction hq using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, hx, y, hy, rfl⟩ := ht
      simp only [TensorProduct.map_tmul, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, LinearEquiv.coe_coe]
      rw [TensorModule.act_tmul, ChevalleyTwist.smul_toTwist, chevalley_minusHom]
      rcases not_and_or.1 h with h | h
      · rw [plusHom_smul_hwWt_eq_zero hR Λ h hx m.2, LinearEquiv.map_zero, zero_tmul]
      · rw [plusHom_smul_hwWt_eq_zero hR Λ' h hy m'.2, tmul_zero]
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]

end Weights

end LieLean.QuantumGroup
