/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWSymm
import LieLean.Algebra.QuantumGroup.Modified.Symmetries

/-!
# Integral PBW bases for `T'_{i,1}` and `T''_{i,-1}` ([Lus] 41.1.4)

Over `ℚ(v)`, `𝒜 = ℤ[v, v⁻¹]`, along a word `ω = i₁ ⋯ iₙ`:

* `Modified.pbwDivPrime ω`: the monomials `E_{i₁}^{(c₁)} T'_{i₁,1}(E_{i₂}^{(c₂)}) ⋯` of
  [Lus] 41.1.4 (a) for `e = 1`;
* `Modified.pbwDivPrimeSymm ω`: the monomials `E_{i₁}^{(c₁)} T''_{i₁,-1}(E_{i₂}^{(c₂)}) ⋯` of
  [Lus] 41.1.4 (b) for `e = -1`.

By [Lus] 37.2.4 each of them is `±v^m` times the corresponding monomial for `T''_{i,1}`
(`pbwDiv`, 41.1.4 (b), `e = 1`) resp. `T'_{i,-1}` (`pbwDivSymm`, 41.1.4 (a), `e = -1`)
(`exists_pbwDivPrime_eq_smul`, `exists_pbwDivPrimeSymm_eq_smul`). Hence they are `𝒜`-linearly
independent along reduced words, for every Cartan datum, and span the same `𝒜`-submodule
`𝒜U⁺(w, e)` (`span_pbwDivPrime`, `span_pbwDivPrimeSymm`). With the simply-laced results of
`Modified/IntegralPBW.lean` and `Modified/IntegralPBWSymm.lean` this completes [Lus] 41.1.4 (a),
(b), (c) for both signs of `e`, and 41.1.7 for both signs, in simply-laced (finite) type
(`span_pbwDivPrime_of_isReduced`, `span_pbwDivPrimeSymm_of_isReduced`,
`coe_span_pbwDivPrime_longest`, `coe_span_pbwDivPrimeSymm_longest`).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 37.2.4, 41.1.4, 41.1.7.
-/

open LieLean Finset

noncomputable section

namespace LieLean.QuantumGroup

local notation "𝕂" => RatFunc ℚ
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)
local notation "𝒜" => LaurentPolynomial ℤ

attribute [local instance] neZero_ratFunc_X

variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

namespace Modified

attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

/-! ### Diagonal automorphisms on the PBW monomials -/

/-- A diagonal automorphism with scalars `±v^m` multiplies each monomial `pbwDiv ω c` by `±v^m`. -/
lemma exists_diagHom_pbwDiv (ω : List I) (c : Fin ω.length → ℕ) {χ : I → 𝕂ˣ}
    (hχ : IsSignPow 𝕧 χ) :
    ∃ e m : ℤ, diagHom R 𝕧 χ (pbwDiv R ω c) = ((-1) ^ e * 𝕧 ^ m) • pbwDiv R ω c := by
  induction ω generalizing χ with
  | nil => exact ⟨0, 0, by simp [CoxeterSystem.pbwDivMonomial]⟩
  | cons i ω ih =>
    obtain ⟨e, m, he⟩ := ih (fun n ↦ c n.succ) (hχ.reflChar i)
    obtain ⟨e', m', he'⟩ := hχ i
    refine ⟨e' * c 0 + e, m' * c 0 + m, ?_⟩
    have H := diagHom_comp_of_hasImages (braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i) χ
    rw [pbwDiv, CoxeterSystem.pbwDivMonomial_cons, _root_.map_mul, Ta_apply]
    rw [show diagHom R 𝕧 χ (braidEquivOfNotRoot R ratFunc_X_not_root i
        (CoxeterSystem.pbwDivMonomial (Ta R) (Ed R) ω fun n ↦ c n.succ)) =
        braidEquivOfNotRoot R ratFunc_X_not_root i (diagHom R 𝕧 (reflChar D i χ)
          (CoxeterSystem.pbwDivMonomial (Ta R) (Ed R) ω fun n ↦ c n.succ)) from
      DFunLike.congr_fun H _]
    rw [he, map_smul, Ed, diagHom_qDivPow_E, he', smul_mul_smul_comm, ← Ta_apply]
    congr 1
    rw [mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      zpow_add₀ (neg_ne_zero.2 one_ne_zero), zpow_add₀ (NeZero.ne 𝕧)]
    simp only [Fin.zero_eta]
    ring

/-- A diagonal automorphism with scalars `±v^m` multiplies each monomial `pbwDivSymm ω c` by
`±v^m`. -/
lemma exists_diagHom_pbwDivSymm (ω : List I) (c : Fin ω.length → ℕ) {χ : I → 𝕂ˣ}
    (hχ : IsSignPow 𝕧 χ) :
    ∃ e m : ℤ, diagHom R 𝕧 χ (pbwDivSymm R ω c) = ((-1) ^ e * 𝕧 ^ m) • pbwDivSymm R ω c := by
  induction ω generalizing χ with
  | nil => exact ⟨0, 0, by simp [CoxeterSystem.pbwDivMonomial]⟩
  | cons i ω ih =>
    obtain ⟨e, m, he⟩ := ih (fun n ↦ c n.succ) (hχ.reflChar i)
    obtain ⟨e', m', he'⟩ := hχ i
    refine ⟨e' * c 0 + e, m' * c 0 + m, ?_⟩
    rw [pbwDivSymm, CoxeterSystem.pbwDivMonomial_cons, _root_.map_mul, Ta_symm_apply,
      diagHom_symm_apply_of_hasImages (braidEquivOfNotRoot_hasImages ratFunc_X_not_root R i)]
    rw [he, map_smul, Ed, diagHom_qDivPow_E, he', smul_mul_smul_comm, ← Ta_symm_apply]
    congr 1
    rw [mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      zpow_add₀ (neg_ne_zero.2 one_ne_zero), zpow_add₀ (NeZero.ne 𝕧)]
    simp only [Fin.zero_eta]
    ring

/-! ### The monomials for `T'_{i,1}` and `T''_{i,-1}` -/

variable (R) in
/-- `T'_{i,1}` as an `𝒜`-algebra automorphism of `U`. -/
def TaPrime (i : I) : QuantumGroup R 𝕧 ≃ₐ[𝒜] QuantumGroup R 𝕧 :=
  (braidPrimeEquiv R ratFunc_X_not_root i).restrictScalars 𝒜

lemma TaPrime_apply (i : I) (x : QuantumGroup R 𝕧) :
    TaPrime R i x = braidPrimeEquiv R ratFunc_X_not_root i x := rfl

lemma TaPrime_symm_apply (i : I) (x : QuantumGroup R 𝕧) :
    (TaPrime R i).symm x = (braidPrimeEquiv R ratFunc_X_not_root i).symm x := rfl

variable (R) in
/-- **The integral PBW monomials for `T'_{i,1}`**: `E_{i₁}^{(c₁)} T'_{i₁,1}(E_{i₂}^{(c₂)}) ⋯`
([Lus] 41.1.4 (a), `e = 1`). -/
abbrev pbwDivPrime (ω : List I) : (Fin ω.length → ℕ) → QuantumGroup R 𝕧 :=
  CoxeterSystem.pbwDivMonomial (TaPrime R) (Ed R) ω

variable (R) in
/-- **The integral PBW monomials for `T''_{i,-1}`**: `E_{i₁}^{(c₁)} T''_{i₁,-1}(E_{i₂}^{(c₂)}) ⋯`
([Lus] 41.1.4 (b), `e = -1`). -/
abbrev pbwDivPrimeSymm (ω : List I) : (Fin ω.length → ℕ) → QuantumGroup R 𝕧 :=
  CoxeterSystem.pbwDivMonomial (fun i ↦ (TaPrime R i).symm) (Ed R) ω

/-- Each `T'_{i,1}`-monomial is `±v^m` times the corresponding `T''_{i,1}`-monomial. -/
lemma exists_pbwDivPrime_eq_smul (ω : List I) (c : Fin ω.length → ℕ) :
    ∃ e m : ℤ, pbwDivPrime R ω c = ((-1) ^ e * 𝕧 ^ m) • pbwDiv R ω c := by
  induction ω with
  | nil => exact ⟨0, 0, by simp [CoxeterSystem.pbwDivMonomial]⟩
  | cons i ω ih =>
    obtain ⟨e, m, he⟩ := ih (fun n ↦ c n.succ)
    obtain ⟨e', m', he'⟩ := exists_diagHom_pbwDiv (R := R) ω (fun n ↦ c n.succ)
      (isSignPow_chevalleyScalar_zpow (D := D) (v := 𝕧) i (D.cartanMatrix i)).inv
    refine ⟨e + e', m + m', ?_⟩
    rw [pbwDivPrime, CoxeterSystem.pbwDivMonomial_cons, pbwDiv, CoxeterSystem.pbwDivMonomial_cons,
      TaPrime_apply, ← pbwDivPrime, he, map_smul,
      braidPrimeEquiv_eq_braidEquivOfNotRoot_diagHom ratFunc_X_not_root,
      show braidSign D 𝕧 i = fun j ↦ chevalleyScalar D 𝕧 i ^ D.cartanMatrix i j from rfl,
      he', map_smul, smul_smul, mul_smul_comm, ← Ta_apply]
    congr 1
    rw [zpow_add₀ (neg_ne_zero.2 one_ne_zero), zpow_add₀ (NeZero.ne 𝕧)]
    ring

/-- Each `T''_{i,-1}`-monomial is `±v^m` times the corresponding `T'_{i,-1}`-monomial. -/
lemma exists_pbwDivPrimeSymm_eq_smul (ω : List I) (c : Fin ω.length → ℕ) :
    ∃ e m : ℤ, pbwDivPrimeSymm R ω c = ((-1) ^ e * 𝕧 ^ m) • pbwDivSymm R ω c := by
  induction ω with
  | nil => exact ⟨0, 0, by simp [CoxeterSystem.pbwDivMonomial]⟩
  | cons i ω ih =>
    obtain ⟨e, m, he⟩ := ih (fun n ↦ c n.succ)
    obtain ⟨e', m', he'⟩ := exists_diagHom_pbwDivSymm (R := R) (i :: ω) c
      (isSignPow_chevalleyScalar_zpow (D := D) (v := 𝕧) i (D.cartanMatrix i))
    set M := pbwDivSymm R ω (fun n ↦ c n.succ)
    set E0 := qDivPow (𝕧 ^ D.d i) (c 0) (E R 𝕧 i)
    set Tinv := (braidEquivOfNotRoot R ratFunc_X_not_root i).symm
    set b := braidSign D 𝕧 i
    have hb : ((b i : 𝕂ˣ) : 𝕂) = 𝕧 ^ (2 * (D.d i : ℤ)) := by
      simp only [b, braidSign, D.cartanMatrix_self, chevalleyScalar, Units.val_zpow_eq_zpow_val,
        Units.val_mk0]
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, neg_sq, ← pow_mul, mul_comm,
        ← zpow_natCast]
      push_cast; ring_nf
    have hb0 : ((b i : 𝕂ˣ) : 𝕂) ^ c 0 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    have hsplit : pbwDivSymm R (i :: ω) c = E0 * Tinv M := rfl
    have h1 : ((b i : 𝕂ˣ) : 𝕂) ^ c 0 • (E0 * diagHom R 𝕧 b (Tinv M)) =
        ((-1) ^ e' * 𝕧 ^ m') • (E0 * Tinv M) := by
      rw [← hsplit, ← he', hsplit, _root_.map_mul, diagHom_qDivPow_E, smul_mul_assoc]
      rfl
    have h2 : E0 * diagHom R 𝕧 b (Tinv M) =
        ((((b i : 𝕂ˣ) : 𝕂) ^ c 0)⁻¹ * ((-1) ^ e' * 𝕧 ^ m')) • (E0 * Tinv M) := by
      rw [← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ hb0, one_smul]
    refine ⟨e + e', m + m' - 2 * D.d i * c 0, ?_⟩
    change E0 * (TaPrime R i).symm (pbwDivPrimeSymm R ω fun n ↦ c n.succ) = _
    rw [hsplit, TaPrime_symm_apply, he, map_smul,
      braidPrimeEquiv_symm_eq_diagHom_symm ratFunc_X_not_root, mul_smul_comm]
    change ((-1) ^ e * 𝕧 ^ m) • (E0 * diagHom R 𝕧 b (Tinv M)) = _
    rw [h2, smul_smul, hb]
    congr 1
    rw [zpow_add₀ (neg_ne_zero.2 one_ne_zero), zpow_sub₀ (NeZero.ne 𝕧),
      zpow_add₀ (NeZero.ne 𝕧), ← zpow_natCast, ← zpow_mul]
    ring

/-! ### Unit rescaling -/

lemma exists_unit_eval (e m : ℤ) :
    ∃ u : 𝒜ˣ, LusztigF.integralLaurentEval (u : 𝒜) = (-1) ^ e * 𝕧 ^ m := by
  have h1 : LaurentPolynomial.T m * LaurentPolynomial.T (-m) = (1 : 𝒜) := by
    rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  have h2 : LaurentPolynomial.T (-m) * LaurentPolynomial.T m = (1 : 𝒜) := by
    rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
  have hT : LusztigF.integralLaurentEval (LaurentPolynomial.T m) = 𝕧 ^ m := by
    simp
  rcases Int.even_or_odd e with he | he
  · exact ⟨⟨_, _, h1, h2⟩, by rw [he.neg_one_zpow, one_mul]; exact hT⟩
  · exact ⟨-⟨_, _, h1, h2⟩, by
      rw [he.neg_one_zpow, Units.val_neg, map_neg, neg_one_mul]; exact congrArg _ hT⟩

lemma span_range_eq_of_units_smul {ι : Type*} {f g : ι → QuantumGroup R 𝕧} (u : ι → 𝒜ˣ)
    (h : ∀ c, f c = u c • g c) :
    Submodule.span 𝒜 (Set.range f) = Submodule.span 𝒜 (Set.range g) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, rfl⟩
    rw [h, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  · rintro _ ⟨c, rfl⟩
    rw [show g c = (u c)⁻¹ • f c by rw [h, smul_smul, inv_mul_cancel, one_smul], Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

lemma exists_units_pbwDivPrime (ω : List I) :
    ∃ u : (Fin ω.length → ℕ) → 𝒜ˣ, ∀ c, pbwDivPrime R ω c = u c • pbwDiv R ω c := by
  choose e m he using exists_pbwDivPrime_eq_smul (R := R) ω
  choose u hu using fun c ↦ exists_unit_eval (e c) (m c)
  exact ⟨u, fun c ↦ by rw [Units.smul_def, laurent_smul_U, hu, he]⟩

lemma exists_units_pbwDivPrimeSymm (ω : List I) :
    ∃ u : (Fin ω.length → ℕ) → 𝒜ˣ, ∀ c, pbwDivPrimeSymm R ω c = u c • pbwDivSymm R ω c := by
  choose e m he using exists_pbwDivPrimeSymm_eq_smul (R := R) ω
  choose u hu using fun c ↦ exists_unit_eval (e c) (m c)
  exact ⟨u, fun c ↦ by rw [Units.smul_def, laurent_smul_U, hu, he]⟩

/-! ### [Lus] 41.1.4 for `T'_{i,1}` and `T''_{i,-1}` -/

/-- The `T'_{i,1}`-monomials span the same `𝒜`-submodule `𝒜U⁺(w, 1)` as the `T''_{i,1}`-monomials
(for any word). -/
theorem span_pbwDivPrime (ω : List I) :
    Submodule.span 𝒜 (Set.range (pbwDivPrime R ω)) =
      Submodule.span 𝒜 (Set.range (pbwDiv R ω)) := by
  obtain ⟨u, hu⟩ := exists_units_pbwDivPrime (R := R) ω
  exact span_range_eq_of_units_smul u hu

/-- The `T''_{i,-1}`-monomials span the same `𝒜`-submodule `𝒜U⁺(w, -1)` as the
`T'_{i,-1}`-monomials (for any word). -/
theorem span_pbwDivPrimeSymm (ω : List I) :
    Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R ω)) =
      Submodule.span 𝒜 (Set.range (pbwDivSymm R ω)) := by
  obtain ⟨u, hu⟩ := exists_units_pbwDivPrimeSymm (R := R) ω
  exact span_range_eq_of_units_smul u hu

/-- The `T'_{i,1}`-monomials are `𝒜`-linearly independent along reduced words (every Cartan
datum). -/
theorem linearIndependent_pbwDivPrime
    {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W} {ω : List I}
    (hω : cs.IsReduced ω) : LinearIndependent 𝒜 (pbwDivPrime R ω) := by
  obtain ⟨u, hu⟩ := exists_units_pbwDivPrime (R := R) ω
  rw [show pbwDivPrime R ω = u • pbwDiv R ω from funext hu]
  exact (linearIndependent_pbwDiv hω).units_smul u

/-- The `T''_{i,-1}`-monomials are `𝒜`-linearly independent along reduced words (every Cartan
datum). -/
theorem linearIndependent_pbwDivPrimeSymm
    {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W} {ω : List I}
    (hω : cs.IsReduced ω) : LinearIndependent 𝒜 (pbwDivPrimeSymm R ω) := by
  obtain ⟨u, hu⟩ := exists_units_pbwDivPrimeSymm (R := R) ω
  rw [show pbwDivPrimeSymm R ω = u • pbwDivSymm R ω from funext hu]
  exact (linearIndependent_pbwDivSymm hω).units_smul u

variable (hSL : D.cartanMatrix.IsSimplyLaced)

include hSL in
/-- **[Lus] 41.1.4 (a)** (`e = 1`, simply-laced type): the `𝒜`-span of the monomials
`E_{i₁}^{(c₁)} T'_{i₁,1}(E_{i₂}^{(c₂)}) ⋯` does not depend on the reduced expression. -/
theorem span_pbwDivPrime_of_isReduced {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span 𝒜 (Set.range (pbwDivPrime R u)) =
      Submodule.span 𝒜 (Set.range (pbwDivPrime R w)) := by
  rw [span_pbwDivPrime, span_pbwDivPrime, span_pbwDiv_of_isReduced hSL cs hu hw huw]

include hSL in
/-- **[Lus] 41.1.4 (b)** (`e = -1`, simply-laced type): the `𝒜`-span of the monomials
`E_{i₁}^{(c₁)} T''_{i₁,-1}(E_{i₂}^{(c₂)}) ⋯` does not depend on the reduced expression, and equals
the span `𝒜U⁺(w, -1)` of [Lus] 41.1.4 (a) (`span_pbwDivPrimeSymm`). -/
theorem span_pbwDivPrimeSymm_of_isReduced {W : Type*} [Group W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {u w : List I}
    (hu : cs.IsReduced u) (hw : cs.IsReduced w) (huw : cs.wordProd u = cs.wordProd w) :
    Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R u)) =
      Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R w)) := by
  rw [span_pbwDivPrimeSymm, span_pbwDivPrimeSymm, span_pbwDivSymm_of_isReduced hSL cs hu hw huw]

include hSL in
/-- **[Lus] 41.1.7** (`e = 1`, via `T'_{i,1}`): `𝒜U⁺(w₀, 1) = 𝒜U⁺` in simply-laced finite type. -/
theorem coe_span_pbwDivPrime_longest {W : Type*} [Group W] [Finite W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    (hw₀ : cs.wordProd w = cs.longestElement) :
    (Submodule.span 𝒜 (Set.range (pbwDivPrime R w)) : Set (QuantumGroup R 𝕧)) = aPlus R := by
  rw [span_pbwDivPrime, coe_span_pbwDiv_longest hSL cs hw hw₀]

include hSL in
/-- **[Lus] 41.1.7** (`e = -1`, via `T''_{i,-1}`): `𝒜U⁺(w₀, -1) = 𝒜U⁺` in simply-laced finite
type. -/
theorem coe_span_pbwDivPrimeSymm_longest {W : Type*} [Group W] [Finite W]
    (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)
    (hw₀ : cs.wordProd w = cs.longestElement) :
    (Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R w)) : Set (QuantumGroup R 𝕧)) = aPlus R := by
  rw [span_pbwDivPrimeSymm, coe_span_pbwDivSymm_longest hSL cs hw hw₀]

end Modified

end LieLean.QuantumGroup
