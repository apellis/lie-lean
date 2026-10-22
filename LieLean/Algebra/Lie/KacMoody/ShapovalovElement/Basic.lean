/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.ShapovalovElement.Families
import LieLean.Algebra.Lie.KacMoody.VermaEmbedding
import LieLean.Algebra.Lie.UniversalEnveloping.Symbol

/-!
# Shapovalov elements: definition and the simple-root case

Let `γ = v αᵢ` be a positive real root, `γ = ∑ⱼ aⱼ αⱼ`, and `r > 0`. A *Shapovalov element* for
`(γ, r)` ([HumO] §4.12) is an element `θ ∈ U(𝔟⁻)_{-rγ}` such that

* (a) `θ v⁺` is a maximal vector of `M(λ)` whenever `⟨λ + ρ, γ^∨⟩ = r`;
* (b) `θ = ∏ⱼ yⱼ^{r aⱼ} + ∑ pₖ qₖ` with `pₖ ∈ U(𝔫⁻)`, `qₖ ∈ U(𝔥)` and `deg pₖ < r ∑ aⱼ`.

Writing `U(𝔟⁻) = U(𝔫⁻) ⊗ S(𝔥)` and specializing the factor `S(𝔥)` (polynomial functions on `𝔥*`)
at `λ`, we encode `θ` as the polynomial family `λ ↦ θ(λ) ∈ U(𝔫⁻)` (`VermaModule.polyFam`); `θ(λ)`
is the element with `θ v_λ = θ(λ) v_λ` of [HumO] §4.13. Condition (a) is stated after this
specialization, and (b) says `θ(λ) - ∏ⱼ yⱼ^{r aⱼ}` lies in the PBW filtration `F_{d-1} U(𝔫⁻)`,
`d = r ∑ aⱼ`, for every `λ` (`VermaModule.IsShapovalovElement`). The product is taken in the
order of `Finset.univ.toList`; modulo `F_{d-1}` the order does not matter
(`VermaModule.hasSymbol_shapovalovLead`).

For a simple root `γ = αⱼ`, `θ = yⱼ^r` is a Shapovalov element ([HumO] §4.13, first paragraph,
via Prop. 1.4): `VermaModule.isShapovalovElement_simple`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §1.4, §4.12, §4.13.
-/

open Module LieModule UniversalEnvelopingAlgebra

noncomputable section

namespace Matrix.Realization.KacMoodyAlgebra.VermaModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)

local notation "𝒰⁻" => UniversalEnvelopingAlgebra K (nNeg P)

/-! ### The generators `yⱼ = fⱼ` of `U(𝔫⁻)` and the leading term -/

/-- The generator `yⱼ = fⱼ` of `U(𝔫⁻)`. -/
def fEnv (j : ι) : 𝒰⁻ := UniversalEnvelopingAlgebra.ι K ⟨f P j, f_mem_nNeg P j⟩

/-- The symbol of `yⱼ` in `gr U(𝔫⁻)`. -/
def fSym (j : ι) : AssociatedGraded K (nNeg P) :=
  toGr K (nNeg P) 1 ⟨fEnv P j, ι_mem_filtration_one _⟩

/-- The leading term `∏ⱼ yⱼ^{r aⱼ}` of a Shapovalov element ([HumO] Thm. 4.12 (b)), with the
product over `ι` in the order of `Finset.univ.toList`. -/
def shapovalovLead (r : ℕ) (a : ι → ℕ) : 𝒰⁻ :=
  ((Finset.univ : Finset ι).toList.map fun j ↦ fEnv P j ^ (r * a j)).prod

variable {P}

omit [CharZero K] in
lemma hasSymbol_fEnv (j : ι) : HasSymbol 1 (fSym P j) (fEnv P j) := HasSymbol.of_mem _

lemma fSym_ne_zero (j : ι) : fSym P j ≠ 0 :=
  toGr_ι_ne_zero fun h ↦ f_ne_zero P j (congrArg Subtype.val h)

omit [CharZero K] in
lemma hasSymbol_list_prod (r : ℕ) (a : ι → ℕ) (l : List ι) :
    HasSymbol (l.map fun j ↦ r * a j).sum (l.map fun j ↦ fSym P j ^ (r * a j)).prod
      (l.map fun j ↦ fEnv P j ^ (r * a j)).prod := by
  induction l with
  | nil => simpa using (HasSymbol.one : HasSymbol 0 1 (1 : 𝒰⁻))
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    exact (((hasSymbol_fEnv j).pow (r * a j)).congr_deg (one_mul _)).mul ih

omit [CharZero K] in
/-- The symbol of `∏ⱼ yⱼ^{r aⱼ}` in degree `r ∑ aⱼ` is `∏ⱼ [yⱼ]^{r aⱼ}`; in particular it does
not depend on the order of the product. -/
lemma hasSymbol_shapovalovLead (r : ℕ) (a : ι → ℕ) :
    HasSymbol (r * ∑ j, a j) (∏ j, fSym P j ^ (r * a j)) (shapovalovLead P r a) := by
  have h := hasSymbol_list_prod (P := P) r a (Finset.univ : Finset ι).toList
  rw [Finset.sum_map_toList, Finset.prod_map_toList, ← Finset.mul_sum] at h
  -- the remaining list product is `shapovalovLead P r a` by definition
  exact h

lemma prod_fSym_ne_zero (r : ℕ) (a : ι → ℕ) : ∏ j, fSym P j ^ (r * a j) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (fSym_ne_zero j)

/-! ### `yⱼ` acting on Verma modules -/

lemma equivEnvNNeg_fEnv_mul (Λ : Dual K H) (j : ι) (u : 𝒰⁻) :
    equivEnvNNeg P Λ (fEnv P j * u) = ⁅f P j, equivEnvNNeg P Λ u⁆ := by
  rw [fEnv, ← actEnv_of_mem_nNeg Λ (f_mem_nNeg P j), equivEnvNNeg_actEnv]

lemma equivEnvNNeg_fEnv_pow_mul (Λ : Dual K H) (j : ι) (n : ℕ) (u : 𝒰⁻) :
    equivEnvNNeg P Λ (fEnv P j ^ n * u) =
      (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P j) ^ n) (equivEnvNNeg P Λ u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, equivEnvNNeg_fEnv_mul, ih, pow_succ', Module.End.mul_apply,
      toEnd_apply_apply]

lemma equivEnvNNeg_fEnv_pow (Λ : Dual K H) (j : ι) (n : ℕ) :
    equivEnvNNeg P Λ (fEnv P j ^ n) =
      (toEnd K P.KacMoodyAlgebra (VermaModule P Λ) (f P j) ^ n) (hwv P Λ) := by
  have h := equivEnvNNeg_fEnv_pow_mul (P := P) Λ j n 1
  rwa [mul_one, equivEnvNNeg_one] at h

/-! ### Shapovalov elements -/

variable (P) in
/-- `θ` is a **Shapovalov element** for the positive root `γ = v αᵢ = ∑ⱼ aⱼ αⱼ` and `r`
([HumO] Thm. 4.12), encoded as a polynomial family `λ ↦ θ(λ) ∈ U(𝔫⁻)`:
* `θ(λ) ∈ U(𝔫⁻)_{-rγ}` for all `λ`;
* (a) if `⟨λ + ρ, γ^∨⟩ = r`, then `𝔫` kills `θ(λ) v_λ ∈ M(λ)`;
* (b) `θ(λ) - ∏ⱼ yⱼ^{r aⱼ} ∈ F_{d-1} U(𝔫⁻)` for all `λ`, where `d = r ∑ aⱼ`. -/
structure IsShapovalovElement (hA : A.IsGeneralizedCartan) (v : P.weylGroup hA) (i : ι) (r : ℕ)
    (a : ι → ℕ) (θ : Dual K H → 𝒰⁻) : Prop where
  mem_polyFam : θ ∈ polyFam P
  mem_negWeightSpace : ∀ Λ, θ Λ ∈ negWeightSpace P (r • P.rootOf fun j ↦ (a j : ℤ))
  actEnv_eq_zero : ∀ Λ, P.corootPairing hA (Λ + P.rho) v i = r →
    ∀ x ∈ nPos P, actEnv P Λ x (θ Λ) = 0
  sub_mem_filtration : ∀ Λ, θ Λ - shapovalovLead P r a ∈ filtration K (nNeg P) (r * ∑ j, a j - 1)

namespace IsShapovalovElement

variable {hA : A.IsGeneralizedCartan} {v : P.weylGroup hA} {i : ι} {r : ℕ} {a : ι → ℕ}

/-- The symbol of `θ(λ)` in degree `r ∑ aⱼ` is `∏ⱼ [yⱼ]^{r aⱼ}`. -/
lemma hasSymbol {θ : Dual K H → 𝒰⁻} (h : IsShapovalovElement P hA v i r a θ)
    (hpos : 0 < r * ∑ j, a j) (Λ : Dual K H) : HasSymbol (r * ∑ j, a j) (∏ j, fSym P j ^ (r * a j)) (θ Λ) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
  have h1 : HasSymbol (d + 1) (∏ j, fSym P j ^ (r * a j)) (shapovalovLead P r a) :=
    (hasSymbol_shapovalovLead r a).congr_deg hd
  have h2 := h.sub_mem_filtration Λ
  rw [hd, Nat.add_sub_cancel] at h2
  exact (h1.of_sub_mem h2).congr_deg hd.symm

lemma ne_zero {θ : Dual K H → 𝒰⁻} (h : IsShapovalovElement P hA v i r a θ) (hpos : 0 < r * ∑ j, a j)
    (Λ : Dual K H) : θ Λ ≠ 0 :=
  HasSymbol.ne_zero (h.hasSymbol hpos Λ) (prod_fSym_ne_zero (P := P) r a)

/-- A Shapovalov element only depends on the coroot pairing `⟨-, γ^∨⟩`. -/
lemma of_corootPairing_eq {θ : Dual K H → 𝒰⁻} {v' : P.weylGroup hA}
    {i' : ι}
    (h : IsShapovalovElement P hA v i r a θ)
    (hc : ∀ x, P.corootPairing hA x v' i' = P.corootPairing hA x v i) :
    IsShapovalovElement P hA v' i' r a θ where
  mem_polyFam := h.mem_polyFam
  mem_negWeightSpace := h.mem_negWeightSpace
  actEnv_eq_zero Λ hΛ := h.actEnv_eq_zero Λ (by rw [← hc]; exact hΛ)
  sub_mem_filtration := h.sub_mem_filtration

end IsShapovalovElement

/-! ### Simple roots -/

/-- **Simple roots** ([HumO] §4.13, via Prop. 1.4): `yⱼ^r` is a Shapovalov element for
`γ = αⱼ` and `r > 0`. -/
theorem isShapovalovElement_simple (hA : A.IsGeneralizedCartan) (j : ι) {r : ℕ} (hr : 0 < r) :
    IsShapovalovElement P hA 1 j r (Pi.single j 1) fun _ ↦ fEnv P j ^ r where
  mem_polyFam := const_mem_polyFam _
  mem_negWeightSpace Λ := by
    have hν : r • P.rootOf (fun k ↦ ((Pi.single j 1 : ι → ℕ) k : ℤ)) = r • P.root j := by
      rw [← P.rootOf_single j]
      congr 2
      ext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]
    rw [hν, ← equivEnvNNeg_mem_weightSpace_iff P Λ, equivEnvNNeg_fEnv_pow]
    exact toEnd_f_pow_mem_weightSpace j (VermaModule.hwv_mem_weightSpace P Λ) r
  actEnv_eq_zero Λ hΛ x hx := by
    rw [corootPairing_one] at hΛ
    have hprim := toEnd_f_pow_hwv_mem_primitiveVectors P hA hr hΛ
    rw [actEnv_apply, equivEnvNNeg_fEnv_pow,
      lie_eq_zero_of_mem_nPos (mem_primitiveVectors.mp hprim).2 hx, map_zero]
  sub_mem_filtration Λ := by
    have hsum : r * ∑ k, (Pi.single j 1 : ι → ℕ) k = r := by simp
    obtain ⟨d, hd⟩ : ∃ d, r = d + 1 := ⟨r - 1, by omega⟩
    have h1 := (hasSymbol_shapovalovLead (P := P) r (Pi.single j 1)).congr_deg
      (hsum.trans hd)
    have h2 := ((hasSymbol_fEnv (P := P) j).pow r).congr_deg ((one_mul r).trans hd)
    have hprod : ∏ k, fSym P k ^ (r * (Pi.single j 1 : ι → ℕ) k) = fSym P j ^ r := by
      rw [Finset.prod_eq_single j (fun k _ hk ↦ by simp [hk]) (by simp)]
      simp
    rw [hprod] at h1
    rw [hsum, show r - 1 = d by omega]
    exact h2.sub_mem h1

end Matrix.Realization.KacMoodyAlgebra.VermaModule
