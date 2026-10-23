/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.Character
import LieLean.Algebra.Lie.KacMoody.Super.HighestWeight

/-!
# The character formula for `G(A, τ)`

Let `G(A, τ)` be the contragredient Lie superalgebra of a symmetrizable generalized Cartan matrix
`A` with an admissible parity `τ` (`aᵢⱼ` even for odd `τᵢ`), `W` the Weyl group of `A`, `ρ` with
`⟨ρ, αᵢ^∨⟩ = 1` and `R = ∏_{α > 0} (1 - e^{-α})^{mult α}` the denominator of the Kac–Moody
algebra `𝔤(A)` with the same Cartan matrix. For `Λ` dominant integral with `⟨Λ, αᵢ^∨⟩` even
for odd `τᵢ`, let `L̃(Λ) = M̄(Λ) / ∑ᵢ U fᵢ^{⟨Λ, αᵢ^∨⟩+1} v̄_Λ`, which is the irreducible
module `L(Λ)` of `G(A, τ)` ([Kac78] Thm. 2 (c), `GVerma.isSimpleModule_fPowQuotient`).

**[Kac78] Thm. 1**: `e^ρ R ch L(Λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}`. As in [Kac78], the
right-hand side is the one for `𝔤(A)`, so `ch L_{G(A, τ)}(Λ) = ch L_{𝔤(A)}(Λ)`.

The denominator of `G(A, τ)` is `ch M̄(0)⁻¹`; by `vermaChar_mul_denominator` it equals `R`. With
the denominator identity of `𝔤(A)` this gives **[Kac78] Thm. 2 (a)** in the form
`e^ρ = ch M̄(0) · ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w ρ}`. (The product form
`∏_{α ∈ Δ₀⁺} (1 - e^{-α})^{mult α} / ∏_{α ∈ Δ₁⁺} (1 + e^{-α})^{mult α}` of `ch M̄(0)⁻¹` would need
the root multiplicities of `G(A, τ)`, which are not formalized.)

## Proof ([Kac78] §2, after [Kac] §10.4)

* `e^ρ R` is `W`-anti-invariant and `ch L̃(Λ)` is `W`-invariant, since `L̃(Λ)` is integrable
  (`rank_modWeightSpace_weylGroup`).
* The Casimir operator acts on `L̃(Λ)` by `(Λ + 2ρ | Λ)`. Expanding `ch L̃(Λ)` in characters of
  Verma modules (`IsCasimirModule.exists_expansion`) and using `ch M̄(κ) R = e^κ` shows that the
  coefficient of `e^ν` in `R ch V` vanishes unless `(ν + 2ρ | ν) = (Λ + 2ρ | Λ)` and `ν ≤ Λ`
  (`IsCasimirModule.coeffAt_character_mul_denominator_ne_zero`, the analogue of [Kac] Prop. 9.8).
* The coefficient of `e^Λ` in `R ch L̃(Λ)` is `1`.
* The final step is that of the even case
  (`CharacterRing.coeffAt_eq_finsum_of_isWeylAntiInvariant`).

## Main definitions

* `Matrix.Realization.SuperEnveloping.IsCasimirModule.character`: the character of a module with
  finite-dimensional weight spaces in finitely many cones.

## Main results

* `Matrix.Realization.SuperEnveloping.IsCasimirModule.coeffAt_character_mul_denominator_ne_zero`.
* `Matrix.Realization.SuperEnveloping.GVerma.exp_rho_mul_denominator_mul_character`:
  **[Kac78] Thm. 1**.
* `Matrix.Realization.SuperEnveloping.GVerma.character_eq_character`:
  `ch L_{G(A, τ)}(Λ) = ch L_{𝔤(A)}(Λ)`.
* `Matrix.Realization.SuperEnveloping.exp_rho_eq_vermaChar_mul_weylAltSum`:
  **[Kac78] Thm. 2 (a)**, in the form above.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §2, Thms. 1, 2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Prop. 9.8, §10.4.
-/

universe u v w

open Module Matrix.Realization.CharacterRing Matrix.Realization.WeightOrd

noncomputable section

namespace Matrix.Realization.SuperEnveloping

variable {ι : Type u} {K : Type v} {H : Type w} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} {p : ι → ZMod 2}
  [CharZero K] [FiniteDimensional K H]

namespace IsCasimirModule

variable {S : A.Symmetrization} {Λs : Finset (Dual K H)} {c : K}

section Character

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (P.SuperEnveloping p) V]
  [IsScalarTower K (P.SuperEnveloping p) V]

/-- The character `ch V = ∑_μ dim V_μ e^μ`. -/
def character (hV : IsCasimirModule P p S V Λs c) : P.CharacterRing ℤ :=
  ofFun P (fun μ ↦ (finrank K (modWeightSpace P p V μ) : ℤ)) ⟨Λs, fun μ hμ ↦ by
    have hne : modWeightSpace P p V μ ≠ ⊥ := fun h ↦ hμ (by rw [h, finrank_bot]; rfl)
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
    exact hV.isBounded.exists_eq_sub hx hx0⟩

lemma coeffAt_character (hV : IsCasimirModule P p S V Λs c) (μ : Dual K H) :
    hV.character.coeffAt μ = finrank K (modWeightSpace P p V μ) := rfl

end Character

variable (hA : A.IsGeneralizedCartan) (hp : A.IsSuperAdmissible p)

include hA hp in
/-- **[Kac78] §2, cf. [Kac] Prop. 9.8**: if the Casimir operator acts on `V` by `c`, the
coefficient of `e^ν` in `R ch V` vanishes unless `(ν + 2ρ | ν) = c` and `ν` lies in one of the
cones. -/
theorem coeffAt_character_mul_denominator_ne_zero {V : Type (max u v w)} [AddCommGroup V]
    [Module K V] [Module (P.SuperEnveloping p) V] [IsScalarTower K (P.SuperEnveloping p) V]
    (hV : IsCasimirModule P p S V Λs c) {ν : Dual K H}
    (hν : (hV.character * KacMoodyAlgebra.denominator P).coeffAt ν ≠ 0) :
    P.dualBilinForm S (ν + 2 • P.rho) ν = c ∧ ∃ Λ ∈ Λs, toWeightOrd P Λ ≤ toWeightOrd P ν := by
  classical
  obtain ⟨a, ha, hexp⟩ := hV.exists_expansion hA ν
  set A' : P.CharacterRing ℤ := ofFun P (fun κ ↦ a κ) ⟨Λs, fun κ hκ ↦ by
    obtain ⟨Λ, hΛ, hle⟩ := (ha κ (Finsupp.mem_support_iff.2 hκ)).2
    obtain ⟨d, hd, h⟩ := (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).1 hle
    exact ⟨Λ, hΛ, d, hd, h⟩⟩
  have hF : ∀ μ, toWeightOrd P μ ≤ toWeightOrd P ν →
      hV.character.coeffAt μ = (A' * vermaChar P p).coeffAt μ := by
    intro μ hμ
    rw [coeffAt_character, hexp μ hμ, CharacterRing.coeff_mul,
      finsum_eq_sum_of_support_subset (s := a.support)]
    · refine Finset.sum_congr rfl fun κ _ ↦ ?_
      rw [coeffAt_vermaChar, neg_sub]
      rfl
    · intro κ hκ
      rw [Function.mem_support] at hκ
      exact Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hκ)
  rw [coeffAt_mul_congr isNegSupported_denominator hF, mul_assoc,
    vermaChar_mul_denominator S hA hp, mul_one] at hν
  exact ha ν (Finsupp.mem_support_iff.2 hν)

end IsCasimirModule

namespace GVerma

variable (S : A.Symmetrization) (hA : A.IsGeneralizedCartan) (hp : A.IsSuperAdmissible p)
  {Λ : Dual K H} {n : ι → ℕ}

include hA in
/-- `L̃(Λ)` is a module on which the Casimir operator acts by `(Λ + 2ρ | Λ)`. -/
lemma isCasimirModule_fPowQuotient :
    IsCasimirModule P p S (FPowQuotient P p Λ n) {Λ} (P.dualBilinForm S (Λ + 2 • P.rho) Λ) :=
  (IsCasimirModule.gVerma hA ⟨Λ, Finset.mem_singleton_self _, le_rfl⟩).quotient _

variable (p) in
/-- The character `ch L̃(Λ)`. -/
abbrev character (Λ : Dual K H) (n : ι → ℕ) : P.CharacterRing ℤ :=
  (isCasimirModule_fPowQuotient (p := p) (Λ := Λ) (n := n) S hA).character

omit [FiniteDimensional K H] in
include hA in
/-- `dim L̃(Λ)_Λ = 1`. -/
lemma finrank_modWeightSpace_fPowQuotient_self (hn : ∀ i, Λ (P.coroot i) = n i)
    (hodd : ∀ i, p i = 1 → Even (n i)) :
    finrank K (modWeightSpace P p (FPowQuotient P p Λ n) Λ) = 1 := by
  set N := fPowSubmodule P p Λ n
  have hW := modWeightSpace_quotient N isBounded.iSup_modWeightSpace_eq_top Λ
  rw [modWeightSpace_self, Submodule.map_span, Set.image_singleton] at hW
  have hx : N.mkQ (hwv P p Λ) ≠ 0 := fun h ↦ by
    refine fPowSubmodule_ne_top hA hn hodd ?_
    rw [eq_top_iff, ← span_hwv, Submodule.span_le, Set.singleton_subset_iff]
    exact (Submodule.Quotient.mk_eq_zero N).1 h
  rw [hW]
  exact finrank_span_singleton hx

include hA hp in
/-- `ch L̃(Λ)` is `W`-invariant. -/
lemma isWeylInvariant_character :
    (character p S hA Λ n).IsWeylInvariant P hA := fun w hw μ ↦ by
  rw [IsCasimirModule.coeffAt_character, IsCasimirModule.coeffAt_character]
  unfold Module.finrank
  rw [rank_modWeightSpace_weylGroup hA (isIntegrable_fPowQuotient S hA hp) hw μ]

include hA hp in
/-- **The character formula for `G(A, τ)`** ([Kac78] Thm. 1): for `Λ` dominant integral with
`⟨Λ, αᵢ^∨⟩ = nᵢ` even for odd `τᵢ`, `e^ρ R ch L̃(Λ) = ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w(Λ + ρ)}`, where
`R` is the denominator of the Kac–Moody algebra `𝔤(A)`. -/
theorem exp_rho_mul_denominator_mul_character (hn : ∀ i, Λ (P.coroot i) = n i)
    (hodd : ∀ i, p i = 1 → Even (n i)) :
    exp P ℤ P.rho * KacMoodyAlgebra.denominator P * character p S hA Λ n =
      weylAltSum P hA (KacMoodyAlgebra.IrreducibleModule.isDominantIntegral_add_rho
        fun i ↦ ⟨n i, hn i⟩) := by
  classical
  set hV := isCasimirModule_fPowQuotient (p := p) (Λ := Λ) (n := n) S hA
  have hcoeff : ∀ ν,
      (exp P ℤ P.rho * KacMoodyAlgebra.denominator P * character p S hA Λ n).coeffAt ν =
      (hV.character * KacMoodyAlgebra.denominator P).coeffAt (ν - P.rho) := fun ν ↦ by
    rw [mul_assoc, coeff_exp_mul, mul_comm]
  have hsupp : ∀ ν, hV.character.coeffAt ν ≠ 0 → ∃ k : ι → ℤ, 0 ≤ k ∧ ν = Λ - P.rootOf k :=
    fun ν hν ↦ by
      have hne : modWeightSpace P p (FPowQuotient P p Λ n) ν ≠ ⊥ :=
        fun h ↦ hν (by rw [IsCasimirModule.coeffAt_character, h, finrank_bot]; rfl)
      obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
      obtain ⟨Λ', hΛ', d, hd, h⟩ := hV.isBounded.exists_eq_sub hx hx0
      rw [Finset.mem_singleton] at hΛ'
      exact ⟨d, hd, hΛ' ▸ h⟩
  ext μ
  rw [coeffAt_weylAltSum]
  refine coeffAt_eq_finsum_of_isWeylAntiInvariant S
    ((KacMoodyAlgebra.isWeylAntiInvariant_exp_rho_mul_denominator hA).mul
      (isWeylInvariant_character S hA hp)) (fun i ↦ ⟨n i, by
        rw [LinearMap.add_apply, hn, rho_coroot]⟩) ?_ (fun ν hν ↦ ?_) μ
  · rw [hcoeff, add_sub_cancel_right]
    have hF : ∀ ν, toWeightOrd P ν ≤ toWeightOrd P Λ →
        hV.character.coeffAt ν = (exp P ℤ Λ).coeffAt ν := by
      intro ν hνΛ
      obtain ⟨k, hk, hk'⟩ := (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).1 hνΛ
      rw [← mul_one (exp P ℤ Λ), coeff_exp_mul, coeffAt_one]
      by_cases hνΛ' : ν = Λ
      · subst ν
        simp only [sub_self, ↓reduceIte]
        rw [IsCasimirModule.coeffAt_character,
          finrank_modWeightSpace_fPowQuotient_self hA hn hodd, Nat.cast_one]
      · simp only [sub_eq_zero, hνΛ', ↓reduceIte]
        by_contra h0
        obtain ⟨d, hd, hd'⟩ := hsupp ν h0
        refine hνΛ' ?_
        have h0' : P.rootOf (k + d) = P.rootOf 0 := by
          rw [map_add, map_zero]
          linear_combination (norm := module) hk' + hd'
        have hkd := P.rootOf_injective h0'
        have hd0 : d = 0 := le_antisymm (fun i ↦ by
          have h1 := congr_fun hkd i
          have h2 := hk i
          simp only [Pi.add_apply, Pi.zero_apply] at h1 h2 ⊢
          omega) hd
        rw [hd', hd0, map_zero, sub_zero]
    rw [coeffAt_mul_congr isNegSupported_denominator hF, coeff_exp_mul, sub_self,
      coeffAt_denominator_zero]
  · rw [hcoeff] at hν
    obtain ⟨hform, Λ', hΛ', hle⟩ := hV.coeffAt_character_mul_denominator_ne_zero hA hp hν
    rw [Finset.mem_singleton] at hΛ'
    subst hΛ'
    obtain ⟨k, hk, hk'⟩ := (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).1 hle
    refine ⟨⟨k, hk, ?_⟩, ?_⟩
    · rw [sub_eq_iff_eq_add] at hk' ⊢
      rw [hk']
      abel
    · have := (KacMoodyAlgebra.dualBilinForm_add_rho_add_rho_eq_iff S Λ' (ν - P.rho)).mpr hform.symm
      rw [sub_add_cancel] at this
      exact this.symm

include hA hp in
/-- **[Kac78] Thm. 1**: `ch L_{G(A, τ)}(Λ) = ch L_{𝔤(A)}(Λ)`, the character of the irreducible
highest-weight module `L̃(Λ)` of `G(A, τ)` is that of the irreducible highest-weight module
`L(Λ)` of the Kac–Moody algebra `𝔤(A)` with the same Cartan matrix. -/
theorem character_eq_character (hn : ∀ i, Λ (P.coroot i) = n i)
    (hodd : ∀ i, p i = 1 → Even (n i)) :
    character p S hA Λ n = (KacMoodyAlgebra.IrreducibleModule.isCategoryO P Λ).character := by
  have hS : A.IsSymmetrizable := Matrix.isSymmetrizable_iff_nonempty_symmetrization.mpr ⟨S⟩
  have h := (exp_rho_mul_denominator_mul_character S hA hp hn hodd).trans
    (KacMoodyAlgebra.IrreducibleModule.exp_rho_mul_denominator_mul_character hA hS
      fun i ↦ ⟨n i, hn i⟩).symm
  have hu : exp P ℤ (-P.rho) * vermaChar P p *
      (exp P ℤ P.rho * KacMoodyAlgebra.denominator P) = 1 := by
    rw [mul_mul_mul_comm, ← exp_add, neg_add_cancel, exp_zero,
      vermaChar_mul_denominator S hA hp, one_mul]
  rw [← one_mul (character p S hA Λ n), ← hu, mul_assoc, h, ← mul_assoc, hu, one_mul]

end GVerma

variable (S : A.Symmetrization) (hA : A.IsGeneralizedCartan) (hp : A.IsSuperAdmissible p)

include S hA hp in
/-- **The denominator identity for `G(A, τ)`** ([Kac78] Thm. 2 (a)): the denominator of
`G(A, τ)` is `ch M̄(0)⁻¹`, and `e^ρ = ch M̄(0) ∑_{w ∈ W} (-1)^{ℓ(w)} e^{w ρ}`. [Kac78] writes
`ch M̄(0)⁻¹` as a product over the even and odd positive roots of `G(A, τ)`; that form needs the
root multiplicities of `G(A, τ)`, which are not formalized. -/
theorem exp_rho_eq_vermaChar_mul_weylAltSum :
    exp P ℤ P.rho = vermaChar P p *
      weylAltSum P hA (KacMoodyAlgebra.IrreducibleModule.isDominantIntegral_rho (P := P)) := by
  have hS : A.IsSymmetrizable := Matrix.isSymmetrizable_iff_nonempty_symmetrization.mpr ⟨S⟩
  rw [← KacMoodyAlgebra.IrreducibleModule.exp_rho_mul_denominator hA hS, mul_comm (exp P ℤ _),
    ← mul_assoc, vermaChar_mul_denominator S hA hp, one_mul]

end Matrix.Realization.SuperEnveloping
