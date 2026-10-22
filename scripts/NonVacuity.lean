import LieLean

/-!
# Non-vacuity checks for the headline theorems

Each `example` below applies a headline theorem to a concrete datum and discharges every
hypothesis by proof. If a later change makes a hypothesis set unsatisfiable for these data, or
breaks the statement's shape, this file stops compiling and CI fails. Where cheap, a second
`example` records that the conclusion is not degenerate.

Data: the Cartan matrix of type `A₂` (so the Serre relations are not vacuous) with its standard
realization over `ℚ`, the Lusztig Cartan datum of `sl₂`, and its extended root datum.
-/

open LieLean LieLean.QuantumGroup Matrix Matrix.Realization Matrix.Realization.KacMoodyAlgebra

noncomputable section

local instance : NeZero (RatFunc.X : RatFunc ℚ) := ⟨RatFunc.X_ne_zero⟩

namespace NonVacuity

/-! ### Type `A₂` -/

theorem hA2 : (CartanMatrix.A 2).IsGeneralizedCartan where
  diag := by decide
  offDiag_nonpos := CartanMatrix.A_apply_le_zero_of_ne 2
  zero_comm i j := by rw [(CartanMatrix.A_isSymm 2).apply i j]

theorem hS2 : (CartanMatrix.A 2).IsSymmetrizable := .of_isSymm (CartanMatrix.A_isSymm 2)

/-- The standard realization of `A₂` over `ℚ`. -/
abbrev P2 := Matrix.Realization.std (CartanMatrix.A 2) ℚ

/-! ### Gabber–Kac -/

example : AuxLieAlgebra.maxIdeal P2 = AuxLieAlgebra.serreIdeal P2 :=
  AuxLieAlgebra.maxIdeal_eq_serreIdeal P2 hA2 hS2

/-! ### Presentation of `L(Λ)` at `Λ = ρ` -/

theorem rho_coroot (i : Fin 2) : P2.rho (P2.coroot i) = ((fun _ ↦ 1 : Fin 2 → ℕ) i : ℚ) := by
  simp

example : FPowQuotient P2 P2.rho (fun _ ↦ 1) ≃ₗ⁅ℚ, P2.KacMoodyAlgebra⁆ IrreducibleModule P2 P2.rho :=
  FPowQuotient.equivIrreducibleModule hS2 hA2 rho_coroot

/-- Non-degeneracy: the highest weight vector of the quotient is nonzero. -/
example : FPowQuotient.hwv P2 P2.rho (fun _ ↦ 1) ≠ 0 :=
  FPowQuotient.hwv_ne_zero P2 hA2 rho_coroot

/-! ### Weyl–Kac character formula at `Λ = ρ` -/

example :=
  IrreducibleModule.exp_rho_mul_denominator_mul_character hA2 hS2
    (IrreducibleModule.isDominantIntegral_rho (P := P2))

/-! ### Complete reducibility, applied to `L(ρ)` -/

open Classical in
example : ∃ s : Set (LieSubmodule ℚ P2.KacMoodyAlgebra (IrreducibleModule P2 P2.rho)),
    DirectSum.IsInternal (fun N : s ↦ (N : Submodule ℚ (IrreducibleModule P2 P2.rho))) ∧
      ∀ N ∈ s, ∃ Λ, P2.IsDominantIntegral Λ ∧
        Nonempty (N ≃ₗ⁅ℚ, P2.KacMoodyAlgebra⁆ IrreducibleModule P2 Λ) :=
  IsCategoryO.exists_isInternal_irreducibleModule hA2 hS2
    (IrreducibleModule.isCategoryO P2 _)
    ((IrreducibleModule.isIntegrable_iff P2 hA2).2
      (IrreducibleModule.isDominantIntegral_rho (P := P2)))

/-! ### Quantum Gabber–Kac for `A₂` -/

/-- The Lusztig Cartan datum of type `A₂`, symmetrized by `ε = 1`. -/
def DA2 : LusztigCartanDatum (Fin 2) :=
  LusztigCartanDatum.ofSymmetrization hA2 ⟨fun _ ↦ 1, fun _ ↦ one_pos, fun i j ↦ by rw [(CartanMatrix.A_isSymm 2).apply i j]⟩

example : LusztigF.radical DA2 (RatFunc.X : RatFunc ℚ) = LusztigF.serreIdeal DA2 RatFunc.X :=
  LusztigF.radical_eq_serreIdeal_ratFunc DA2

/-- [Lus] Prop. 7.1.5 (b): the higher-order quantum Serre relation `f_{0,1;1,2;1} = 0` in `f`
for `A₂`. -/
example : higherSerre DA2 0 1 1 2 1 ∈ LusztigF.radical DA2 (RatFunc.X : RatFunc ℚ) :=
  higherSerre_mem_radical (by decide) 1 2 (Or.inl rfl)
    (by rw [DA2, LusztigCartanDatum.cartanMatrix_ofSymmetrization]; decide)

/-- [Lus] Cor. 7.1.7 for `A₂`, `m = 2`, `n = 1`: `θ₀^{(2)} θ₁` in terms of `θ₀^{(r)} θ₁ θ₀^{(2-r)}`,
`r ≤ 1`, in `f`. -/
example : LusztigF.toQuotient DA2 (RatFunc.X : RatFunc ℚ) (fDivPow DA2 0 2 * fDivPow DA2 1 1) =
    ∑ r ∈ Finset.range (1 * 1 + 1), higherSerreCoeff DA2 0 1 1 2 (2 - r) •
      LusztigF.toQuotient DA2 RatFunc.X
        (fDivPow DA2 0 r * fDivPow DA2 1 1 * fDivPow DA2 0 (2 - r)) :=
  toQuotient_fDivPow_mul_fDivPow (by decide)
    (by rw [DA2, LusztigCartanDatum.cartanMatrix_ofSymmetrization]; decide) (by norm_num)

open scoped TensorProduct in
/-- [Lus] 31.1.1: `_S f = S ⊗_𝒜 𝒜f` has the basis `1 ⊗ b`, `b ∈ B`; here `S = ℚ(v)`. -/
example : letI := LusztigF.integralLaurentEval.toAlgebra
    Module.Basis (canonicalBasis DA2) (RatFunc ℚ)
      (RatFunc ℚ ⊗[LaurentPolynomial ℤ] LusztigF.quotientIntegralForm DA2) :=
  letI := LusztigF.integralLaurentEval.toAlgebra
  baseChangeCanonicalBasis DA2 (RatFunc ℚ)

open scoped TensorProduct in
/-- [Lus] Prop. 33.2.2 (c): `_ℚ f` at `v ↦ -1` is presented by the quantum Serre relations at
`ε = -1`. -/
example : letI := (LaurentPolynomial.eval₂ (Int.castRingHom ℚ) (-1)).toAlgebra
    (LusztigF.serreIdeal DA2 (algebraMap (LaurentPolynomial ℤ) ℚ
      (LaurentPolynomial.T 1))).ringCon.Quotient ≃ₐ[ℚ]
      ℚ ⊗[LaurentPolynomial ℤ] LusztigF.quotientIntegralForm DA2 :=
  letI := (LaurentPolynomial.eval₂ (Int.castRingHom ℚ) (-1)).toAlgebra
  quasiClassicalEquiv DA2 ℚ fun i ↦ by
    rw [RingHom.algebraMap_toAlgebra, LaurentPolynomial.eval₂_T, ← pow_mul, mul_comm, pow_mul]
    simp

/-! ### Lusztig 25.2.1 (d) and 26.3.1 on the extended root datum of `sl₂` -/

/-- The extended root datum of `sl₂`. -/
abbrev R1 := sl2Datum.extendedRootDatum

theorem hR1 : R1.IsXRegular := sl2Datum.isXRegular_extendedRootDatum

theorem hY1 : ∀ N : ℕ, ∃ Λ : GrandLoop.Dom R1, ∀ i, (N : ℤ) ≤ Λ.1 (R1.coroot i) :=
  fun N ↦ GrandLoop.exists_dom_ge (R := R1) sl2Datum.exists_fundamental_extendedRootDatum N

/-- [Lus] Thm. 25.2.1 (d): the canonical basis of `U̇`. -/
example : Module.Basis (((Unit → ℤ) × (Unit → ℤ) →+ ℤ) × canonicalBasis sl2Datum ×
    canonicalBasis sl2Datum) (RatFunc ℚ) (Modified R1 (RatFunc.X : RatFunc ℚ)) :=
  Modified.modifiedCanonicalBasis hR1 hY1

/-- Non-degeneracy: the index set of that basis is nonempty. -/
example : Nonempty (((Unit → ℤ) × (Unit → ℤ) →+ ℤ) × canonicalBasis sl2Datum ×
    canonicalBasis sl2Datum) :=
  ⟨(0, ⟨_, one_mem_canonicalBasis sl2Datum⟩, ⟨_, one_mem_canonicalBasis sl2Datum⟩)⟩

/-- The extended root datum of `sl₂` is `Y`-regular. -/
theorem hYreg1 : R1.IsYRegular :=
  linearIndependent_unique_iff.2 (by simp [Prod.ext_iff, funext_iff])

/-- [Lus] Thm. 25.2.1 (a) with uniqueness, from `Y`-regularity. -/
example := existsUnique_modifiedCanonical_of_isYRegular hR1 hYreg1 0
  (one_mem_canonicalBasis sl2Datum) (one_mem_canonicalBasis sl2Datum)

/-- [Lus] Thm. 25.2.1 (a) for the transported element, without `hY`. -/
example (Λ : GrandLoop.Dom R1) :=
  modTensorAct_columnCanonical hR1 Λ Λ 0 (one_mem_canonicalBasis sl2Datum)
    (one_mem_canonicalBasis sl2Datum) (sub_self _) (one_mem_canonicalBasisHW Λ)
    (one_mem_canonicalBasisHW Λ)

/-! ### Lusztig 34.1.2 at `v = 2 ∈ 𝔽₅`, a primitive fourth root of `1` (`l = 2`) -/

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- `v = 2 ∈ 𝔽₅`. -/
abbrev v5 : (ZMod 5)ˣ := ZMod.unitOfCoprime 2 (by norm_num)

theorem hv5 : ((v5 : ZMod 5)) ^ (2 * 2) = 1 := by decide

theorem hv5prim : ∀ t, 0 < t → t < 2 → (v5 : ZMod 5) ^ (2 * t) ≠ 1 := fun t h0 ht ↦ by
  obtain rfl : t = 1 := by omega
  decide

/-- [Lus] 34.1.2 (a): `[2; 1] = 0` at `v = 2 ∈ 𝔽₅`. -/
example : gaussBinom v5 2 1 = 0 :=
  gaussBinom_eq_zero_of_not_dvd hv5 hv5prim (by norm_num) (by norm_num) (by norm_num)

/-- [Lus] 34.1.2 (e): `v^{l² + l} = (-1)^{l+1}` at `v = 2 ∈ 𝔽₅`. -/
example : (v5 : ZMod 5) ^ (2 ^ 2 + 2) = (-1) ^ (2 + 1) :=
  pow_sq_add_eq_of_root hv5 hv5prim (by norm_num)

/-- [Lus] 34.1.3 (a): `[2; 2] [4; 2] = 2! v^4` at `v = 2 ∈ 𝔽₅`. -/
example : ∏ j ∈ Finset.range 2, qBinomialU v5 (2 * (j + 1)) 2 =
    (Nat.factorial 2 : ZMod 5) * (v5 : ZMod 5) ^ (2 ^ 2 * Nat.choose 2 2) :=
  prod_qBinomialU_mul_root hv5 hv5prim (by norm_num) 2

/-- [Lus] 34.1.4 (a) at `v = 2 ∈ 𝔽₅`, `r = 0`, `a = 1`. -/
example := sum_qBinomialU_root (r := 0) (a := 1) hv5 hv5prim (by norm_num) (by norm_num)

end NonVacuity
