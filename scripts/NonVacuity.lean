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

end NonVacuity
