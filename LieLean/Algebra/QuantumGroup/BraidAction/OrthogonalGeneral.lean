/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.HigherDoubleRelation
import LieLean.Algebra.QuantumGroup.BraidAction.Artin

/-!
# Constructor-independent length-two quantum braid relations

## Main definitions / results
`HasBraidGeneratorImages` records explicit generator formulas, not braid equalities.
Any actual quotient homomorphisms with these formulas commute at orthogonal centres,
with arbitrary outgoing Cartan degrees and arbitrary common neighbours.
The published nonterminal-double maps instantiate the theorem.

## References
Reconstructed from the repository definitions `serreAux`, `braidEj`, `braidFj`,
`SimplyLacedRelations` and `HigherDoubleRelation`.
This does not construct maps at currently unsupported nodes or prove length three.
-/
noncomputable section
namespace QuantumGroup

section Polynomial
variable {k B : Type*} [Field k] [Ring B] [Algebra k B]

/-- Arbitrarily weighted left/right power operators at commuting centres commute.
No Serre relation or nonvanishing denominator is required. -/
theorem powerSandwich_comm (a b c : B) (hab : Commute a b)
    (r s u w : ℕ) :
    a ^ r * (b ^ u * c * b ^ w) * a ^ s =
      b ^ u * (a ^ r * c * a ^ s) * b ^ w := by
  have hleft := (hab.pow_pow r u).eq
  have hright := (hab.pow_pow s w).eq
  calc
    _ = (a ^ r * b ^ u) * c * (b ^ w * a ^ s) := by simp only [mul_assoc]
    _ = (b ^ u * a ^ r) * c * (a ^ s * b ^ w) := by rw [hleft, ← hright]
    _ = _ := by simp only [mul_assoc]

/-- Commutation of the totalized rescaled-Serre operators, in all degrees. -/
theorem serreAux_operator_comm (a b c : B) (hab : Commute a b)
    (q t x y α β : k) (m n : ℕ) :
    α • serreAux q x m a (β • serreAux t y n b c) =
      β • serreAux t y n b (α • serreAux q x m a c) := by
  simp only [serreAux, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro w _
  rw [powerSandwich_comm a b c hab]
  congr 1
  ring

/-- Naturality of the rescaled-Serre polynomial under algebra homomorphisms. -/
theorem map_serreAux_allNode (T : B →ₐ[k] B) (q x : k) (m : ℕ) (a b : B) :
    T (serreAux q x m a b) = serreAux q x m (T a) (T b) := by
  simp only [serreAux, map_sum, map_smul, map_mul, map_pow]

end Polynomial

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k}

/-- Explicit Lusztig formulas for an already constructed algebra homomorphism.
This package asserts neither transformed relations nor braid equalities. -/
structure HasBraidGeneratorImages (i : I)
    (T : QuantumGroup R v →ₐ[k] QuantumGroup R v) : Prop where
  map_E : ∀ l, T (QuantumGroup.E R v l) =
    if l = i then braidEi R i else braidEj R v i l
  map_F : ∀ l, T (QuantumGroup.F R v l) =
    if l = i then braidFi R i else braidFj R v i l
  map_K : ∀ μ, T (QuantumGroup.K R v μ) = QuantumGroup.K R v (reflY R i μ)

/-- Maps from different local constructors agree whenever they have the same formulas. -/
theorem HasBraidGeneratorImages.unique {i : I}
    {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
    (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages i T) : S = T := by
  apply hom_ext
  · intro l; rw [HS.map_E, HT.map_E]
  · intro l; rw [HS.map_F, HT.map_F]
  · intro μ; rw [HS.map_K, HT.map_K]

/-- Length two on every positive generator, even at arbitrary-degree common neighbours. -/
theorem HasBraidGeneratorImages.comm_E {i j : I}
    {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
    (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) (l : I) :
    S (T (E R v l)) = T (S (E R v l)) := by
  have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp h0
  by_cases hli : l = i
  · subst l
    simp [HS.map_E, HT.map_E, HT.map_F, HT.map_K, hij, braidEi, Kt,
      braidEj_eq_of_cartanMatrix_eq_zero h0',
      braidFj_eq_of_cartanMatrix_eq_zero h0', reflY_ktilde_of_cartanMatrix_eq_zero h0']
  · by_cases hlj : l = j
    · subst l
      simp [HS.map_E, HT.map_E, HS.map_F, HS.map_K, hij.symm, braidEi, Kt,
        braidEj_eq_of_cartanMatrix_eq_zero h0,
        braidFj_eq_of_cartanMatrix_eq_zero h0, reflY_ktilde_of_cartanMatrix_eq_zero h0]
    · rw [HT.map_E, ite_eq_right hlj, HS.map_E, ite_eq_right hli]
      rw [braidEj, map_smul, map_serreAux_allNode,
        braidEj, map_smul, map_serreAux_allNode]
      simp only [HS.map_E, HT.map_E, hij, hij.symm, hli, hlj, ↓reduceIte,
        braidEj_eq_of_cartanMatrix_eq_zero h0,
        braidEj_eq_of_cartanMatrix_eq_zero h0']
      exact serreAux_operator_comm (E R v j) (E R v i) (E R v l)
        (E_commute_E_of_cartanMatrix_eq_zero h0') _ _ _ _ _ _ _ _

/-- Length two on every negative generator, without degree or parameter restrictions. -/
theorem HasBraidGeneratorImages.comm_F {i j : I}
    {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
    (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) (l : I) :
    S (T (F R v l)) = T (S (F R v l)) := by
  have h0' := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).mp h0
  by_cases hli : l = i
  · subst l
    simp [HT.map_E, HS.map_F, HT.map_F, HT.map_K, hij, braidFi,
      braidEj_eq_of_cartanMatrix_eq_zero h0',
      braidFj_eq_of_cartanMatrix_eq_zero h0', reflY_ktilde_of_cartanMatrix_eq_zero h0']
  · by_cases hlj : l = j
    · subst l
      simp [HS.map_E, HS.map_F, HT.map_F, HS.map_K, hij.symm, braidFi,
        braidEj_eq_of_cartanMatrix_eq_zero h0,
        braidFj_eq_of_cartanMatrix_eq_zero h0, reflY_ktilde_of_cartanMatrix_eq_zero h0]
    · rw [HT.map_F, ite_eq_right hlj, HS.map_F, ite_eq_right hli]
      rw [braidFj, map_smul, map_serreAux_allNode,
        braidFj, map_smul, map_serreAux_allNode]
      simp only [HS.map_F, HT.map_F, hij, hij.symm, hli, hlj, ↓reduceIte,
        braidFj_eq_of_cartanMatrix_eq_zero h0,
        braidFj_eq_of_cartanMatrix_eq_zero h0']
      exact serreAux_operator_comm (F R v j) (F R v i) (F R v l)
        (F_commute_F_of_cartanMatrix_eq_zero h0') _ _ _ _ _ _ _ _

/-- Orthogonal-centre braid relation on the entire quotient and arbitrary toral lattice.
Only explicit formulas for actual algebra homomorphisms are assumed. -/
theorem HasBraidGeneratorImages.comm {i j : I}
    {S T : QuantumGroup R v →ₐ[k] QuantumGroup R v}
    (HS : HasBraidGeneratorImages i S) (HT : HasBraidGeneratorImages j T)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) : S.comp T = T.comp S := by
  refine hom_ext (HS.comm_E HT hij h0) (HS.comm_F HT hij h0) ?_
  intro μ
  simp only [AlgHom.comp_apply, HS.map_K, HT.map_K, reflY_comm_of_cartanMatrix_eq_zero i j h0]

variable [NeZero v]

/-- The nonterminal-double quotient lift has the constructor-independent formulas. -/
theorem nonterminalDoubleBraid_hasBraidGeneratorImages (i : I) (H : HigherDoubleData D v i) :
    HasBraidGeneratorImages i (nonterminalDoubleBraid (R := R) i
      H.edge H.leaf H.unique H.path H.diff H.sum H.cycl H.cube) where
  map_E := nonterminalDoubleBraid_E i H.edge H.leaf H.unique H.path H.diff H.sum H.cycl H.cube
  map_F := nonterminalDoubleBraid_F i H.edge H.leaf H.unique H.path H.diff H.sum H.cycl H.cube
  map_K := nonterminalDoubleBraid_K i H.edge H.leaf H.unique H.path H.diff H.sum H.cycl H.cube

/-- Actual length-two relation for the published double-edge quotient maps.
Hypotheses are local at these two nodes, not imposed at every node of the diagram. -/
theorem nonterminalDoubleBraid_comm (i j : I)
    (Hi : HigherDoubleData D v i) (Hj : HigherDoubleData D v j)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) :
    (nonterminalDoubleBraid (R := R) i
      Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube).comp
      (nonterminalDoubleBraid j
        Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube) =
    (nonterminalDoubleBraid j
      Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube).comp
      (nonterminalDoubleBraid i
        Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube) :=
  (nonterminalDoubleBraid_hasBraidGeneratorImages i Hi).comm
    (nonterminalDoubleBraid_hasBraidGeneratorImages j Hj) hij h0

omit [NeZero v] in
/-- Length two in the automorphism-group multiplication convention, for any constructors. -/
theorem HasBraidGeneratorImages.equiv_comm {i j : I}
    {S T : QuantumGroup R v ≃ₐ[k] QuantumGroup R v}
    (HS : HasBraidGeneratorImages i S.toAlgHom) (HT : HasBraidGeneratorImages j T.toAlgHom)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) : S * T = T * S := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (HS.comm HT hij h0) x

/-- Actual orthogonal nonterminal-double automorphisms commute. -/
theorem nonterminalDoubleBraidEquiv_comm (i j : I)
    (Hi : HigherDoubleData D v i) (Hj : HigherDoubleData D v j)
    (hij : i ≠ j) (h0 : D.cartanMatrix i j = 0) :
    nonterminalDoubleBraidEquiv (R := R) i
        Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube *
      nonterminalDoubleBraidEquiv j
        Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube =
    nonterminalDoubleBraidEquiv j
        Hj.edge Hj.leaf Hj.unique Hj.path Hj.diff Hj.sum Hj.cycl Hj.cube *
      nonterminalDoubleBraidEquiv i
        Hi.edge Hi.leaf Hi.unique Hi.path Hi.diff Hi.sum Hi.cycl Hi.cube :=
  (nonterminalDoubleBraid_hasBraidGeneratorImages i Hi).equiv_comm
    (nonterminalDoubleBraid_hasBraidGeneratorImages j Hj) hij h0

variable (i : I)
  (he : ∀ j, j ≠ i → D.cartanMatrix i j = 0 ∨
    (D.cartanMatrix i j = -1 ∧ D.cartanMatrix j i = -1))
  (hl : ∀ j l, D.cartanMatrix i j = -1 → D.cartanMatrix i l = -1 →
    j ≠ l → D.cartanMatrix j l = 0)
  (hp : ∀ j l, D.cartanMatrix i j = -1 → D.cartanMatrix i l = 0 →
    D.cartanMatrix j l = 0 ∨ (D.cartanMatrix j l = -1 ∧ D.cartanMatrix l j = -1))
  (hq : v ^ D.d i - (v ^ D.d i)⁻¹ ≠ 0)
  (hs : v ^ D.d i + (v ^ D.d i)⁻¹ ≠ 0)

/-- The simply-laced constructor has exactly the same constructor-independent formulas. -/
theorem simplyLacedBraid_hasBraidGeneratorImages :
    HasBraidGeneratorImages i (simplyLacedBraid (R := R) i he hl hp hq hs) where
  map_E := simplyLacedBraid_E i he hl hp hq hs
  map_F := simplyLacedBraid_F i he hl hp hq hs
  map_K := simplyLacedBraid_K i he hl hp hq hs

/-- Exact compatibility of the two published local constructors on their overlap.
This does not extend either constructor's path scope. -/
theorem simplyLacedBraid_eq_nonterminalDoubleBraid (H : HigherDoubleData D v i) :
    simplyLacedBraid (R := R) i he hl hp hq hs =
      nonterminalDoubleBraid i H.edge H.leaf H.unique H.path H.diff H.sum H.cycl H.cube :=
  (simplyLacedBraid_hasBraidGeneratorImages i he hl hp hq hs).unique
    (nonterminalDoubleBraid_hasBraidGeneratorImages i H)

end QuantumGroup
