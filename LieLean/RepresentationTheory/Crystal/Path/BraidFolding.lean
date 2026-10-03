/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.Folding
import LieLean.RepresentationTheory.Crystal.Path.BraidA2

/-!
# The braid relations of types `B₂` and `G₂` on path crystals, by folding

Kashiwara's reflections on `B(Λ)` satisfy the braid relations of lengths `4` and `6`
(types `B₂` and `G₂`); with the relations of lengths `2` and `3` this gives an action of the
Weyl group on `B(Λ)` for **every** generalized Cartan matrix
(`Matrix.Realization.pathBraidRelations`).

The proof folds the Dynkin diagrams `A₃ → B₂` and `D₄ → G₂`. For a rank-two realization `Q` of a
matrix with `a₀₁ = -1`, `a₁₀ = -2` (resp. `-3`), a linear map `ψ` into a realization `R` of `A₃`
(resp. `D₄`; Mathlib's `CartanMatrix.A 3`, `CartanMatrix.D 4`) with
`⟨ψ v, α_a^∨⟩ = ⟨v, α_{o a}^∨⟩` for the colour map `o = (0, 1, 0)` (resp. `o = (0, 1, 0, 0)`,
the centre of `D₄` being `1`) is a folding map (`Matrix.Realization.FoldMap`). Composition with
`ψ` embeds `B_Q(μ)` into `B_R(ψ μ)` and sends `S₀ ↦ S₀ S₂`, `S₁ ↦ S₁` (resp.
`S₀ ↦ S₀ S₂ S₃`, `S₁ ↦ S₁`). The simply-laced braid relations on
`B_R(ψ μ)` (`Matrix.Realization.pathCrystal_reflection_braid_three`,
`Matrix.Realization.pathCrystal_reflection_comm`) give the folded relations by explicit braid
moves (`Matrix.Realization.braid_word_A3`, `Matrix.Realization.braid_word_D4`), and injectivity
of `ψ` transports them back (`Matrix.Realization.reflection_braid_four_of_B2`,
`Matrix.Realization.reflection_braid_six_of_G2`). Levi restriction
(`LSGeneralClass.LeviMap.iterate_reflection_eq_of_levi`) reduces the relations on `B(Λ)` for an
arbitrary generalized Cartan matrix to these rank-two cases.

## Main results

* `Matrix.Realization.reflection_braid_four_of_B2`,
  `Matrix.Realization.reflection_braid_six_of_G2`: `S₀S₁S₀S₁ = S₁S₀S₁S₀` and
  `(S₀S₁)³ = (S₁S₀)³` on the rank-two path crystals `B(μ)`.
* `Matrix.Realization.pathBraidRelations`: all braid relations hold on `B(Λ)` for every
  generalized Cartan matrix; the resulting action of the Weyl group on `B(Λ)` is
  `Matrix.Realization.pathWeylAction`
  (`LieLean.RepresentationTheory.Crystal.Path.WeylGroupAction`).

## References

* [Kas94] M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J.
  **73** (1994), 383–413, §7 (the Weyl group action on normal crystals).

The folding argument for the path model is reconstructed; it replaces, for the lengths `4` and
`6`, the rank-two piecewise-linear computations used for `A₂` in
`LieLean.RepresentationTheory.Crystal.Path.BraidA2`.
-/

open Set Module LittelmannPath

namespace Matrix.Realization

/-! ### Braid words -/

section Words

/-- A word identity for maps with `a c = c a`, `a b a = b a b` and `c b c = b c b` (a
relation in the Artin monoid of type `A₃`): `(ac) b (ac) b = b (ac) b (ac)`. -/
theorem braid_word_A3 {X : Type*} (a b c : X → X)
    (hac : ∀ z, a (c z) = c (a z))
    (hba : ∀ z, a (b (a z)) = b (a (b z)))
    (hbc : ∀ z, c (b (c z)) = b (c (b z)))
    (x : X) :
    a (c (b (a (c (b x))))) =
      b (a (c (b (a (c x))))) := by
  calc a (c (b (a (c (b x)))))
      _ = c (a (b (a (c (b x))))) := by
        rw [hac (b (a (c (b x))))]
      _ = c (b (a (b (c (b x))))) := by
        rw [hba (c (b x))]
      _ = c (b (a (c (b (c x))))) := by
        rw [(hbc x).symm]
      _ = c (b (c (a (b (c x))))) := by
        rw [hac (b (c x))]
      _ = b (c (b (a (b (c x))))) := by
        rw [hbc (a (b (c x)))]
      _ = b (c (a (b (a (c x))))) := by
        rw [(hba (c x)).symm]
      _ = b (a (c (b (a (c x))))) := by
        rw [(hac (b (a (c x)))).symm]

/-- A word identity for maps `a, c, d` commuting pairwise and each braiding with `b` (a relation
in the Artin monoid of type `D₄`): `(acd) b (acd) b (acd) b = b (acd) b (acd) b (acd)`. -/
theorem braid_word_D4 {X : Type*} (a b c d : X → X)
    (hac : ∀ z, a (c z) = c (a z))
    (had : ∀ z, a (d z) = d (a z))
    (hcd : ∀ z, c (d z) = d (c z))
    (hba : ∀ z, a (b (a z)) = b (a (b z)))
    (hbc : ∀ z, c (b (c z)) = b (c (b z)))
    (hbd : ∀ z, d (b (d z)) = b (d (b z)))
    (x : X) :
    a (c (d (b (a (c (d (b (a (c (d (b x))))))))))) =
      b (a (c (d (b (a (c (d (b (a (c (d x))))))))))) := by
  calc a (c (d (b (a (c (d (b (a (c (d (b x)))))))))))
      _ = a (c (d (b (c (a (d (b (a (c (d (b x))))))))))) := by
        rw [hac (d (b (a (c (d (b x))))))]
      _ = a (c (d (b (c (d (a (b (a (c (d (b x))))))))))) := by
        rw [had (b (a (c (d (b x)))))]
      _ = a (c (d (b (d (c (a (b (a (c (d (b x))))))))))) := by
        rw [hcd (a (b (a (c (d (b x))))))]
      _ = a (c (b (d (b (c (a (b (a (c (d (b x))))))))))) := by
        rw [hbd (c (a (b (a (c (d (b x)))))))]
      _ = a (c (b (d (b (c (b (a (b (c (d (b x))))))))))) := by
        rw [hba (c (d (b x)))]
      _ = a (c (b (d (c (b (c (a (b (c (d (b x))))))))))) := by
        rw [(hbc (a (b (c (d (b x)))))).symm]
      _ = a (c (b (c (d (b (c (a (b (c (d (b x))))))))))) := by
        rw [(hcd (b (c (a (b (c (d (b x)))))))).symm]
      _ = a (c (b (c (d (b (a (c (b (c (d (b x))))))))))) := by
        rw [(hac (b (c (d (b x))))).symm]
      _ = a (b (c (b (d (b (a (c (b (c (d (b x))))))))))) := by
        rw [hbc (d (b (a (c (b (c (d (b x))))))))]
      _ = a (b (c (d (b (d (a (c (b (c (d (b x))))))))))) := by
        rw [(hbd (a (c (b (c (d (b x))))))).symm]
      _ = a (b (c (d (b (a (d (c (b (c (d (b x))))))))))) := by
        rw [(had (c (b (c (d (b x)))))).symm]
      _ = a (b (c (d (b (a (d (b (c (b (d (b x))))))))))) := by
        rw [hbc (d (b x))]
      _ = a (b (c (d (b (a (d (b (c (d (b (d x))))))))))) := by
        rw [(hbd x).symm]
      _ = a (b (c (d (b (a (d (b (d (c (b (d x))))))))))) := by
        rw [hcd (b (d x))]
      _ = a (b (c (d (b (a (b (d (b (c (b (d x))))))))))) := by
        rw [hbd (c (b (d x)))]
      _ = a (b (c (d (a (b (a (d (b (c (b (d x))))))))))) := by
        rw [(hba (d (b (c (b (d x)))))).symm]
      _ = a (b (c (a (d (b (a (d (b (c (b (d x))))))))))) := by
        rw [(had (b (a (d (b (c (b (d x)))))))).symm]
      _ = a (b (a (c (d (b (a (d (b (c (b (d x))))))))))) := by
        rw [(hac (d (b (a (d (b (c (b (d x))))))))).symm]
      _ = a (b (a (c (d (b (d (a (b (c (b (d x))))))))))) := by
        rw [had (b (c (b (d x))))]
      _ = b (a (b (c (d (b (d (a (b (c (b (d x))))))))))) := by
        rw [hba (c (d (b (d (a (b (c (b (d x)))))))))]
      _ = b (a (b (c (b (d (b (a (b (c (b (d x))))))))))) := by
        rw [hbd (a (b (c (b (d x)))))]
      _ = b (a (c (b (c (d (b (a (b (c (b (d x))))))))))) := by
        rw [(hbc (d (b (a (b (c (b (d x)))))))).symm]
      _ = b (a (c (b (d (c (b (a (b (c (b (d x))))))))))) := by
        rw [hcd (b (a (b (c (b (d x))))))]
      _ = b (a (c (b (d (c (b (a (c (b (c (d x))))))))))) := by
        rw [(hbc (d x)).symm]
      _ = b (a (c (b (d (c (b (c (a (b (c (d x))))))))))) := by
        rw [hac (b (c (d x)))]
      _ = b (a (c (b (d (b (c (b (a (b (c (d x))))))))))) := by
        rw [hbc (a (b (c (d x))))]
      _ = b (a (c (d (b (d (c (b (a (b (c (d x))))))))))) := by
        rw [(hbd (c (b (a (b (c (d x))))))).symm]
      _ = b (a (c (d (b (c (d (b (a (b (c (d x))))))))))) := by
        rw [(hcd (b (a (b (c (d x)))))).symm]
      _ = b (a (c (d (b (c (d (a (b (a (c (d x))))))))))) := by
        rw [(hba (c (d x))).symm]
      _ = b (a (c (d (b (c (a (d (b (a (c (d x))))))))))) := by
        rw [(had (b (a (c (d x))))).symm]
      _ = b (a (c (d (b (a (c (d (b (a (c (d x))))))))))) := by
        rw [(hac (d (b (a (c (d x)))))).symm]

end Words

/-! ### The Cartan matrices of types `A₃` and `D₄` -/

theorem _root_.CartanMatrix.isGeneralizedCartan_A_three :
    (CartanMatrix.A 3).IsGeneralizedCartan where
  diag := by decide
  offDiag_nonpos i j h := by fin_cases i <;> fin_cases j <;> simp_all [CartanMatrix.A]
  zero_comm i j := by fin_cases i <;> fin_cases j <;> simp [CartanMatrix.A]

theorem _root_.CartanMatrix.isGeneralizedCartan_D_four :
    (CartanMatrix.D 4).IsGeneralizedCartan where
  diag := by decide
  offDiag_nonpos i j h := by fin_cases i <;> fin_cases j <;> simp_all [CartanMatrix.D]
  zero_comm i j := by fin_cases i <;> fin_cases j <;> simp [CartanMatrix.D]

theorem _root_.CartanMatrix.det_map_A_three_ne_zero :
    ((CartanMatrix.A 3).map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  have h : ((CartanMatrix.A 3).det : ℝ) = ((CartanMatrix.A 3).map (Int.cast : ℤ → ℝ)).det :=
    Int.cast_det _
  rw [← h, show (CartanMatrix.A 3).det = 4 by decide]
  norm_num

theorem _root_.CartanMatrix.det_map_D_four_ne_zero :
    ((CartanMatrix.D 4).map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  have h : ((CartanMatrix.D 4).det : ℝ) = ((CartanMatrix.D 4).map (Int.cast : ℤ → ℝ)).det :=
    Int.cast_det _
  rw [← h, show (CartanMatrix.D 4).det = 4 by decide]
  norm_num

/-! ### Rank two -/

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- **The `B₂` braid relation on the rank-two path crystals** `B(μ)`: for a realization of a
generalized Cartan matrix with `a₀₁ = -1`, `a₁₀ = -2`, `S₀S₁S₀S₁ = S₁S₀S₁S₀` on the component of
the straight line path `π_μ`, `μ` dominant integral. Proof by folding `A₃ → B₂`. -/
theorem reflection_braid_four_of_B2 {B : Matrix (Fin 2) (Fin 2) ℤ} {hB : B.IsGeneralizedCartan}
    (h01 : B 0 1 = -1) (h10 : B 1 0 = -2) (Q : Realization B ℝ H) {μ : Dual ℝ H}
    (hμ : Q.IsDominantIntegral μ) {π : LittelmannPath (Q.pathSpace hB)}
    (hπ : π ∈ (straightLine (Q.pathSpace hB) ⟨μ, hμ.mem_integralWeights⟩).component) :
    (crystal (Q.pathSpace hB)).reflection 0 ((crystal (Q.pathSpace hB)).reflection 1
      ((crystal (Q.pathSpace hB)).reflection 0 ((crystal (Q.pathSpace hB)).reflection 1 π))) =
    (crystal (Q.pathSpace hB)).reflection 1 ((crystal (Q.pathSpace hB)).reflection 0
      ((crystal (Q.pathSpace hB)).reflection 1 ((crystal (Q.pathSpace hB)).reflection 0 π))) := by
  let R := Realization.std (CartanMatrix.A 3) ℝ
  have hR := CartanMatrix.isGeneralizedCartan_A_three
  let F : FoldMap Q R := FoldMap.ofSpan Q R
    (span_coroot_eq_top_of_det_map_ne_zero R CartanMatrix.det_map_A_three_ne_zero)
    ![0, 1, 0] ![[0, 2], [1]] (by decide) (by decide) (by decide)
    (fun a b h1 h2 => by fin_cases a <;> fin_cases b <;> simp_all [CartanMatrix.A]) (by
      intro b k
      fin_cases b <;> fin_cases k <;> simp [CartanMatrix.A_three, h01, h10, hB.diag])
  have hdetQ : (B.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [h01, h10, hB.diag]
    norm_num
  have hinj := F.fold_injective (hA := hB) (hA' := hR)
    (F.injective_of_span (span_coroot_eq_top_of_det_map_ne_zero Q hdetQ))
  have hψ := F.isDominantIntegral hμ
  have hmem : F.fold (hA' := hR) π ∈
      (straightLine (R.pathSpace hR) ⟨F.toLinearMap μ, hψ.mem_integralWeights⟩).component := by
    have := F.fold_mem_component (hA' := hR) hπ
    rwa [FoldMap.fold_straightLine] at this
  have h0 : ∀ x, F.fold (hA' := hR) ((crystal (Q.pathSpace hB)).reflection 0 x) =
      (crystal (R.pathSpace hR)).reflection 0 ((crystal (R.pathSpace hR)).reflection 2
        (F.fold x)) := F.fold_reflection_of_orbit_eq_pair rfl
  have h1 : ∀ x, F.fold (hA' := hR) ((crystal (Q.pathSpace hB)).reflection 1 x) =
      (crystal (R.pathSpace hR)).reflection 1 (F.fold x) :=
    F.fold_reflection_of_orbit_eq_singleton rfl
  apply hinj
  simp only [h0, h1]
  have key := braid_word_A3 ((R.pathCrystal hR hψ).reflection 0)
    ((R.pathCrystal hR hψ).reflection 1) ((R.pathCrystal hR hψ).reflection 2)
    (pathCrystal_reflection_comm hR hψ (by decide))
    (pathCrystal_reflection_braid_three hR hψ (by decide) (by decide))
    (pathCrystal_reflection_braid_three hR hψ (by decide) (by decide)) ⟨_, hmem⟩
  have key' := congrArg Subtype.val key
  simp only [coe_reflection_pathCrystal] at key'
  exact key'

/-- **The `G₂` braid relation on the rank-two path crystals** `B(μ)`: for a realization of a
generalized Cartan matrix with `a₀₁ = -1`, `a₁₀ = -3`, `(S₀S₁)³ = (S₁S₀)³` on the component of the
straight line path `π_μ`, `μ` dominant integral. Proof by folding `D₄ → G₂`. -/
theorem reflection_braid_six_of_G2 {B : Matrix (Fin 2) (Fin 2) ℤ} {hB : B.IsGeneralizedCartan}
    (h01 : B 0 1 = -1) (h10 : B 1 0 = -3) (Q : Realization B ℝ H) {μ : Dual ℝ H}
    (hμ : Q.IsDominantIntegral μ) {π : LittelmannPath (Q.pathSpace hB)}
    (hπ : π ∈ (straightLine (Q.pathSpace hB) ⟨μ, hμ.mem_integralWeights⟩).component) :
    (crystal (Q.pathSpace hB)).reflection 0 ((crystal (Q.pathSpace hB)).reflection 1
      ((crystal (Q.pathSpace hB)).reflection 0 ((crystal (Q.pathSpace hB)).reflection 1
        ((crystal (Q.pathSpace hB)).reflection 0 ((crystal (Q.pathSpace hB)).reflection 1
          π))))) =
    (crystal (Q.pathSpace hB)).reflection 1 ((crystal (Q.pathSpace hB)).reflection 0
      ((crystal (Q.pathSpace hB)).reflection 1 ((crystal (Q.pathSpace hB)).reflection 0
        ((crystal (Q.pathSpace hB)).reflection 1 ((crystal (Q.pathSpace hB)).reflection 0
          π))))) := by
  let R := Realization.std (CartanMatrix.D 4) ℝ
  have hR := CartanMatrix.isGeneralizedCartan_D_four
  let F : FoldMap Q R := FoldMap.ofSpan Q R
    (span_coroot_eq_top_of_det_map_ne_zero R CartanMatrix.det_map_D_four_ne_zero)
    ![0, 1, 0, 0] ![[0, 2, 3], [1]] (by decide) (by decide) (by decide)
    (fun a b h1 h2 => by fin_cases a <;> fin_cases b <;> simp_all [CartanMatrix.D]) (by
      intro b k
      fin_cases b <;> fin_cases k <;> simp [CartanMatrix.D_four, h01, h10, hB.diag])
  have hdetQ : (B.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [h01, h10, hB.diag]
    norm_num
  have hinj := F.fold_injective (hA := hB) (hA' := hR)
    (F.injective_of_span (span_coroot_eq_top_of_det_map_ne_zero Q hdetQ))
  have hψ := F.isDominantIntegral hμ
  have hmem : F.fold (hA' := hR) π ∈
      (straightLine (R.pathSpace hR) ⟨F.toLinearMap μ, hψ.mem_integralWeights⟩).component := by
    have := F.fold_mem_component (hA' := hR) hπ
    rwa [FoldMap.fold_straightLine] at this
  have h0 : ∀ x, F.fold (hA' := hR) ((crystal (Q.pathSpace hB)).reflection 0 x) =
      (crystal (R.pathSpace hR)).reflection 0 ((crystal (R.pathSpace hR)).reflection 2
        ((crystal (R.pathSpace hR)).reflection 3 (F.fold x))) :=
    F.fold_reflection_of_orbit_eq_triple rfl
  have h1 : ∀ x, F.fold (hA' := hR) ((crystal (Q.pathSpace hB)).reflection 1 x) =
      (crystal (R.pathSpace hR)).reflection 1 (F.fold x) :=
    F.fold_reflection_of_orbit_eq_singleton rfl
  apply hinj
  simp only [h0, h1]
  have key := braid_word_D4 ((R.pathCrystal hR hψ).reflection 0)
    ((R.pathCrystal hR hψ).reflection 1) ((R.pathCrystal hR hψ).reflection 2)
    ((R.pathCrystal hR hψ).reflection 3)
    (pathCrystal_reflection_comm hR hψ (by decide))
    (pathCrystal_reflection_comm hR hψ (by decide))
    (pathCrystal_reflection_comm hR hψ (by decide))
    (pathCrystal_reflection_braid_three hR hψ (by decide) (by decide))
    (pathCrystal_reflection_braid_three hR hψ (by decide) (by decide))
    (pathCrystal_reflection_braid_three hR hψ (by decide) (by decide)) ⟨_, hmem⟩
  have key' := congrArg Subtype.val key
  simp only [coe_reflection_pathCrystal] at key'
  exact key'

/-! ### All generalized Cartan matrices -/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ} {P : Realization A ℝ H}
  (hA : A.IsGeneralizedCartan) {Λ : Dual ℝ H}

omit [DecidableEq ι] in
/-- The Coxeter relation `(SᵢSⱼ)^m = 1` on `B(Λ)` from the corresponding iterate on paths. -/
theorem pathReflectionPerm_mul_pow_eq_one (hΛ : P.IsDominantIntegral Λ) {i j : ι} {m : ℕ}
    (h : ∀ x ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component,
      ((crystal (P.pathSpace hA)).reflection i ∘ (crystal (P.pathSpace hA)).reflection j)^[m] x =
        x) :
    (pathReflectionPerm P hA hΛ i * pathReflectionPerm P hA hΛ j) ^ m = 1 := by
  have hsemi : Function.Semiconj Subtype.val
      (pathReflectionPerm P hA hΛ i * pathReflectionPerm P hA hΛ j)
      ((crystal (P.pathSpace hA)).reflection i ∘ (crystal (P.pathSpace hA)).reflection j) :=
    fun b => by
      simp only [Equiv.Perm.mul_apply, Crystal.IsSeminormal.reflectionPerm_apply,
        Function.comp_apply, coe_reflection_pathCrystal]
  refine Equiv.ext fun b => Subtype.ext ?_
  rw [Equiv.Perm.coe_pow, (hsemi.iterate_right m) b, Equiv.Perm.one_apply]
  exact h b.1 b.2

/-- In a group, `(ab)ⁿ = 1` if `(ba)ⁿ = 1`. -/
lemma mul_pow_eq_one_of_swap {G : Type*} [Group G] {a b : G} {n : ℕ} (h : (b * a) ^ n = 1) :
    (a * b) ^ n = 1 := by
  have : a * b = a * (b * a) * a⁻¹ := by group
  rw [this, conj_pow, h, mul_one, mul_inv_cancel]

omit [DecidableEq ι] in
/-- The rank-two relation `(S_{e 0} S_{e 1})^m = 1` on `B(Λ)` from the same relation on all
straight-line path crystals of one rank-two realization of the principal submatrix. -/
theorem iterate_reflection_eq_of_rankTwo (hΛ : P.IsDominantIntegral Λ) {i j : ι} (hij : i ≠ j)
    (m : ℕ) (hQ : ∀ {H' : Type} [AddCommGroup H'] [Module ℝ H']
      (hA' : (A.submatrix ![i, j] ![i, j]).IsGeneralizedCartan)
      (Q : Realization (A.submatrix ![i, j] ![i, j]) ℝ H') (μ : Dual ℝ H')
      (hμ : Q.IsDominantIntegral μ),
      ∀ z ∈ (straightLine (Q.pathSpace hA') ⟨μ, hμ.mem_integralWeights⟩).component,
        ((crystal (Q.pathSpace hA')).reflection 0 ∘
          (crystal (Q.pathSpace hA')).reflection 1)^[m] z = z)
    {x : LittelmannPath (P.pathSpace hA)}
    (hx : x ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ((crystal (P.pathSpace hA)).reflection i ∘ (crystal (P.pathSpace hA)).reflection j)^[m] x =
      x := by
  have : FiniteDimensional ℝ H := by
    have : Nonempty ι := ⟨i⟩
    apply Module.finite_of_finrank_pos
    have h1 := P.finrank_add_rank
    have h2 := (A.map (Int.cast : ℤ → ℝ)).rank_le_card_width
    have h3 : 0 < Fintype.card ι := Fintype.card_pos
    omega
  have he : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have hA' := LSGeneralClass.isGeneralizedCartan_submatrix hA he
  let Q := Realization.std (A.submatrix ![i, j] ![i, j]) ℝ
  obtain ⟨L⟩ := LSGeneralClass.exists_leviMap (P := P) he Q
  exact L.iterate_reflection_eq_of_levi (hA' := hA') 0 1 m (fun μ hμ z hz => hQ hA' Q μ hμ z hz)
    hΛ hx

omit [DecidableEq ι] in
/-- `(SᵢSⱼ)⁴ = 1` on `B(Λ)` when `aᵢⱼ = -1` and `aⱼᵢ = -2`. -/
theorem iterate_reflection_four (hΛ : P.IsDominantIntegral Λ) {i j : ι} (hij : A i j = -1)
    (hji : A j i = -2) {x : LittelmannPath (P.pathSpace hA)}
    (hx : x ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ((crystal (P.pathSpace hA)).reflection i ∘ (crystal (P.pathSpace hA)).reflection j)^[4] x =
      x := by
  have hne : i ≠ j := fun h => by subst h; rw [hA.diag] at hij; norm_num at hij
  refine iterate_reflection_eq_of_rankTwo hA hΛ hne 4 (fun hA' Q μ hμ z hz => ?_) hx
  have hC := isSeminormal_crystal (Q.pathSpace hA')
  have hS := isStable_component (straightLine (Q.pathSpace hA') ⟨μ, hμ.mem_integralWeights⟩)
  change (crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    z))))))) = z
  rw [reflection_braid_four_of_B2 (by simpa using hij) (by simpa using hji) Q hμ
    (hS.reflection_mem (hS.reflection_mem (hS.reflection_mem (hS.reflection_mem hz))))]
  simp only [hC.reflection_reflection]

omit [DecidableEq ι] in
/-- `(SᵢSⱼ)⁶ = 1` on `B(Λ)` when `aᵢⱼ = -1` and `aⱼᵢ = -3`. -/
theorem iterate_reflection_six (hΛ : P.IsDominantIntegral Λ) {i j : ι} (hij : A i j = -1)
    (hji : A j i = -3) {x : LittelmannPath (P.pathSpace hA)}
    (hx : x ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ((crystal (P.pathSpace hA)).reflection i ∘ (crystal (P.pathSpace hA)).reflection j)^[6] x =
      x := by
  have hne : i ≠ j := fun h => by subst h; rw [hA.diag] at hij; norm_num at hij
  refine iterate_reflection_eq_of_rankTwo hA hΛ hne 6 (fun hA' Q μ hμ z hz => ?_) hx
  have hC := isSeminormal_crystal (Q.pathSpace hA')
  have hS := isStable_component (straightLine (Q.pathSpace hA') ⟨μ, hμ.mem_integralWeights⟩)
  change (crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
    z))))))))))) = z
  rw [reflection_braid_six_of_G2 (by simpa using hij) (by simpa using hji) Q hμ
    (π := (crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
      ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
      ((crystal (Q.pathSpace hA')).reflection 0 ((crystal (Q.pathSpace hA')).reflection 1
      z))))))
    (hS.reflection_mem (hS.reflection_mem (hS.reflection_mem (hS.reflection_mem
      (hS.reflection_mem (hS.reflection_mem hz))))))]
  simp only [hC.reflection_reflection]

/-- **The braid relations on `B(Λ)` for every generalized Cartan matrix**: Kashiwara's
reflections satisfy `(SᵢSⱼ)^{mᵢⱼ} = 1` for all pairs with `aᵢⱼaⱼᵢ ∈ {1, 2, 3}` (types `A₂`,
`B₂`, `G₂`; the relations for the other pairs hold by `isLiftable_pathReflectionPerm`). Hence
Kashiwara's reflections extend to an action of the Weyl group on `B(Λ)` with `sᵢ ↦ Sᵢ`, for
every generalized Cartan matrix (`Matrix.Realization.pathWeylAction`). -/
theorem pathBraidRelations (hΛ : P.IsDominantIntegral Λ) : P.PathBraidRelations hA hΛ := by
  intro i j hij hA0 hM
  have hn := hA.offDiag_nonpos i j hij
  have hn' := hA.offDiag_nonpos j i (Ne.symm hij)
  have hA0' : A j i ≠ 0 := fun h => hA0 ((hA.zero_comm i j).mpr h)
  have ha : A i j ≤ -1 := by omega
  have hb : A j i ≤ -1 := by omega
  have hp : A i j * A j i ≤ 3 := by
    by_contra h
    apply hM
    rw [A.coxeterMatrix_apply_of_ne hij]
    exact coxeterEntry_of_four_le (by omega)
  have ha' : -3 ≤ A i j := by nlinarith
  have hb' : -3 ≤ A j i := by nlinarith
  have hm : ∀ n : ℕ, A i j * A j i = n → A.coxeterMatrix i j = coxeterEntry n := fun n hn => by
    rw [A.coxeterMatrix_apply_of_ne hij, hn, Int.toNat_natCast]
  obtain ⟨p, hp1, hp2, hp3⟩ : ∃ p : ℤ, A i j = p ∧ -3 ≤ p ∧ p ≤ -1 := ⟨_, rfl, ha', ha⟩
  obtain ⟨q, hq1, hq2, hq3⟩ : ∃ q : ℤ, A j i = q ∧ -3 ≤ q ∧ q ≤ -1 := ⟨_, rfl, hb', hb⟩
  rw [hp1, hq1] at hp
  interval_cases p <;> interval_cases q <;> norm_num at hp
  all_goals first
    | rw [hm 1 (by rw [hp1, hq1]; norm_num)]
      exact pathReflectionPerm_mul_pow_three hA hΛ hp1 hq1
    | rw [hm 2 (by rw [hp1, hq1]; norm_num)]
      exact pathReflectionPerm_mul_pow_eq_one hA hΛ
        fun x hx => iterate_reflection_four hA hΛ hp1 hq1 hx
    | rw [hm 2 (by rw [hp1, hq1]; norm_num)]
      exact mul_pow_eq_one_of_swap (pathReflectionPerm_mul_pow_eq_one hA hΛ
        fun x hx => iterate_reflection_four hA hΛ hq1 hp1 hx)
    | rw [hm 3 (by rw [hp1, hq1]; norm_num)]
      exact pathReflectionPerm_mul_pow_eq_one hA hΛ
        fun x hx => iterate_reflection_six hA hΛ hp1 hq1 hx
    | rw [hm 3 (by rw [hp1, hq1]; norm_num)]
      exact mul_pow_eq_one_of_swap (pathReflectionPerm_mul_pow_eq_one hA hΛ
        fun x hx => iterate_reflection_six hA hΛ hq1 hp1 hx)

end General

end Matrix.Realization
