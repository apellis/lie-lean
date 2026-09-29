/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.GluingPause
import LieLean.LinearAlgebra.Matrix.Cartan.Symmetrizable

/-!
# Endpoint rigidity for the final source of a gluing pair

## Main results

`Presentation.directions_eq_of_tail_endpoint` proves the final rigidity step in
Littelmann Proposition 5.7: a source chain from an auxiliary weight to the first
slope, together with the exact retained-tail displacement, forces every slope to
be that auxiliary weight. The weight may lie outside the Tits cone.

## References

Littelmann, *Paths and root operators in representation theory*, Ann. Math. 142
(1995), Proposition 5.7, printed p. 516, final three lines of its proof. The proof below reconstructs the omitted positive-root-cone
rigidity argument using the separating functional rhoCheck. Finite-dimensional
Cartan space is explicit. This is a necessary lemma, NOT highest-path uniqueness
or an isomorphism theorem. No output integrality or word relation is assumed.
-/

open Module Set LittelmannPath LittelmannPath.FiniteConstruction

namespace Matrix.Realization.LSGeneralClass

variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℝ H]
  [FiniteDimensional ℝ H] {A : Matrix ι ι ℤ} {P : Realization A ℝ H}
  {hA : A.IsGeneralizedCartan}

/-- Every actual descending source step strictly increases evaluation on rhoCheck.
This has the source order orientation, which is opposite to usual weight order. -/
theorem RootStep.rhoCheck_lt {x y : Dual ℝ H} {c : Dual ℝ (Dual ℝ H)}
    (h : RootStep P hA x y c) : x P.rhoCheck < y P.rhoCheck := by
  classical
  obtain ⟨u, j, ⟨k, hk, he⟩, -, hn, hy⟩ := h
  have hkne : k ≠ 0 := by
    intro hz
    have hr : u.1 (P.root j) = 0 := by simpa [hz] using he
    have hr' : P.root j = 0 := u.1.injective (hr.trans (map_zero u.1).symm)
    have hc := congrArg (fun z : Dual ℝ H => z (P.coroot j)) hr'
    simp [P.root_coroot, hA.diag] at hc
  have hp : (0 : ℝ) < P.rootOf k P.rhoCheck := by
    rw [P.rootOf_rhoCheck]
    have hex : ∃ i, k i ≠ 0 := by
      by_contra! hn
      exact hkne (funext hn)
    obtain ⟨i, hi⟩ := hex
    have hp : 0 < ∑ j, k j := Finset.sum_pos'
      (fun j _ => hk j) ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hk i) (Ne.symm hi)⟩
    exact_mod_cast hp
  rw [hy, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, he]
  linarith [mul_neg_of_neg_of_pos hn hp]

/-- A source time chain is either literally constant or strictly increases the
separating functional; no dominant-orbit premise is needed. -/
theorem AChain.eq_or_rhoCheck_lt {x y : Dual ℝ H} {a : ℝ}
    (h : AChain P hA a x y) : x = y ∨ x P.rhoCheck < y P.rhoCheck := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail y z _ hyz ih =>
    obtain ⟨c, hc, -⟩ := hyz
    have hz := hc.1.rhoCheck_lt
    exact Or.inr (ih.elim (fun hxy => hxy ▸ hz) (fun hxy => hxy.trans hz))

/-- The same rigidity remains valid across chains at DIFFERENT break times.
The initial auxiliary chain is the actual source right-cut hypothesis. -/
theorem Presentation.aux_eq_or_rhoCheck_lt (σ : Presentation P hA)
    {μ : Dual ℝ H} {s : ℝ} (hc : AChain P hA s μ (σ.x 0))
    (j : Fin (σ.n + 1)) : μ = (σ.x j : Dual ℝ H) ∨
      μ P.rhoCheck < (σ.x j : Dual ℝ H) P.rhoCheck := by
  induction j using Fin.induction with
  | zero => exact hc.eq_or_rhoCheck_lt
  | succ j ih =>
    rcases (σ.chains j).eq_or_rhoCheck_lt with he | hl
    · simpa only [← he] using ih
    · exact Or.inr (ih.elim (fun he => he ▸ hl) (fun hi => hi.trans hl))

/-- A positive weighted average cannot equal the lower source direction unless
all directions coincide. This uses actual source-chain conclusions, not an
assumed antisymmetric order or a positive-definite invariant form. -/
theorem Presentation.directions_eq_of_positive_average (σ : Presentation P hA)
    {μ : Dual ℝ H} {s : ℝ} (hc : AChain P hA s μ (σ.x 0))
    (b : Fin (σ.n + 1) → ℝ) (hb : ∀ j, 0 < b j)
    (he : ∑ j, b j • (σ.x j : Dual ℝ H) = (∑ j, b j) • μ) :
    ∀ j, (σ.x j : Dual ℝ H) = μ := by
  classical
  have hnonneg (j) : 0 ≤ b j * ((σ.x j : Dual ℝ H) P.rhoCheck - μ P.rhoCheck) := by
    apply mul_nonneg (hb j).le
    exact sub_nonneg.mpr ((σ.aux_eq_or_rhoCheck_lt hc j).elim
      (fun h => by rw [h]) (fun h => h.le))
  have hsum : ∑ j, b j * ((σ.x j : Dual ℝ H) P.rhoCheck - μ P.rhoCheck) = 0 := by
    have hv := congrArg (fun z : Dual ℝ H => z P.rhoCheck) he
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hv
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hv, sub_self]
  intro j
  have hj : b j * ((σ.x j : Dual ℝ H) P.rhoCheck - μ P.rhoCheck) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnonneg k)).mp hsum j (Finset.mem_univ j)
  rcases σ.aux_eq_or_rhoCheck_lt hc j with heq | hlt
  · exact heq.symm
  · have hp := mul_pos (hb j) (sub_pos.mpr hlt)
    linarith

omit [FiniteDimensional ℝ H] in
/-- Positive durations of every retained piece when the cut is STRICTLY inside
(or before) the first piece, as required by source Definition 5.3. -/
theorem Presentation.tail_duration_pos (σ : Presentation P hA) {s : ℝ}
    (hs : s < (σ.a (0 : Fin (σ.n + 1)).succ : ℝ)) (j : Fin (σ.n + 1)) :
    0 < (σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ) - if j = 0 then s else 0 := by
  classical
  by_cases hj : j = 0
  · subst j
    simpa [σ.zero] using sub_pos.mpr hs
  · simp only [hj, ite_false, sub_zero]
    exact sub_pos.mpr (by exact_mod_cast σ.mono (Fin.castSucc_lt_succ (i := j)))

omit [FiniteDimensional ℝ H] in
/-- The retained durations sum to the literal remaining time, not to a normalized
unit interval. -/
theorem Presentation.sum_tail_duration (σ : Presentation P hA) (s : ℝ) :
    (∑ j : Fin (σ.n + 1),
      ((σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ) - if j = 0 then s else 0)) = 1 - s := by
  classical
  have h₁ := Fin.sum_univ_succ (fun j : Fin (σ.n + 2) => (σ.a j : ℝ))
  have h₂ := Fin.sum_univ_castSucc (fun j : Fin (σ.n + 2) => (σ.a j : ℝ))
  simp only [σ.zero, σ.one, Rat.cast_zero, Rat.cast_one, zero_add] at h₁ h₂
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  linarith

omit [FiniteDimensional ℝ H] in
/-- The actual finite path's retained displacement is its positive weighted sum
of source directions; no new path or endpoint field is supplied. -/
theorem Presentation.tail_displacement (σ : Presentation P hA) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (σ.a (0 : Fin (σ.n + 1)).succ : ℝ)) :
    σ.path 1 - σ.path s = ∑ j : Fin (σ.n + 1),
      ((σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ) - if j = 0 then s else 0) •
        (σ.x j : Dual ℝ H) := by
  classical
  have hend : σ.path 1 = ∑ j : Fin (σ.n + 1),
      ((σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ)) • (σ.x j : Dual ℝ H) := by
    change raw (P.pathSpace hA) σ.a σ.x 1 = _
    unfold raw
    apply Finset.sum_congr rfl
    intro j _
    have hj : (σ.a j.succ : ℝ) ≤ 1 := by
      have h := σ.mono.monotone (Fin.le_last j.succ)
      rw [σ.one] at h
      exact_mod_cast h
    have hp : 0 ≤ (σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ) := by
      exact sub_nonneg.mpr (by exact_mod_cast σ.mono.monotone Fin.castSucc_lt_succ.le)
    simp only [min_eq_right hj, max_eq_right hp, pathSpace_embed]
  rw [hend, σ.first_piece s hs]
  have hh (j : Fin (σ.n + 1)) :
      ((σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ) - if j = 0 then s else 0) •
          (σ.x j : Dual ℝ H) =
        ((σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ)) • (σ.x j : Dual ℝ H) -
          (if j = 0 then s else 0) • (σ.x j : Dual ℝ H) :=
    @sub_smul ℝ (Dual ℝ H) _ _ _
      ((σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ)) (if j = 0 then s else 0)
      (σ.x j : Dual ℝ H)
  simp_rw [hh]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp

/-- The exact last rigidity step of Proposition 5.7 (p. 516). The original
auxiliary weight may be arbitrary. The strict right cut and actual cut chain
make every retained duration positive and every direction lie above the auxiliary.
Equality of the retained endpoint displacement therefore forces all slopes equal. -/
theorem Presentation.directions_eq_of_tail_endpoint (σ : Presentation P hA)
    {μ : Dual ℝ H} {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < (σ.a (0 : Fin (σ.n + 1)).succ : ℝ))
    (hc : AChain P hA s μ (σ.x 0))
    (he : σ.path 1 - σ.path s = (1 - s) • μ) :
    ∀ j, (σ.x j : Dual ℝ H) = μ := by
  apply σ.directions_eq_of_positive_average hc
    (fun j => (σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ) - if j = 0 then s else 0)
    (σ.tail_duration_pos hs)
  rw [σ.sum_tail_duration, ← σ.tail_displacement ⟨hs0, hs.le⟩]
  exact he

omit [FiniteDimensional ℝ H] in
/-- The finite clamped durations partition the actual parameter interval. -/
theorem Presentation.sum_piece_duration (σ : Presentation P hA) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∑ j : Fin (σ.n + 1),
      max 0 (min t (σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ))) = t := by
  have hterm (j : Fin (σ.n + 1)) :
      max 0 (min t (σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ)) =
        min t (σ.a j.succ : ℝ) - min t (σ.a j.castSucc : ℝ) := by
    have hj : (σ.a j.castSucc : ℝ) ≤ (σ.a j.succ : ℝ) := by
      exact_mod_cast σ.mono.monotone Fin.castSucc_lt_succ.le
    by_cases h : t ≤ (σ.a j.castSucc : ℝ)
    · rw [min_eq_left (h.trans hj), min_eq_left h, max_eq_left (sub_nonpos.mpr h)]
      exact (sub_self t).symm
    · have h' := le_of_not_ge h
      rw [min_eq_right h', max_eq_right (sub_nonneg.mpr (le_min h' hj))]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ (fun j : Fin (σ.n + 2) => min t (σ.a j : ℝ))
  have h₂ := Fin.sum_univ_castSucc (fun j : Fin (σ.n + 2) => min t (σ.a j : ℝ))
  simp only [σ.zero, σ.one, Rat.cast_zero, Rat.cast_one,
    min_eq_right ht.1, min_eq_left ht.2, zero_add] at h₁ h₂
  linarith

omit [FiniteDimensional ℝ H] in
/-- Constant source directions give literal equality on the unit interval;
redundant finite subdivisions do not change the parametrized path. -/
theorem Presentation.path_eq_smul_of_directions_eq (σ : Presentation P hA)
    {μ : Dual ℝ H} (hd : ∀ j, (σ.x j : Dual ℝ H) = μ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : σ.path t = t • μ := by
  change (∑ j : Fin (σ.n + 1),
    max 0 (min t (σ.a j.succ : ℝ) - (σ.a j.castSucc : ℝ)) •
      (σ.x j : Dual ℝ H)) = _
  simp_rw [hd]
  rw [← Finset.sum_smul, σ.sum_piece_duration ht]

/-- The rigidity conclusion is equality of actual paths, not just of endpoints
or weights. This is the final-source conclusion in Proposition 5.7's proof. -/
theorem Presentation.path_eq_straight_of_tail_endpoint (σ : Presentation P hA)
    {μ : Dual ℝ H} {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < (σ.a (0 : Fin (σ.n + 1)).succ : ℝ))
    (hc : AChain P hA s μ (σ.x 0))
    (he : σ.path 1 - σ.path s = (1 - s) • μ) :
    σ.path = straightLine (P.pathSpace hA) (σ.x 0) := by
  have hd := σ.directions_eq_of_tail_endpoint hs0 hs hc he
  apply ext_of_eqOn
  intro t ht
  rw [σ.path_eq_smul_of_directions_eq hd ht, straightLine_apply,
    min_eq_right ht.2, max_eq_right ht.1]
  exact congrArg (t • ·) (hd 0).symm

/-- Consume the production gluing pair's actual right chain and STRICT cut.
An exact normalized endpoint forces its entire right source to be straight,
even for nondominant auxiliary weights. No highest-weight or isomorphism result
is smuggled into this local rigidity theorem. -/
theorem GluingPair.right_source_rigidity {σ δ : Presentation P hA} (g : GluingPair σ δ)
    (he : g.path 1 = σ.path g.s + (1 - (g.s' : ℝ)) • g.μ) :
    (∀ j, (δ.x j : Dual ℝ H) = g.μ) ∧
      δ.path = straightLine (P.pathSpace hA) (δ.x 0) := by
  have hs : (g.s' : ℝ) < (δ.a (0 : Fin (δ.n + 1)).succ : ℝ) := by
    exact_mod_cast g.first_gt
  have hdisp : δ.path 1 - δ.path g.s' = (1 - (g.s' : ℝ)) • g.μ := by
    have hg := g.raw_right (t := 1) (by exact_mod_cast g.lt_one.le)
    change g.path 1 = _ at hg
    rw [he] at hg
    calc
      δ.path 1 - δ.path g.s' =
          (δ.path 1 + (σ.path g.s - δ.path g.s')) - σ.path g.s := by abel
      _ = (σ.path g.s + (1 - (g.s' : ℝ)) • g.μ) - σ.path g.s := by rw [← hg]
      _ = (1 - (g.s' : ℝ)) • g.μ := by abel
  exact ⟨δ.directions_eq_of_tail_endpoint g.right_cut_mem.1 hs g.right_chain hdisp,
    δ.path_eq_straight_of_tail_endpoint g.right_cut_mem.1 hs g.right_chain hdisp⟩

/-- The normalized ORIGINAL-endpoint-fibre rigidity reduction of Proposition 5.7.
Once the first source has its original straight direction and the second auxiliary
has been restored to the original weight, the entire gluing path is forced to be
the original two-piece path. These normalization premises are explicit: deriving
them from highestness and common Weyl transport is a SEPARATE remaining argument. -/
theorem twoPieceGluing_fibre_eq_of_normalized (Λ μ : Dual ℝ H) (n : ℕ) (hn : 2 ≤ n)
    (hΛ : (n : ℝ) • Λ ∈ P.integralWeights)
    (hμ : (n : ℝ) • μ ∈ P.integralWeights)
    (hsum : Λ + μ ∈ P.integralWeights) (hp : P.GluingPrecedes hA Λ μ)
    {τ ρ : Presentation P hA} (g : GluingPair τ ρ)
    (hs : g.s = (n : ℚ)⁻¹) (hs' : g.s' = 1 - (n : ℚ)⁻¹)
    (hl : ∀ j, (τ.x j : Dual ℝ H) = (n : ℝ) • Λ)
    (haux : g.μ = (n : ℝ) • μ) (he : g.path 1 = Λ + μ) :
    g.path = (twoPieceGluing Λ μ n hn hΛ hμ hsum hp).path := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hsr : (g.s : ℝ) = (n : ℝ)⁻¹ := by simp only [hs, Rat.cast_inv, Rat.cast_natCast]
  have hs'r : (g.s' : ℝ) = 1 - (n : ℝ)⁻¹ := by
    simp only [hs', Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast]
  have hcut : τ.path g.s = Λ := by
    rw [τ.path_eq_smul_of_directions_eq hl
      ⟨by exact_mod_cast g.pos.le, by exact_mod_cast g.le.trans g.lt_one.le⟩,
      hsr, smul_smul, inv_mul_cancel₀ hnpos.ne', one_smul]
  have hr := (g.right_source_rigidity (by
    rw [he, hcut, haux, hs'r, sub_sub_cancel, smul_smul,
      inv_mul_cancel₀ hnpos.ne', one_smul])).1
  have hτ : τ.path =
      (Presentation.straight (hA := hA) ⟨(n : ℝ) • Λ, hΛ⟩).path := by
    apply ext_of_eqOn
    intro t ht
    rw [τ.path_eq_smul_of_directions_eq hl ht, Presentation.straight_path _ ht]
  have hρ : ρ.path =
      (Presentation.straight (hA := hA) ⟨(n : ℝ) • μ, hμ⟩).path := by
    apply ext_of_eqOn
    intro t ht
    rw [ρ.path_eq_smul_of_directions_eq hr ht, haux, Presentation.straight_path _ ht]
  apply ext_of_eqOn
  intro t _
  change glueRaw τ ρ g.s g.s' t = glueRaw _ _ (n : ℚ)⁻¹ (1 - (n : ℚ)⁻¹) t
  simp only [glueRaw, hτ, hρ, hs, hs']

end Matrix.Realization.LSGeneralClass
