/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.TranslationFacet
import LieLean.Algebra.Lie.KacMoody.HarishChandraLinkage
import LieLean.Algebra.Lie.KacMoody.CentralTensorFiltration
import LieLean.Algebra.Lie.KacMoody.FiniteDimensional

/-!
# Translation of Verma modules (integral weights, finite type)

Let `A` be of finite type over an algebraically closed field of characteristic zero, `λ, μ`
integral weights with `λ + ρ`, `μ + ρ` antidominant and `μ` in the closure of the facet of `λ`,
and `ν` the dominant weight in `W (μ - λ)`. For every `w ∈ W`, the `χ_μ`-block of
`M(w·λ) ⊗ L(ν)` is isomorphic to `M(w·μ)`: the translation functor `T_λ^μ` sends `M(w·λ)`
to `M(w·μ)`.

## Main results

* `LieSubmodule.map_mk'_eq_bot_iff`, `LieSubmodule.eq_bot_and_eq_last_of_single_step`:
  a monotone filtration starting at `⊥` with a single nonzero step.
* `Matrix.Realization.KacMoodyAlgebra.translation_verma`: `pr_{χ_μ}(M(w·λ) ⊗ L(ν)) ≅ M(w·μ)`.

## Proof

`M(w·λ) ⊗ L(ν)` has a standard filtration with factors `M(w·λ + ν')`, `ν'` running over the
weights of `L(ν)` with multiplicity (`exists_tensorVermaStandardFiltration`), and projecting to
the `χ_μ`-block keeps exactly the factors with central character `χ_μ`
(`exists_centralTensorVermaFiltration`). By linkage (`VermaModule.centralCharacter_eq_iff`)
such a factor has `w·λ + ν' ∈ W·μ`, and by facet exclusion (`weylDot_add_eq_weylDot`)
`w·λ + ν' = w·μ`; the weight `ν' = w (μ - λ)` is extremal, of multiplicity one. So exactly one
step survives and the block is `M(w·μ)`.

## References

* Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*, GSM 94,
  Theorem 7.6 (check). Humphreys treats arbitrary `λ` with the integral Weyl group `W_[λ]`;
  here all weights are integral, so `W_[λ] = W`. The argument is the standard one,
  reconstructed; the tensor factor is written on the right.
-/

noncomputable section

open Module LieModule TensorProduct

namespace LieSubmodule

variable {K L V : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

/-- The image of `M` in `V ⧸ N` vanishes iff `M ≤ N`. -/
theorem map_mk'_eq_bot_iff (N M : LieSubmodule K L V) :
    M.map (Quotient.mk' N) = ⊥ ↔ M ≤ N := by
  constructor
  · intro h m hm
    have : Quotient.mk' N m ∈ M.map (Quotient.mk' N) := (mem_map _).mpr ⟨m, hm, rfl⟩
    rw [h, mem_bot] at this
    exact (Quotient.mk_eq_zero N).mp this
  · intro h
    rw [eq_bot_iff]
    rintro _ hx
    obtain ⟨m, hm, rfl⟩ := (mem_map _).mp hx
    exact (Quotient.mk_eq_zero N).mpr (h hm)

/-- A monotone filtration `F 0 = ⊥ ≤ ⋯ ≤ F n` whose successive quotient images vanish except
at the step `j₀` has `F j₀ = ⊥` and `F (j₀ + 1) = F n`. -/
theorem eq_bot_and_eq_last_of_single_step {n : ℕ} (F : Fin (n + 1) → LieSubmodule K L V)
    (hF : Monotone F) (h0 : F 0 = ⊥) (j₀ : Fin n)
    (hstep : ∀ j, j ≠ j₀ → (F j.succ).map (Quotient.mk' (F j.castSucc)) = ⊥) :
    F j₀.castSucc = ⊥ ∧ F j₀.succ = F (Fin.last n) := by
  have hle (j : Fin n) (hj : j ≠ j₀) : F j.succ = F j.castSucc :=
    le_antisymm ((map_mk'_eq_bot_iff _ _).mp (hstep j hj))
      (hF (Fin.castSucc_le_succ j))
  constructor
  · have key : ∀ m (hm : m ≤ j₀.val), F ⟨m, by omega⟩ = ⊥ := by
      intro m
      induction m with
      | zero => intro _; exact h0
      | succ m ih =>
        intro hm
        have hj : (⟨m, by omega⟩ : Fin n) ≠ j₀ := by
          intro h; rw [← h] at hm; simp at hm
        have := hle ⟨m, by omega⟩ hj
        simp only [Fin.succ_mk, Fin.castSucc_mk] at this
        rw [this]
        exact ih (by omega)
    exact key j₀.val le_rfl
  · have key : ∀ d (k : Fin (n + 1)), k.val + d = n → j₀.val + 1 ≤ k.val →
        F k = F (Fin.last n) := by
      intro d
      induction d with
      | zero =>
        intro k hk _
        congr 1
        ext
        simp [← hk]
      | succ d ih =>
        intro k hk hk₀
        have hj : (⟨k.val, by omega⟩ : Fin n) ≠ j₀ := by
          intro h; rw [← h] at hk₀; simp at hk₀
        have := hle ⟨k.val, by omega⟩ hj
        simp only [Fin.succ_mk, Fin.castSucc_mk] at this
        rw [← ih ⟨k.val + 1, by omega⟩ (by simp only; omega)
          (by simp only; omega), this]
    exact key (n - (j₀.val + 1)) j₀.succ (by simp only [Fin.val_succ]; omega)
      (by simp only [Fin.val_succ]; omega)

/-- The image of `M` in `V ⧸ ⊥` is isomorphic to `M`. -/
def mapMkBotEquiv (M : LieSubmodule K L V) :
    M ≃ₗ⁅K,L⁆ M.map (Quotient.mk' (⊥ : LieSubmodule K L V)) :=
  LieModuleEquiv.ofBijective
    (((Quotient.mk' ⊥).comp M.incl).codRestrict _ (fun m => (mem_map _).mpr ⟨m.val, m.property,
      rfl⟩)) ⟨fun x y hxy => by
      have h := congrArg Subtype.val hxy
      simp only [LieModuleHom.codRestrict_apply, LieModuleHom.coe_comp, Function.comp_apply,
        incl_apply] at h
      rw [← sub_eq_zero, ← map_sub, Quotient.mk_eq_zero, mem_bot, sub_eq_zero] at h
      exact Subtype.ext h, by
      rintro ⟨y, hy⟩
      obtain ⟨m, hm, rfl⟩ := (mem_map _).mp hy
      exact ⟨⟨m, hm⟩, rfl⟩⟩

end LieSubmodule

namespace Matrix.Realization.KacMoodyAlgebra

open VermaModule

variable {ι H : Type*} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (hA : A.IsFiniteCartan)

local notation "𝔤" => KacMoodyAlgebra P

include hA in
/-- **Translation of Verma modules** (integral weights, finite type; Humphreys, GSM 94,
Theorem 7.6 (check)). Let `λ + ρ`, `μ + ρ` be antidominant integral with every simple wall of
`λ + ρ` a wall of `μ + ρ`, and `ν = z (μ - λ)` dominant. Then for every `w ∈ W` the
`χ_μ`-block of `M(w·λ) ⊗ L(ν)` is isomorphic to `M(w·μ)`. -/
theorem translation_verma {lam μ ν : Dual K H}
    (hlam : ∀ i, ∃ n : ℕ, (lam + P.rho) (P.coroot i) = -n)
    (hμ : ∀ i, ∃ n : ℕ, (μ + P.rho) (P.coroot i) = -n)
    (hfacet : ∀ i, (lam + P.rho) (P.coroot i) = 0 → (μ + P.rho) (P.coroot i) = 0)
    (hν : P.IsDominantIntegral ν) {z : Dual K H ≃ₗ[K] Dual K H}
    (hz : z ∈ P.weylGroup hA.isGeneralizedCartan) (hzν : z (μ - lam) = ν)
    (w : P.weylGroup hA.isGeneralizedCartan) :
    Nonempty (VermaModule P (P.weylDot hA.isGeneralizedCartan w μ) ≃ₗ⁅K,𝔤⁆
      centralBlock P (VermaModule P (P.weylDot hA.isGeneralizedCartan w lam) ⊗[K]
        IrreducibleModule P ν) (centralCharacter P μ)) := by
  classical
  have hA' := hA.isGeneralizedCartan
  set Λ := P.weylDot hA' w lam with hΛdef
  set ν₀ := P.weylDot hA' w μ - Λ with hν₀def
  have : FiniteDimensional K (IrreducibleModule P ν) :=
    IrreducibleModule.finiteDimensional (P := P) hA hν
  have hZ : IsHDiagonalizable P (IrreducibleModule P ν) :=
    (IrreducibleModule.isCategoryO P ν).iSup_weightSpaceOfMap_eq_top
  obtain ⟨N, wt, -, -, -, -, hcount, hFmono, hF0, hFlast, -, hFstep, hret⟩ :=
    exists_centralTensorVermaFiltration P hZ Λ (centralCharacter P μ)
  set C := centralBlock P (VermaModule P Λ ⊗[K] IrreducibleModule P ν) (centralCharacter P μ)
  set F := fun k => N k ⊓ C with hFdef
  have hwμ : Λ + ν₀ = P.weylDot hA' w μ := by rw [hν₀def]; abel
  -- The weight `ν₀ = w (μ - λ)` is extremal, of multiplicity one, with character `χ_μ`.
  have hχ₀ : centralCharacter P (Λ + ν₀) = centralCharacter P μ := by
    rw [hwμ]
    exact centralCharacter_weyl P hA' w.property μ
  have hν₀ : ν₀ = (w.val * z⁻¹) ν := by
    rw [LinearEquiv.mul_apply]
    change _ = w.val (z.symm ν)
    rw [← hzν, LinearEquiv.symm_apply_apply, hν₀def, hΛdef]
    simp only [weylDot, map_sub, map_add]
    abel
  have hmult : finrank K (weightSpace P (IrreducibleModule P ν) ν₀) = 1 := by
    have hV := (IrreducibleModule.isIntegrable_iff P hA').mpr hν
    have hr := rank_weightSpace_weylGroup hA' hV (mul_mem w.property (inv_mem hz)) ν
    rw [hν₀]
    unfold Module.finrank
    rw [hr]
    exact IrreducibleModule.finrank_weightSpace_self P ν
  have hone := hret ν₀
  rw [ite_eq_left hχ₀, hmult] at hone
  obtain ⟨hsub, ⟨j₀, hj₀wt, hj₀χ⟩⟩ := Nat.card_eq_one_iff_unique.mp hone
  -- Every retained step has weight `ν₀` (linkage and facet exclusion).
  have hretained (j) (hj : centralCharacter P (Λ + wt j) = centralCharacter P μ) :
      wt j = ν₀ := by
    have hwtj : weightSpace P (IrreducibleModule P ν) (wt j) ≠ ⊥ := by
      intro hbot
      have hc := hcount (wt j)
      rw [hbot, finrank_bot] at hc
      have : Nonempty {j' // wt j' = wt j} := ⟨⟨j, rfl⟩⟩
      exact (Nat.card_pos (α := {j' // wt j' = wt j})).ne' hc
    obtain ⟨x, hx, hxe⟩ := (VermaModule.centralCharacter_eq_iff P hA μ (Λ + wt j)).mp hj.symm
    have h : P.weylDot hA' w lam + wt j = P.weylDot hA' ⟨x, hx⟩ μ := by
      simp only [weylDot]
      rw [hxe, hΛdef]
      simp only [weylDot]
      abel
    have := IrreducibleModule.weylDot_add_eq_weylDot hA hlam hμ hfacet hν hz hzν hwtj h
    rw [hν₀def, ← this, hΛdef]
    abel
  have hstep_ne (j) (hj : j ≠ j₀) :
      (F j.succ).map (LieSubmodule.Quotient.mk' (F j.castSucc)) = ⊥ := by
    apply (hFstep j).2
    intro hχ
    apply hj
    have := hsub.elim ⟨j, hretained j hχ, hχ⟩ ⟨j₀, hj₀wt, hj₀χ⟩
    exact congrArg Subtype.val this
  obtain ⟨h1, h2⟩ := LieSubmodule.eq_bot_and_eq_last_of_single_step F hFmono hF0 j₀ hstep_ne
  obtain ⟨e⟩ := (hFstep j₀).1 hj₀χ
  have h2' : F j₀.succ = C := h2.trans hFlast
  rw [hj₀wt, hwμ] at e
  change VermaModule P _ ≃ₗ⁅K,𝔤⁆ (F j₀.succ).map (LieSubmodule.Quotient.mk' (F j₀.castSucc))
    at e
  rw [h1, h2'] at e
  exact ⟨e.trans (LieSubmodule.mapMkBotEquiv C).symm⟩

end Matrix.Realization.KacMoodyAlgebra
