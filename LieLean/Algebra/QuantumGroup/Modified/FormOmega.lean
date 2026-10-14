/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.FormPlus

/-!
# The form on `U̇` is invariant under `ω`

The Chevalley involution `ω` of `U` (`Eᵢ ↔ Fᵢ`, `K_μ ↦ K_{-μ}`) induces the algebra automorphism
`ω : U̇ → U̇`, `π_{λ',λ''}(u) ↦ π_{-λ',-λ''}(ω u)` ([Lus] 23.1.6), as `Modified.map` of
`Modified.chevalleyAut`.

## Main results

* `QuantumGroup.chevalley_rho`: `ω ρ = ρ ω` on `U`.
* `QuantumGroup.Modified.map_leftAct`: `φ(u x) = φ(u) φ(x)` for the automorphism of `U̇` induced
  by `φ`.
* `QuantumGroup.Modified.form_map_chevalleyAut`: [Lus] 26.1.6, `(ω(x), ω(y)) = (x, y)`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.6, 26.1.6.
-/

open LieLean LusztigF

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v]

/-- `ω ρ = ρ ω` on `U` ([Lus] 26.1.6). -/
theorem chevalley_rho (u : QuantumGroup R v) :
    chevalley R v (rho R v u) = rho R v (chevalley R v u) := by
  induction u using QuantumGroup.induction_on with
  | algebraMap c => simp
  | E i => rw [rho_E, rhoE, map_smul, map_mul, chevalley_E, chevalley_F, rho_F, rhoF, Kt,
      chevalley_K]
  | F i => rw [rho_F, rhoF, map_smul, map_mul, chevalley_F, chevalley_K, neg_neg, chevalley_E,
      rho_E, rhoE, Kt]
  | K μ => rw [rho_K, chevalley_K, rho_K]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | mul x y hx hy => rw [rho_mul, map_mul, hx, hy, map_mul, rho_mul]

namespace Modified

variable (R v) in
/-- The Chevalley involution `ω` (`Eᵢ ↔ Fᵢ`, `K_μ ↦ K_{-μ}`) as an element of `torusAut`. -/
def chevalleyAut : torusAut R v :=
  ⟨(chevalleyEquiv R v, LinearEquiv.neg ℤ), fun μ ↦ chevalley_K R v μ⟩

omit [NeZero v] in
@[simp] lemma chevalleyAut_apply (u : QuantumGroup R v) :
    (chevalleyAut R v).1.1 u = chevalley R v u :=
  rfl

omit [NeZero v] in
lemma wt_chevalleyAut (l : Y →+ ℤ) : wt (chevalleyAut R v) l = -l := by
  ext μ
  have h : (chevalleyAut R v).1.2⁻¹ μ = -μ := by
    have := autY_apply_inv (chevalleyAut R v).1.2 μ
    change -((chevalleyAut R v).1.2⁻¹ μ) = μ at this
    exact neg_eq_iff_eq_neg.mp this
  rw [wt_apply, h, map_neg, AddMonoidHom.neg_apply]

omit [NeZero v] in
lemma map_chevalleyAut_one (l : Y →+ ℤ) : map (chevalleyAut R v) (one l) = one (-l) := by
  rw [one, map_elt, one]
  exact elt_index (wt_chevalleyAut l) (wt_chevalleyAut l) (_root_.map_one _) _ _

omit [NeZero v] in
lemma wt_add (g : torusAut R v) (l l' : Y →+ ℤ) : wt g (l + l') = wt g l + wt g l' := by
  ext μ; simp

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv

/-- `φ(u x) = φ(u) φ(x)` for the map of `U̇` induced by `(φ, σ) ∈ torusAut`. -/
theorem map_leftAct (g : torusAut R v) (u : QuantumGroup R v) (x : Modified R v) :
    map g (leftAct R v hv u x) = leftAct R v hv (g.1.1 u) (map g x) := by
  induction u using induction_adWeightSpace with
  | h0 => simp
  | hadd u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | hhom χ u hu =>
  induction x using induction_on with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, hx, hx']
  | helt l₁ l₂ t ht =>
    rw [leftAct_elt hv hu, map_elt, map_elt, leftAct_elt hv (map_mem_adWeightSpace g hu)]
    exact elt_index (wt_add g l₁ χ) rfl (_root_.map_mul _ _ _) _ _

/-- **[Lus] 26.1.6**: `(ω(x), ω(y)) = (x, y)` for `x, y ∈ U̇`. -/
theorem form_map_chevalleyAut (x y : Modified R v) :
    form R v hv (map (chevalleyAut R v) x) (map (chevalleyAut R v) y) = form R v hv x y := by
  set g := chevalleyAut R v
  have h := eq_form hv (B := (form R v hv).compl₁₂ (map g) (map g))
    (fun _ _ _ _ hne ↦ one_mul_mul_one_eq_zero_of_elt (fun l₁ l₂ m₁ m₂ a b ha hb hne ↦ by
      rw [LinearMap.compl₁₂_apply, map_elt, map_elt]
      refine form_elt_elt_of_ne hv (fun h ↦ hne ?_) _ _
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨wt_injective g h.1, wt_injective g h.2⟩) hne)
    (fun u x y ↦ by
      rw [LinearMap.compl₁₂_apply, LinearMap.compl₁₂_apply, map_leftAct, form_leftAct_left,
        map_leftAct, chevalleyAut_apply, chevalleyAut_apply, chevalley_rho])
    (fun l x y ↦ by
      rw [LinearMap.compl₁₂_apply, map_leftAct, map_leftAct, map_chevalleyAut_one,
        chevalleyAut_apply, chevalleyAut_apply, chevalley_minusHom, chevalley_minusHom,
        form_plusHom_leftAct_one])
  exact LinearMap.congr_fun₂ h x y

end Modified

end LieLean.QuantumGroup
