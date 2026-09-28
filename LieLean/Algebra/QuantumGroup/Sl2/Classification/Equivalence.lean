/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Sl2.Classification.StringBasis

/-!
# Exhaustion of finite-dimensional irreducible quantum sl₂ representations

## Main results

* `QuantumGroup.Sl2.exists_equiv_simpleRep`: every nonzero finite-dimensional irreducible
  representation is equivalent to `simpleRep`, retaining both signs of the highest weight.
* `QuantumGroup.Sl2.irreducible_iff_equiv_simpleRep`: the finite-dimensional exhaustion
  equivalence, combining this existence result with `simpleRep_irreducible`.

## References

Jantzen, *Lectures on quantum groups*, Ch. 2. The intertwining argument is reconstructed;
precise theorem numbering has not been checked against the source.
-/

noncomputable section

namespace QuantumGroup.Sl2

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] {v : k}

/-- Every nonzero finite-dimensional irreducible representation over an algebraically closed
field is equivalent to one of the existing `simpleRep` representations. Both signs `σ² = 1`
are retained, with no characteristic or type-1 restriction. The highest-string intertwining
argument is reconstructed from Jantzen, Ch. 2. -/
theorem exists_equiv_simpleRep [IsAlgClosed k] [FiniteDimensional k M] [Nontrivial M]
    (hv : v ≠ 0) (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1)
    (ρ : Sl2 v →ₐ[k] Module.End k M)
    (hρ : ∀ W : Submodule k M, (∀ (u : Sl2 v) x, x ∈ W → ρ u x ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ (n : ℕ) (σ : k) (hσ : σ ^ 2 = 1) (e : (Fin (n + 1) → k) ≃ₗ[k] M),
      ∀ (u : Sl2 v) x, e (simpleRep v n σ hv (hv' 2 two_pos) hσ u x) = ρ u (e x) := by
  classical
  obtain ⟨n, σ, m, hσ, _, hm, hE, _, hz, b, hb⟩ :=
    exists_highestString_basis hv hv' ρ hρ
  let S := simpleRep v n σ hv (hv' 2 two_pos) hσ
  let m₀ : Fin (n + 1) → k := Pi.single 0 1
  let e : (Fin (n + 1) → k) ≃ₗ[k] M := b.equivFun.symm
  have ha : σ * v ^ n ≠ 0 := by
    apply mul_ne_zero _ (pow_ne_zero _ hv)
    intro h
    simp [h] at hσ
  have hsK : S (K sl2RootDatum v 1) m₀ = (σ * v ^ n) • m₀ := by
    simpa [S, m₀] using
      simpleRep_K_single (n := n) hv (hv' 2 two_pos) hσ 1 0
  have hsE : S (E sl2RootDatum v ()) m₀ = 0 := by
    simp only [S, m₀, simpleRep_E_single, Fin.val_zero, lt_self_iff_false,
      ↓reduceDIte]
  have hsF (i : Fin (n + 1)) :
      (S (F sl2RootDatum v ()) ^ (i : ℕ)) m₀ = Pi.single i 1 := by
    simp only [S, simpleRep_F, m₀]
    apply ext_coord
    intro l
    have := i.2
    rw [coord_opF_pow, coord_single, coord_single, Fin.val_zero]
    split_ifs <;> first | rfl | (exfalso; omega)
  have he (i : Fin (n + 1)) :
      e (Pi.single i 1) = (ρ (F sl2RootDatum v ()) ^ (i : ℕ)) m := by
    simpa [e, Module.Basis.equivFun_symm_apply, Pi.single_apply] using hb i
  have heF (r : ℕ) (hr : r ≤ n) :
      e ((S (F sl2RootDatum v ()) ^ r) m₀) =
        (ρ (F sl2RootDatum v ()) ^ r) m := by
    rw [hsF ⟨r, by omega⟩]
    exact he ⟨r, by omega⟩
  have he0 : e m₀ = m := by simpa using heF 0 (Nat.zero_le n)
  have extend (u : Sl2 v)
      (h : ∀ i : Fin (n + 1),
        e (S u (Pi.single i 1)) = ρ u (e (Pi.single i 1))) :
      ∀ x, e (S u x) = ρ u (e x) := by
    have hh : e.toLinearMap.comp (S u) = (ρ u).comp e.toLinearMap := by
      apply (Pi.basisFun k (Fin (n + 1))).ext
      intro i
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply] using h i
    exact fun x => LinearMap.congr_fun hh x
  refine ⟨n, σ, hσ, e, ?_⟩
  intro u
  change ∀ x, e (S u x) = ρ u (e x)
  induction u using QuantumGroup.induction_on with
  | algebraMap c => intro x; simp
  | E i =>
    obtain rfl := Subsingleton.elim i ()
    apply extend
    intro i
    rw [← hsF i]
    rcases Nat.eq_zero_or_pos i.val with hi | hi
    · simp [hi, hsE, he0, hE]
    · obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
      rw [hr, E_apply_F_pow_succ hv S ha hsK hsE, map_smul,
        heF r (by omega), heF (r + 1) (by omega), E_apply_F_pow_succ hv ρ ha hm hE]
  | F i =>
    obtain rfl := Subsingleton.elim i ()
    apply extend
    intro i
    rw [he, ← Module.End.mul_apply, ← pow_succ']
    by_cases hi : i.val + 1 < n + 1
    · rw [show S (F sl2RootDatum v ()) (Pi.single i 1) =
        Pi.single ⟨i.val + 1, hi⟩ 1 by
          simp only [S, simpleRep_F_single, hi, ↓reduceDIte]]
      exact he ⟨i.val + 1, hi⟩
    · have hin : i.val = n := by omega
      rw [show S (F sl2RootDatum v ()) (Pi.single i 1) = 0 by
        simp only [S, simpleRep_F_single, hi, ↓reduceDIte]]
      rw [map_zero, hin, hz]
  | K μ =>
    apply extend
    intro i
    rw [← hsF i,
      K_apply_of_K_apply S
        (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero hv))) ha)
        (K_apply_F_pow S hsK i) μ,
      map_smul, heF i (by omega),
      K_apply_of_K_apply ρ
        (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero hv))) ha)
        (K_apply_F_pow ρ hm i) μ]
  | add u u' hu hu' => intro x; simp [hu, hu']
  | mul u u' hu hu' => intro x; simp only [map_mul, Module.End.mul_apply, hu, hu']

/-- Equivalence to a member of `simpleRep` implies irreducibility. This direction
uses the existing `simpleRep_irreducible` theorem and transport of invariant subspaces;
the transport argument is reconstructed here. -/
theorem irreducible_of_equiv_simpleRep (hv : v ≠ 0)
    (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1) (ρ : Sl2 v →ₐ[k] Module.End k M)
    {n : ℕ} {σ : k} (hσ : σ ^ 2 = 1) (e : (Fin (n + 1) → k) ≃ₗ[k] M)
    (he : ∀ (u : Sl2 v) x,
      e (simpleRep v n σ hv (hv' 2 two_pos) hσ u x) = ρ u (e x))
    (W : Submodule k M) (hW : ∀ (u : Sl2 v) x, x ∈ W → ρ u x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hstable : ∀ (u : Sl2 v) x, x ∈ W.comap e.toLinearMap →
      simpleRep v n σ hv (hv' 2 two_pos) hσ u x ∈ W.comap e.toLinearMap := by
    intro u x hx
    change e (simpleRep v n σ hv (hv' 2 two_pos) hσ u x) ∈ W
    rw [he]
    exact hW u _ hx
  rcases simpleRep_irreducible hv hv' hσ _ hstable with hbot | htop
  · left
    apply bot_unique
    intro x hx
    change x = 0
    have hmem : e.symm x ∈ W.comap e.toLinearMap := by simpa using hx
    rw [hbot] at hmem
    have hz : e.symm x = 0 := hmem
    simpa using congrArg e hz
  · right
    apply top_unique
    intro x _
    have hmem : e.symm x ∈ W.comap e.toLinearMap := by rw [htop]; trivial
    simpa using hmem

/-- Classification of nonzero finite-dimensional irreducible quantum sl₂ representations:
irreducibility is equivalent to being linearly intertwined with some `simpleRep L(n,σ)`,
where `σ² = 1`. No type-1 or highest-vector hypothesis is imposed. This is the finite-
dimensional exhaustion statement from Jantzen, Ch. 2, reconstructed here. -/
theorem irreducible_iff_equiv_simpleRep [IsAlgClosed k] [FiniteDimensional k M]
    [Nontrivial M] (hv : v ≠ 0) (hv' : ∀ r : ℕ, 0 < r → v ^ r ≠ 1)
    (ρ : Sl2 v →ₐ[k] Module.End k M) :
    (∀ W : Submodule k M, (∀ (u : Sl2 v) x, x ∈ W → ρ u x ∈ W) →
      W = ⊥ ∨ W = ⊤) ↔
    ∃ (n : ℕ) (σ : k) (hσ : σ ^ 2 = 1) (e : (Fin (n + 1) → k) ≃ₗ[k] M),
      ∀ (u : Sl2 v) x, e (simpleRep v n σ hv (hv' 2 two_pos) hσ u x) = ρ u (e x) := by
  constructor
  · exact exists_equiv_simpleRep hv hv' ρ
  · rintro ⟨n, σ, hσ, e, he⟩
    exact irreducible_of_equiv_simpleRep hv hv' ρ hσ e he

end QuantumGroup.Sl2
