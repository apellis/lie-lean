/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Frobenius.CartanDatum
import LieLean.Algebra.QuantumGroup.Weight
import LieLean.Algebra.QuantumGroup.YRegular

/-!
# The root datum `(Y*, X*)` of [Lus] 2.2.5

Let `R` be a root datum of type `(I, ·)` and `l ≥ 1`, and let `(I, ∘)` be the Cartan datum of
[Lus] 2.2.4 (`LusztigCartanDatum.frobenius`), `i ∘ j = lᵢ lⱼ (i · j)`. Lusztig defines a root datum
`(Y*, X*)` of type `(I, ∘)`: `X* = {ζ ∈ X | lᵢ ∣ ⟨i, ζ⟩ for all i}`, `Y* = Hom(X*, ℤ)`, the simple
roots `j* = lⱼ j' ∈ X*` and the simple coroots `i* : ζ ↦ ⟨i, ζ⟩/lᵢ`.

The library records a root datum through `Y` alone, with `X = Y →+ ℤ`, and does not ask `Y` to be
free of finite rank. The construction makes sense in that generality: `X*` is the subgroup
`frobWeights` of `Y →+ ℤ`, and the root datum `frobRootDatum` lives on `frobWeights →+ ℤ`. Its
simple roots are the evaluations at the `lⱼ j'`. When `Y` is free of finite rank, the double dual
of `X*` is `X*`, which recovers Lusztig's statement.

## Main definitions

* `LusztigCartanDatum.RootDatum.frobWeights`: `X*`.
* `LusztigCartanDatum.RootDatum.frobRootDatum`: the root datum `(Y*, X*)` of type `(I, ∘)`.
* `LusztigCartanDatum.RootDatum.frobDualHom`: the map `f : Y → Y*` dual to `X* ⊆ X`.

## Main results

* `frobRootDatum_root_coroot`: `⟨i*, j*⟩ = 2 (i ∘ j)/(i ∘ i)`.
* `frobDualHom_coroot`, `frobRootDatum_root_frobDualHom`: `f(i) = lᵢ i*` and
  `⟨f(μ), j*⟩ = lⱼ ⟨μ, j'⟩`.
* `IsXRegular.frobRootDatum`, `IsYRegular.frobRootDatum`: `X`-regularity (resp. `Y`-regularity, for
  `Y` free) passes from `(Y, X)` to `(Y*, X*)`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 2.2.4, 2.2.5.
-/

open LieLean

noncomputable section

namespace LusztigCartanDatum.RootDatum

variable {I Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I} (R : D.RootDatum Y) (l : ℕ)

/-- `X* = {ζ ∈ X | lᵢ ∣ ⟨i, ζ⟩ for all i}` ([Lus] 2.2.5). -/
def frobWeights : AddSubgroup (Y →+ ℤ) where
  carrier := {ζ | ∀ i, (D.frobOrder l i : ℤ) ∣ ζ (R.coroot i)}
  add_mem' ha hb i := by simpa using dvd_add (ha i) (hb i)
  zero_mem' i := by simp
  neg_mem' ha i := by simpa using (ha i).neg_right

variable {R l} in
lemma mem_frobWeights {ζ : Y →+ ℤ} :
    ζ ∈ R.frobWeights l ↔ ∀ i, (D.frobOrder l i : ℤ) ∣ ζ (R.coroot i) := Iff.rfl

/-- The simple coroot `i* ∈ Y*`, `ζ ↦ ⟨i, ζ⟩/lᵢ`. -/
def frobCoroot (i : I) : R.frobWeights l →+ ℤ where
  toFun ζ := ζ.1 (R.coroot i) / D.frobOrder l i
  map_zero' := by simp
  map_add' ζ η := by
    simp only [AddSubgroup.coe_add, AddMonoidHom.add_apply]
    exact Int.add_ediv_of_dvd_left (ζ.2 i)

lemma frobCoroot_apply (i : I) (ζ : R.frobWeights l) :
    R.frobCoroot l i ζ = ζ.1 (R.coroot i) / D.frobOrder l i := rfl

lemma frobOrder_mul_frobCoroot (i : I) (ζ : R.frobWeights l) :
    (D.frobOrder l i : ℤ) * R.frobCoroot l i ζ = ζ.1 (R.coroot i) :=
  Int.mul_ediv_cancel' (ζ.2 i)

variable {l}

/-- The simple root `j* = lⱼ j' ∈ X*`. -/
def frobRoot (hl : 0 < l) (j : I) : R.frobWeights l :=
  ⟨(D.frobOrder l j : ℤ) • R.root j, fun i ↦ by
    simpa [R.root_coroot] using D.frobOrder_dvd_mul_cartanMatrix hl i j⟩

@[simp] lemma coe_frobRoot (hl : 0 < l) (j : I) :
    (R.frobRoot hl j : Y →+ ℤ) = (D.frobOrder l j : ℤ) • R.root j := rfl

/-- The root datum `(Y*, X*)` of type `(I, ∘)` ([Lus] 2.2.5), on `Y* = Hom(X*, ℤ)`: simple coroots
`i*` (`frobCoroot`) and simple roots the evaluations at `j* = lⱼ j'` (`frobRoot`). -/
def frobRootDatum (hl : 0 < l) : (D.frobenius hl).RootDatum (R.frobWeights l →+ ℤ) where
  coroot := R.frobCoroot l
  root j :=
    { toFun := fun y ↦ y (R.frobRoot hl j)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  root_coroot i j := by
    change (R.frobRoot hl j : Y →+ ℤ) (R.coroot i) / D.frobOrder l i = _
    have h0 : (D.frobOrder l i : ℤ) ≠ 0 := by exact_mod_cast (D.frobOrder_pos hl i).ne'
    rw [coe_frobRoot, AddMonoidHom.smul_apply, R.root_coroot, smul_eq_mul,
      ← D.frobOrder_mul_cartanMatrix_frobenius hl, Int.mul_ediv_cancel_left _ h0]

@[simp] lemma frobRootDatum_coroot (hl : 0 < l) (i : I) :
    (R.frobRootDatum hl).coroot i = R.frobCoroot l i := rfl

@[simp] lemma frobRootDatum_root (hl : 0 < l) (j : I) (y : R.frobWeights l →+ ℤ) :
    (R.frobRootDatum hl).root j y = y (R.frobRoot hl j) := rfl

/-- `⟨i*, j*⟩ = 2 (i ∘ j)/(i ∘ i)`, the Cartan matrix of `(I, ∘)` ([Lus] 2.2.5). -/
lemma frobRootDatum_root_coroot (hl : 0 < l) (i j : I) :
    (R.frobRootDatum hl).root j (R.frobCoroot l i) = (D.frobenius hl).cartanMatrix i j :=
  (R.frobRootDatum hl).root_coroot i j

variable (l) in
/-- The map `f : Y → Y*` dual to the inclusion `X* ⊆ X` ([Lus] 2.2.5). -/
def frobDualHom : Y →+ (R.frobWeights l →+ ℤ) where
  toFun μ :=
    { toFun := fun ζ ↦ ζ.1 μ
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

@[simp] lemma frobDualHom_apply (μ : Y) (ζ : R.frobWeights l) : R.frobDualHom l μ ζ = ζ.1 μ := rfl

/-- `f(i) = lᵢ i*`. -/
lemma frobDualHom_coroot (i : I) :
    R.frobDualHom l (R.coroot i) = (D.frobOrder l i : ℤ) • R.frobCoroot l i := by
  ext ζ
  simp [frobOrder_mul_frobCoroot]

/-- `⟨f(μ), j*⟩ = lⱼ ⟨μ, j'⟩`. -/
lemma frobRootDatum_root_frobDualHom (hl : 0 < l) (j : I) (μ : Y) :
    (R.frobRootDatum hl).root j (R.frobDualHom l μ) = D.frobOrder l j * R.root j μ := rfl

/-- If `(Y, X)` is `X`-regular, so is `(Y*, X*)` ([Lus] 2.2.5). -/
theorem IsXRegular.frobRootDatum {R : D.RootDatum Y} (hR : R.IsXRegular) (hl : 0 < l) :
    (R.frobRootDatum hl).IsXRegular := by
  rw [IsXRegular, linearIndependent_iff'] at hR ⊢
  intro s g hg i hi
  have h := hR s (fun j ↦ g j * D.frobOrder l j) ?_ i hi
  · exact (mul_eq_zero.1 h).resolve_right (by exact_mod_cast (D.frobOrder_pos hl i).ne')
  · ext μ
    have := DFunLike.congr_fun hg (R.frobDualHom l μ)
    simpa [frobRootDatum_root_frobDualHom, mul_assoc] using this

/-- If `(Y, X)` is `Y`-regular and `Y` is free, then `(Y*, X*)` is `Y`-regular ([Lus] 2.2.5). -/
theorem IsYRegular.frobRootDatum [Module.Free ℤ Y] {R : D.RootDatum Y} (hR : R.IsYRegular)
    (hl : 0 < l) : (R.frobRootDatum hl).IsYRegular := by
  rw [IsYRegular, linearIndependent_iff'] at hR ⊢
  intro s g hg i hi
  have hdvd : ∀ j, (D.frobOrder l j : ℤ) ∣ l := fun j ↦ by exact_mod_cast D.frobOrder_dvd (l := l) j
  have h := hR s (fun j ↦ g j * ((l : ℤ) / D.frobOrder l j)) ?_ i hi
  · refine (mul_eq_zero.1 h).resolve_right ?_
    intro h0
    have := Int.mul_ediv_cancel' (hdvd i)
    rw [h0, mul_zero] at this
    exact hl.ne' (by exact_mod_cast this.symm)
  · -- every `η ∈ X` vanishes on the left side, by evaluating `hg` at `l η ∈ X*`
    refine (Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun η ↦ ?_
    have hη : (l : ℤ) • η.toAddMonoidHom ∈ R.frobWeights l := fun j ↦ by
      simpa using (hdvd j).mul_right (η (R.coroot j))
    have := DFunLike.congr_fun hg ⟨_, hη⟩
    simp only [frobRootDatum_coroot, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
      frobCoroot_apply, AddMonoidHom.zero_apply, smul_eq_mul] at this
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) this
    obtain ⟨c, hc⟩ := hdvd j
    have h0 : (D.frobOrder l j : ℤ) ≠ 0 := by exact_mod_cast (D.frobOrder_pos hl j).ne'
    simp only [map_zsmul, smul_eq_mul, LinearMap.toAddMonoidHom_coe]
    rw [hc, Int.mul_ediv_cancel_left _ h0, mul_assoc (D.frobOrder l j : ℤ),
      Int.mul_ediv_cancel_left _ h0, mul_assoc]

end LusztigCartanDatum.RootDatum
