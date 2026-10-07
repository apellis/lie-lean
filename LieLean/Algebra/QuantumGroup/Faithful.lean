/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Integrable
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerreNegative

/-!
# Integrable modules detect `U⁺` and `U⁻`

Let `U = U_q(𝔤)` (`QuantumGroup R v`) with `v` not a root of unity, and suppose that the simple
coroots can be paired with weights as large as we like: for every `N` there is `Λ ∈ Hom(Y, ℤ)`
with `⟨i, Λ⟩ ≥ N` for all `i`. We show that an element of `U⁻ = ('f)⁻` acting as zero on all the
integrable modules `L̃_q(Λ) = M_q(Λ) ⧸ Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ` (`QuantumGroup.FPowQuotient`) is zero
(`QuantumGroup.minusHom_eq_zero_of_forall_smul_eq_zero`), and likewise for `U⁺` with the modules
`ʷL̃_q(Λ)` twisted by the Chevalley involution (`QuantumGroup.ChevalleyTwist`,
`QuantumGroup.plusHom_eq_zero_of_forall_smul_eq_zero`); cf. [Jan] 5.11, whose argument with
tensor products shows the analogous statement for all of `U` in finite type.

The point is that `y ↦ y⁻ v_Λ` is injective on the weights `ν ∈ ℕ[I]` with `νᵢ ≤ ⟨i, Λ⟩` for all
`i`: the submodule `Σᵢ U Fᵢ^{⟨i,Λ⟩+1} v_Λ` equals `Σᵢ ('f θᵢ^{⟨i,Λ⟩+1})⁻ v_Λ`
(`QuantumGroup.VermaModule.fPowSubmodule_le_map_toVerma`), and the Serre ideal `J` of `'f` is
graded (`LusztigF.weightProj_mem_serreIdeal`), so `M_q(Λ) ≅ 'f ⧸ J` (`toVerma_eq_zero_iff`) gives
the claim. We do not need the root datum to be `X`-regular.

## Main definitions

* `QuantumGroup.ChevalleyTwist R v M`: a `U`-module `M` with `U` acting through the Chevalley
  involution `ω` (`Eᵢ ↦ Fᵢ`, `Fᵢ ↦ Eᵢ`, `K_μ ↦ K_{-μ}`); integrable if `M` is.

## References

* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, 5.11.
-/

open LieLean Finset

noncomputable section

namespace LusztigF

variable {k I : Type*} [Field k]

lemma weightProj_apply (ν : I →₀ ℕ) (y : LusztigF k I) :
    weightProj ν y = (gradingHom k I y).coeff ν := rfl

/-- Every element of `'f` is the sum of its weight components. -/
lemma sum_weightProj (y : LusztigF k I) : (gradingHom k I y).coeff.sum (fun _ a ↦ a) = y := by
  classical
  have hy : y ∈ ⨆ μ, weightSpace k (I := I) μ := by rw [iSup_weightSpace]; trivial
  induction hy using Submodule.iSup_induction' with
  | mem μ y hy => rw [gradingHom_of_mem hy, AddMonoidAlgebra.coeff_single,
      Finsupp.sum_single_index rfl]
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index' (fun _ ↦ rfl)
      (fun _ _ _ ↦ rfl), hy, hz]

variable {D : LusztigCartanDatum I} {v : k}

/-- The Serre ideal is graded: the weight components of its elements lie in it. -/
theorem weightProj_mem_serreIdeal {x : LusztigF k I} (hx : x ∈ serreIdeal D v)
    (ν : I →₀ ℕ) : weightProj ν x ∈ serreIdeal D v := by
  classical
  induction hx using TwoSidedIdeal.span_induction generalizing ν with
  | mem y hy =>
    obtain ⟨i, j, hij, rfl⟩ := hy
    have hmem : serreElement D v i j ∈ weightSpace k
        ((1 - D.cartanMatrix i j).toNat • Finsupp.single i 1 + Finsupp.single j 1) := by
      have hpow : ∀ n : ℕ, θ k i ^ n ∈ weightSpace k (n • Finsupp.single i 1) := by
        intro n
        induction n with
        | zero => simpa using one_mem_weightSpace (k := k) (I := I)
        | succ n ih =>
          rw [pow_succ, succ_nsmul]
          exact mul_mem_weightSpace ih (θ_mem_weightSpace i)
      have hdiv : ∀ n : ℕ, QuantumGroup.qDivPow (v ^ D.d i) n (θ k i) ∈
          weightSpace k (n • Finsupp.single i 1) := fun n ↦ Submodule.smul_mem _ _ (hpow n)
      rw [serreElement, QuantumGroup.qSerreDiv]
      refine Submodule.sum_mem _ fun r hr ↦ Submodule.smul_mem _ _ ?_
      simp only [mem_range] at hr
      have h1 := mul_mem_weightSpace (mul_mem_weightSpace
        (hdiv ((1 - D.cartanMatrix i j).toNat - r)) (θ_mem_weightSpace j)) (hdiv r)
      convert h1 using 2
      rw [add_right_comm, ← add_nsmul, Nat.sub_add_cancel (by omega)]
    rw [weightProj_of_mem hmem]
    split_ifs
    · exact TwoSidedIdeal.subset_span ⟨i, j, hij, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem (hy ν) (hz ν)
  | neg y _ hy => rw [map_neg]; exact neg_mem (hy ν)
  | left_absorb a y _ hy =>
    rw [weightProj_apply, map_mul, AddMonoidAlgebra.coeff_mul]
    refine sum_mem fun p _ ↦ sum_mem fun q _ ↦ ?_
    dsimp only
    split_ifs
    · exact (serreIdeal D v).mul_mem_left _ _ (hy q)
    · exact zero_mem _
  | right_absorb a y _ hy =>
    rw [weightProj_apply, map_mul, AddMonoidAlgebra.coeff_mul]
    refine sum_mem fun p _ ↦ sum_mem fun q _ ↦ ?_
    dsimp only
    split_ifs
    · exact (serreIdeal D v).mul_mem_right _ _ (hy p)
    · exact zero_mem _

/-- An element of `'f` all of whose weight components lie in the Serre ideal lies in it. -/
lemma mem_serreIdeal_of_weightProj {y : LusztigF k I}
    (h : ∀ ν, weightProj ν y ∈ serreIdeal D v) : y ∈ serreIdeal D v := by
  rw [← sum_weightProj y]
  exact sum_mem fun ν _ ↦ h ν

end LusztigF

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}

namespace VermaModule

open LusztigF

variable (R) in
/-- The span of the weight spaces `'f_ν` with `νᵢ > ⟨i, Λ⟩⁺` for some `i`. -/
def highSpan (Λ : Y →+ ℤ) : Submodule k (LusztigF k I) where
  carrier := {h | ∀ ν, weightProj ν h ≠ 0 → ∃ i, (Λ (R.coroot i)).toNat < ν i}
  add_mem' {a b} ha hb ν hν := by
    rw [map_add] at hν
    by_cases h : weightProj ν a = 0
    · rw [h, zero_add] at hν; exact hb ν hν
    · exact ha ν h
  zero_mem' ν hν := (hν (map_zero _)).elim
  smul_mem' c a ha ν hν := ha ν fun h ↦ hν (by rw [map_smul, h, smul_zero])

variable [NeZero v]

omit [DecidableEq I] in
lemma mem_highSpan_of_mem {Λ : Y →+ ℤ} {ν : I →₀ ℕ} {y : LusztigF k I}
    (hy : y ∈ LusztigF.weightSpace k ν) {i : I} (hi : (Λ (R.coroot i)).toNat < ν i) :
    y ∈ highSpan R Λ := fun μ hμ ↦ by
  classical
  rw [weightProj_of_mem hy] at hμ
  split_ifs at hμ with h
  · exact ⟨i, h ▸ hi⟩
  · exact (hμ rfl).elim

/-- `Σᵢ U Fᵢ^{⟨i,Λ⟩⁺+1} v_Λ` is contained in the image of `highSpan` under `y ↦ y⁻ v_Λ`. -/
theorem fPowSubmodule_le_map_toVerma {Λ : Y →+ ℤ} (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) :
    (fPowSubmodule R v Λ).restrictScalars k ≤ (highSpan R Λ).map (toVerma R v Λ) := by
  -- the vectors `u Fᵢ^{n+1} v_Λ`
  have key : ∀ (i : I) (u : QuantumGroup R v),
      u • (F R v i ^ ((Λ (R.coroot i)).toNat + 1) • hwv R v Λ) ∈
        (highSpan R Λ).map (toVerma R v Λ) := by
    intro i u
    set n := (Λ (R.coroot i)).toNat
    have hw := F_pow_smul_mem_weightSpace (hwv_mem_weightSpace (R := R) (v := v) (Λ := Λ)) i
      (n + 1)
    have hE : ∀ j, E R v j • (F R v i ^ (n + 1) • hwv R v Λ) = 0 :=
      E_smul_F_pow_smul_eq_zero (NeZero.ne v) hwv_mem_weightSpace (fun j ↦ E_smul_hwv j)
        (Int.toNat_of_nonneg (hΛ i)).symm
    induction mem_triangularSpan_of u (NeZero.ne v) using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨w, μ, w', rfl⟩ := hu
      rw [mul_smul, mul_smul, plusHom_smul_of_E_smul_eq_zero hE, smul_comm (K R v μ),
        hw μ, smul_comm (minusHom R v _), smul_comm (minusHom R v _)]
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ⟨monomial k w * θ k i ^ (n + 1),
        ?_, ?_⟩)
      · have hpow : θ k i ^ (n + 1) ∈ LusztigF.weightSpace k ((n + 1) • Finsupp.single i 1) := by
          induction (n + 1) with
          | zero => simpa using one_mem_weightSpace (k := k) (I := I)
          | succ m ih =>
            rw [pow_succ, succ_nsmul]
            exact mul_mem_weightSpace ih (θ_mem_weightSpace i)
        refine mem_highSpan_of_mem (i := i)
          (mul_mem_weightSpace (monomial_mem_weightSpace w) hpow) ?_
        simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
          mul_one]
        omega
      · simp only [toVerma_apply, map_mul, map_pow, minusHom_θ, mul_smul]
    | zero => rw [zero_smul]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [add_smul]; exact add_mem hx hx'
    | smul c x _ hx => rw [smul_assoc]; exact Submodule.smul_mem _ _ hx
  intro m hm
  change m ∈ Submodule.span _ (Set.range fun i ↦ F R v i ^ ((Λ (R.coroot i)).toNat + 1) •
    hwv R v Λ) at hm
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hm
  exact Submodule.sum_mem _ fun i _ ↦ key i (c i)

variable (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

/-- **`y ↦ y⁻ v_Λ` is injective in `L̃_q(Λ)` on low weights**: if all weight components
`'f_ν` of `y` have `νᵢ ≤ ⟨i, Λ⟩⁺`, and `y⁻ v_Λ` lies in `Σᵢ U Fᵢ^{⟨i,Λ⟩⁺+1} v_Λ`, then `y` lies
in the Serre ideal. -/
theorem mem_serreIdeal_of_toVerma_mem_fPowSubmodule {Λ : Y →+ ℤ}
    (hΛ : ∀ i, 0 ≤ Λ (R.coroot i)) {y : LusztigF k I}
    (hy : ∀ ν, weightProj ν y ≠ 0 → ∀ i, ν i ≤ (Λ (R.coroot i)).toNat)
    (h : toVerma R v Λ y ∈ fPowSubmodule R v Λ) : y ∈ serreIdeal D v := by
  obtain ⟨z, hz, hzy⟩ := fPowSubmodule_le_map_toVerma hΛ h
  have hsub : y - z ∈ serreIdeal D v := by
    rw [← toVerma_eq_zero_iff (R := R) (Λ := Λ) hv', map_sub, hzy, sub_self]
  refine LusztigF.mem_serreIdeal_of_weightProj fun ν ↦ ?_
  have h1 := LusztigF.weightProj_mem_serreIdeal hsub ν
  by_cases hν : weightProj ν y = 0
  · rw [hν]; exact zero_mem _
  · have hz0 : weightProj ν z = 0 := by
      by_contra hne
      obtain ⟨i, hi⟩ := hz ν hne
      have := hy ν hν i
      omega
    rwa [map_sub, hz0, sub_zero] at h1

end VermaModule

open LusztigF VermaModule

variable [NeZero v] (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

/-- **`U⁻` acts faithfully on the modules `L̃_q(Λ)`** if `⟨i, Λ⟩` can be made arbitrarily large. -/
theorem minusHom_eq_zero_of_forall_smul_eq_zero
    (hcor : ∀ N : ℕ, ∃ Λ : Y →+ ℤ, ∀ i, (N : ℤ) ≤ Λ (R.coroot i)) (y : LusztigF k I)
    (h : ∀ (Λ : Y →+ ℤ) (m : FPowQuotient R v Λ), minusHom R v y • m = 0) :
    minusHom R v y = 0 := by
  classical
  set N := ∑ ν ∈ (gradingHom k I y).coeff.support, ∑ i ∈ ν.support, ν i
  obtain ⟨Λ, hΛ⟩ := hcor N
  rw [minusHom_eq_zero_iff R v hv']
  refine mem_serreIdeal_of_toVerma_mem_fPowSubmodule hv' (Λ := Λ) (fun i ↦ (hΛ i).trans' (by
    positivity)) (fun ν hν i ↦ ?_) ?_
  · have hνs : ν ∈ (gradingHom k I y).coeff.support := Finsupp.mem_support_iff.2 hν
    have h1 : ν i ≤ ∑ i ∈ ν.support, ν i := by
      by_cases hi : i ∈ ν.support
      · exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi
      · rw [Finsupp.notMem_support_iff.1 hi]; exact Nat.zero_le _
    have h2 : ∑ i ∈ ν.support, ν i ≤ N :=
      Finset.single_le_sum (f := fun ν : I →₀ ℕ ↦ ∑ i ∈ ν.support, ν i)
        (fun _ _ ↦ Nat.zero_le _) hνs
    have := hΛ i
    omega
  · have := h Λ (Submodule.Quotient.mk (hwv R v Λ))
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

omit hv' [NeZero v] in
/-- `ω ∘ (·)⁺ = (·)⁻` on `'f`. -/
lemma chevalley_comp_plusHom : (chevalley R v).comp (plusHom R v) = minusHom R v :=
  FreeAlgebra.hom_ext (funext fun i ↦ by
    simp only [Function.comp_apply, AlgHom.comp_apply]
    exact (congrArg (chevalley R v) (plusHom_θ R v i)).trans ((chevalley_E R v i).trans
      (minusHom_θ R v i).symm))

end LieLean.QuantumGroup

/-! ### Twisting by the Chevalley involution -/

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

/-- A `U`-module `M` with `u ∈ U` acting as `ω(u)`, `ω` the Chevalley involution
(`Eᵢ ↦ Fᵢ`, `Fᵢ ↦ Eᵢ`, `K_μ ↦ K_{-μ}`). -/
def ChevalleyTwist (_R : D.RootDatum Y) (_v : k) (M : Type*) : Type _ := M

namespace ChevalleyTwist

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

instance : AddCommGroup (ChevalleyTwist R v M) := inferInstanceAs (AddCommGroup M)

instance : Module k (ChevalleyTwist R v M) := inferInstanceAs (Module k M)

instance : Module (QuantumGroup R v) (ChevalleyTwist R v M) :=
  Module.compHom M (chevalley R v : QuantumGroup R v →+* QuantumGroup R v)

/-- The identity map `M → ʷM`. -/
def toTwist : M ≃ₗ[k] ChevalleyTwist R v M := LinearEquiv.refl k M

variable {R v M}

omit [IsScalarTower k (QuantumGroup R v) M] in
lemma smul_toTwist (u : QuantumGroup R v) (m : M) :
    u • toTwist R v M m = toTwist R v M (chevalley R v u • m) := rfl

instance : IsScalarTower k (QuantumGroup R v) (ChevalleyTwist R v M) where
  smul_assoc c u m := by
    obtain ⟨m, rfl⟩ := (toTwist R v M).surjective m
    calc (c • u) • toTwist R v M m = toTwist R v M (chevalley R v (c • u) • m) :=
          smul_toTwist _ _
      _ = toTwist R v M (c • (chevalley R v u • m)) := by
        rw [map_smul (chevalley R v) c u, smul_assoc]
      _ = c • (u • toTwist R v M m) := by rw [smul_toTwist, LinearEquiv.map_smul]

/-- The twist of an integrable module is integrable. -/
theorem isIntegrable (hM : IsIntegrable R v M) : IsIntegrable R v (ChevalleyTwist R v M) where
  iSup_weightSpace_eq_top := by
    rw [eq_top_iff]
    rintro m -
    obtain ⟨m, rfl⟩ := (toTwist R v M).surjective m
    have hm : m ∈ ⨆ Λ, weightSpace R v M Λ := by rw [hM.iSup_weightSpace_eq_top]; trivial
    induction hm using Submodule.iSup_induction' with
    | mem Λ m hm =>
      refine Submodule.mem_iSup_of_mem (-Λ) fun μ ↦ ?_
      rw [smul_toTwist, chevalley_K, hm (-μ), map_neg, AddMonoidHom.neg_apply]
      rfl
    | zero => rw [map_zero]; exact zero_mem _
    | add m m' _ _ hm hm' => rw [map_add]; exact add_mem hm hm'
  exists_E_pow_smul_eq_zero i m := by
    obtain ⟨m, rfl⟩ := (toTwist R v M).surjective m
    obtain ⟨n, hn⟩ := hM.exists_F_pow_smul_eq_zero i m
    exact ⟨n, by rw [smul_toTwist, map_pow, chevalley_E, hn, map_zero]⟩
  exists_F_pow_smul_eq_zero i m := by
    obtain ⟨m, rfl⟩ := (toTwist R v M).surjective m
    obtain ⟨n, hn⟩ := hM.exists_E_pow_smul_eq_zero i m
    exact ⟨n, by rw [smul_toTwist, map_pow, chevalley_F, hn, map_zero]⟩

end ChevalleyTwist

variable {R v} [NeZero v] (hv' : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
include hv'

/-- **`U⁺` acts faithfully on the modules `ʷL̃_q(Λ)`** if `⟨i, Λ⟩` can be made arbitrarily
large. -/
theorem plusHom_eq_zero_of_forall_smul_eq_zero
    (hcor : ∀ N : ℕ, ∃ Λ : Y →+ ℤ, ∀ i, (N : ℤ) ≤ Λ (R.coroot i)) (x : LusztigF k I)
    (h : ∀ (Λ : Y →+ ℤ) (m : ChevalleyTwist R v (FPowQuotient R v Λ)), plusHom R v x • m = 0) :
    plusHom R v x = 0 := by
  have hx : minusHom R v x = 0 := by
    refine minusHom_eq_zero_of_forall_smul_eq_zero hv' hcor x fun Λ m ↦ ?_
    have := h Λ (ChevalleyTwist.toTwist R v _ m)
    rwa [ChevalleyTwist.smul_toTwist, ← AlgHom.comp_apply, chevalley_comp_plusHom,
      LinearEquiv.map_eq_zero_iff] at this
  rwa [plusHom_eq_zero_iff R v hv', ← minusHom_eq_zero_iff R v hv']

end LieLean.QuantumGroup
