/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.KashiwaraOperators
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Integrable

/-!
# Kashiwara operators on integrable `U`-modules

Let `M` be an integrable module over `U = U_q(𝔤)` ([Lus] 3.5.1, `QuantumGroup.IsIntegrable`),
with `v` not a root of unity. For a node `i`, `M` with `Eᵢ`, `Fᵢ` and the grading by `⟨i, ·⟩` is an
integrable `U_{vᵢ}(𝔰𝔩₂)`-module (`QuantumGroup.nodeSl2`), so it carries the Kashiwara operators
`ẽᵢ`, `f̃ᵢ` of `QuantumGroup.IntegrableSl2.eTilde`, `QuantumGroup.IntegrableSl2.fTilde`
([HK] Def. 4.1.2; `QuantumGroup.kashiwaraE`, `QuantumGroup.kashiwaraF`).

## Main results

* `QuantumGroup.kashiwaraE_mem_weightSpace`, `QuantumGroup.kashiwaraF_mem_weightSpace`:
  `ẽᵢ M^Λ ⊆ M^{Λ + αᵢ}` and `f̃ᵢ M^Λ ⊆ M^{Λ - αᵢ}` ([HK] Prop. 4.1.3 (1)).
* `QuantumGroup.map_kashiwaraE`, `QuantumGroup.map_kashiwaraF`: the Kashiwara operators commute
  with homomorphisms of integrable `U`-modules ([HK] Prop. 4.1.3 (2)).
* `QuantumGroup.kashiwaraE_eq_zero_iff`: `ẽᵢ m = 0 ↔ Eᵢ m = 0` for `m ∈ M^Λ`.

The weight statements are deduced from the `ℤ`-graded ones by naturality with respect to the
projection of `M` onto `⊕_{n ∈ ℤ} M^{Λ + n αᵢ}`, which commutes with `Eᵢ`, `Fᵢ` and preserves the
grading by `⟨i, ·⟩`.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.1.
* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §3.5.
-/

open DirectSum

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-! ### Projections onto sums of weight spaces -/

section WeightProj

variable [NeZero v]

open scoped Classical in
lemma isInternal_weightSpace (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M) :
    DirectSum.IsInternal (weightSpace R v M) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_weightSpace hv)
    hM.iSup_weightSpace_eq_top

/-- The projection of an integrable module onto the sum of its weight spaces `M^Λ`, `Λ ∈ S`. -/
noncomputable def weightSetProj (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M)
    (S : Set (Y →+ ℤ)) : Module.End k M := by
  classical
  exact DirectSum.coeLinearMap (weightSpace R v M) ∘ₗ
    DFinsupp.filterLinearMap k (fun Λ ↦ weightSpace R v M Λ) (· ∈ S) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (weightSpace R v M))
      (isInternal_weightSpace hv hM)).symm.toLinearMap

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M)

open scoped Classical in
lemma weightSetProj_of_mem (S : Set (Y →+ ℤ)) {Λ : Y →+ ℤ} {m : M}
    (hm : m ∈ weightSpace R v M Λ) :
    weightSetProj hv hM S m = if Λ ∈ S then m else 0 := by
  classical
  have h : (LinearEquiv.ofBijective (DirectSum.coeLinearMap (weightSpace R v M))
      (isInternal_weightSpace hv hM)).symm m =
      DirectSum.of (fun Λ ↦ weightSpace R v M Λ) Λ ⟨m, hm⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_of (A := weightSpace R v M) Λ ⟨m, hm⟩).symm
  simp only [weightSetProj, LinearMap.comp_apply, LinearEquiv.coe_coe, h]
  rw [DirectSum.of, DFinsupp.singleAddHom_apply]
  erw [DFinsupp.filterLinearMap_apply, DFinsupp.filter_single]
  split_ifs with hΛ
  · exact DirectSum.coeLinearMap_of (A := weightSpace R v M) Λ ⟨m, hm⟩
  · exact map_zero _

omit [NeZero v] in
include hM in
/-- Linear maps agreeing on all weight vectors of an integrable module are equal. -/
lemma ext_weightSpace {N : Type*} [AddCommGroup N] [Module k N] {f g : M →ₗ[k] N}
    (h : ∀ Λ, ∀ m ∈ weightSpace R v M Λ, f m = g m) : f = g := by
  have : ⊤ ≤ LinearMap.eqLocus f g :=
    hM.iSup_weightSpace_eq_top ▸ iSup_le fun Λ m hm ↦ h Λ m hm
  ext m
  exact this Submodule.mem_top

/-- The projection onto the sum of the weight spaces in a coset of `ℤ αᵢ` commutes with `Eᵢ`. -/
lemma weightSetProj_E_smul (i : I) (S : Set (Y →+ ℤ))
    (hS : ∀ Λ, Λ + R.root i ∈ S ↔ Λ ∈ S) (m : M) :
    weightSetProj hv hM S (E R v i • m) = E R v i • weightSetProj hv hM S m := by
  have := ext_weightSpace hM (f := weightSetProj hv hM S ∘ₗ act R v M (E R v i))
    (g := act R v M (E R v i) ∘ₗ weightSetProj hv hM S) fun Λ m hm ↦ by
      simp only [LinearMap.comp_apply, Algebra.lsmul_apply]
      rw [weightSetProj_of_mem hv hM S (E_smul_mem_weightSpace hm i),
        weightSetProj_of_mem hv hM S hm, hS]
      split_ifs <;> simp
  exact LinearMap.congr_fun this m

/-- The projection onto the sum of the weight spaces in a coset of `ℤ αᵢ` commutes with `Fᵢ`. -/
lemma weightSetProj_F_smul (i : I) (S : Set (Y →+ ℤ))
    (hS : ∀ Λ, Λ - R.root i ∈ S ↔ Λ ∈ S) (m : M) :
    weightSetProj hv hM S (F R v i • m) = F R v i • weightSetProj hv hM S m := by
  have := ext_weightSpace hM (f := weightSetProj hv hM S ∘ₗ act R v M (F R v i))
    (g := act R v M (F R v i) ∘ₗ weightSetProj hv hM S) fun Λ m hm ↦ by
      simp only [LinearMap.comp_apply, Algebra.lsmul_apply]
      rw [weightSetProj_of_mem hv hM S (F_smul_mem_weightSpace hm i),
        weightSetProj_of_mem hv hM S hm, hS]
      split_ifs <;> simp
  exact LinearMap.congr_fun this m

lemma weightSetProj_mem_nodeWt (i : I) (S : Set (Y →+ ℤ)) {n : ℤ} {m : M}
    (hm : m ∈ nodeWt R v M i n) : weightSetProj hv hM S m ∈ nodeWt R v M i n := by
  refine nodeWt_induction (P := fun m ↦ weightSetProj hv hM S m ∈ nodeWt R v M i n) hm
    (by simp) (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy) fun Λ hΛ x hx ↦ ?_
  rw [weightSetProj_of_mem hv hM S hx]
  split_ifs
  · exact hΛ ▸ mem_nodeWt_of_mem hx
  · exact zero_mem _

end WeightProj

/-! ### The Kashiwara operators -/

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M) (i : I)

omit [DecidableEq I] in
lemma pow_d_ne_zero : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)

variable (R v M) in
/-- The Kashiwara operator `ẽᵢ` on an integrable `U`-module ([HK] Def. 4.1.2). -/
noncomputable def kashiwaraE : Module.End k M :=
  (nodeSl2 R v M hv hM i).eTilde (pow_d_ne_zero i) (pow_d_ne_one hv i)

variable (R v M) in
/-- The Kashiwara operator `f̃ᵢ` on an integrable `U`-module ([HK] Def. 4.1.2). -/
noncomputable def kashiwaraF : Module.End k M :=
  (nodeSl2 R v M hv hM i).fTilde (pow_d_ne_zero i) (pow_d_ne_one hv i)

/-- The coset `Λ + ℤ αᵢ`. -/
def rootCoset (Λ : Y →+ ℤ) : Set (Y →+ ℤ) := {Λ' | ∃ n : ℤ, Λ' = Λ + n • R.root i}

omit [DecidableEq I] in
lemma add_mem_rootCoset (Λ Λ' : Y →+ ℤ) :
    Λ' + R.root i ∈ rootCoset (R := R) i Λ ↔ Λ' ∈ rootCoset (R := R) i Λ := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n - 1, by rw [eq_sub_of_add_eq hn, sub_zsmul, one_zsmul]; abel⟩
  · rintro ⟨n, rfl⟩; exact ⟨n + 1, by rw [add_zsmul, one_zsmul, add_assoc]⟩

omit [DecidableEq I] in
lemma sub_mem_rootCoset (Λ Λ' : Y →+ ℤ) :
    Λ' - R.root i ∈ rootCoset (R := R) i Λ ↔ Λ' ∈ rootCoset (R := R) i Λ := by
  rw [← add_mem_rootCoset i Λ (Λ' - R.root i), sub_add_cancel]

/-- The projection onto `⊕ₙ M^{Λ + n αᵢ}` lands in `M^{Λ + s αᵢ}` on `M`'s graded piece
`⟨i, ·⟩ = ⟨i, Λ⟩ + 2s`. -/
lemma weightSetProj_rootCoset_mem (Λ : Y →+ ℤ) (s : ℤ) {m : M}
    (hm : m ∈ nodeWt R v M i (Λ (R.coroot i) + 2 * s)) :
    weightSetProj hv hM (rootCoset (R := R) i Λ) m ∈ weightSpace R v M (Λ + s • R.root i) := by
  refine nodeWt_induction (P := fun m ↦ weightSetProj hv hM (rootCoset (R := R) i Λ) m ∈
    weightSpace R v M (Λ + s • R.root i)) hm (by simp)
    (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy) fun Λ' hΛ' x hx ↦ ?_
  rw [weightSetProj_of_mem hv hM _ hx]
  split_ifs with h
  · obtain ⟨n, rfl⟩ := h
    have hn : n = s := by
      simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, R.root_coroot,
        D.cartanMatrix_self, smul_eq_mul] at hΛ'
      omega
    exact hn ▸ hx
  · exact zero_mem _

/-- An endomorphism of `M` which shifts the grading by `⟨i, ·⟩` by `2s` and commutes with the
projections onto the sums of weight spaces over cosets of `ℤ αᵢ` maps `M^Λ` to `M^{Λ + s αᵢ}`. -/
lemma mem_weightSpace_of_comm_weightSetProj (T : Module.End k M) (s : ℤ)
    (hT : ∀ n, ∀ m ∈ nodeWt R v M i n, T m ∈ nodeWt R v M i (n + 2 * s))
    (hTP : ∀ Λ m, T (weightSetProj hv hM (rootCoset (R := R) i Λ) m) =
      weightSetProj hv hM (rootCoset (R := R) i Λ) (T m))
    {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) :
    T m ∈ weightSpace R v M (Λ + s • R.root i) := by
  have hP : weightSetProj hv hM (rootCoset (R := R) i Λ) m = m := by
    rw [weightSetProj_of_mem hv hM _ hm]
    simp [show Λ ∈ rootCoset (R := R) i Λ from ⟨0, by simp⟩]
  rw [← hP, hTP]
  exact weightSetProj_rootCoset_mem hv hM i Λ s (hT _ m (mem_nodeWt_of_mem hm))

/-- The projection onto a coset of `ℤ αᵢ` commutes with `ẽᵢ` and `f̃ᵢ`. -/
lemma weightSetProj_rootCoset_comm (Λ : Y →+ ℤ) (T : Module.End k M)
    (hT : ∀ (f : Module.End k M), (∀ m, f ((nodeSl2 R v M hv hM i).E m) =
      (nodeSl2 R v M hv hM i).E (f m)) → (∀ m, f ((nodeSl2 R v M hv hM i).F m) =
      (nodeSl2 R v M hv hM i).F (f m)) →
      (∀ n, ∀ m ∈ (nodeSl2 R v M hv hM i).wt n, f m ∈ (nodeSl2 R v M hv hM i).wt n) →
      ∀ m, f (T m) = T (f m)) (m : M) :
    T (weightSetProj hv hM (rootCoset (R := R) i Λ) m) =
      weightSetProj hv hM (rootCoset (R := R) i Λ) (T m) :=
  (hT _ (fun m ↦ weightSetProj_E_smul hv hM i _ (add_mem_rootCoset i Λ) m)
    (fun m ↦ weightSetProj_F_smul hv hM i _ (sub_mem_rootCoset i Λ) m)
    (fun _ _ hm ↦ weightSetProj_mem_nodeWt hv hM i _ hm) m).symm

/-- `ẽᵢ M^Λ ⊆ M^{Λ + αᵢ}` ([HK] Prop. 4.1.3 (1)). -/
theorem kashiwaraE_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) :
    kashiwaraE R v M hv hM i m ∈ weightSpace R v M (Λ + R.root i) := by
  have := mem_weightSpace_of_comm_weightSetProj hv hM i (kashiwaraE R v M hv hM i) 1
    (fun n m hm ↦ by
      rw [mul_one]
      exact IntegrableSl2.eTilde_mem (V := nodeSl2 R v M hv hM i) _ _ hm)
    (fun Λ m ↦ weightSetProj_rootCoset_comm hv hM i Λ _
      (fun f hE hF hwt m ↦ (IntegrableSl2.map_eTilde _ _ _ f hE hF hwt m)) m) hm
  rwa [one_zsmul] at this

/-- `f̃ᵢ M^Λ ⊆ M^{Λ - αᵢ}` ([HK] Prop. 4.1.3 (1)). -/
theorem kashiwaraF_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) :
    kashiwaraF R v M hv hM i m ∈ weightSpace R v M (Λ - R.root i) := by
  have := mem_weightSpace_of_comm_weightSetProj hv hM i (kashiwaraF R v M hv hM i) (-1)
    (fun n m hm ↦ by
      rw [show n + 2 * (-1) = n - 2 by ring]
      exact IntegrableSl2.fTilde_mem (V := nodeSl2 R v M hv hM i) _ _ hm)
    (fun Λ m ↦ weightSetProj_rootCoset_comm hv hM i Λ _
      (fun f hE hF hwt m ↦ (IntegrableSl2.map_fTilde _ _ _ f hE hF hwt m)) m) hm
  rwa [neg_one_zsmul, ← sub_eq_add_neg] at this

/-- `ẽᵢ m = 0` if and only if `Eᵢ m = 0`, for `m ∈ M^Λ`. -/
theorem kashiwaraE_eq_zero_iff {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) :
    kashiwaraE R v M hv hM i m = 0 ↔ E R v i • m = 0 :=
  IntegrableSl2.eTilde_eq_zero_iff (V := nodeSl2 R v M hv hM i) _ _ (mem_nodeWt_of_mem hm)

/-! ### Naturality -/

variable {M' : Type*} [AddCommGroup M'] [Module k M'] [Module (QuantumGroup R v) M']
  [IsScalarTower k (QuantumGroup R v) M'] (hM' : IsIntegrable R v M')

omit [NeZero v] in
lemma map_mem_weightSpace (f : M →ₗ[QuantumGroup R v] M') {Λ : Y →+ ℤ} {m : M}
    (hm : m ∈ weightSpace R v M Λ) : f m ∈ weightSpace R v M' Λ := fun μ ↦ by
  rw [← map_smul, hm μ, LinearMap.map_smul_of_tower]

omit [NeZero v] in
lemma map_mem_nodeWt (f : M →ₗ[QuantumGroup R v] M') {n : ℤ} {m : M}
    (hm : m ∈ nodeWt R v M i n) : f m ∈ nodeWt R v M' i n :=
  nodeWt_induction (P := fun m ↦ f m ∈ nodeWt R v M' i n) hm (by simp)
    (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy)
    fun Λ hΛ x hx ↦ hΛ ▸ mem_nodeWt_of_mem (map_mem_weightSpace f hx)

/-- The Kashiwara operator `ẽᵢ` commutes with homomorphisms of integrable `U`-modules
([HK] Prop. 4.1.3 (2)). -/
theorem map_kashiwaraE (f : M →ₗ[QuantumGroup R v] M') (m : M) :
    f (kashiwaraE R v M hv hM i m) = kashiwaraE R v M' hv hM' i (f m) :=
  IntegrableSl2.map_eTilde _ _ (nodeSl2 R v M' hv hM' i) (f.restrictScalars k)
    (fun m ↦ map_smul f _ m) (fun m ↦ map_smul f _ m) (fun _ _ hm ↦ map_mem_nodeWt i f hm) m

/-- The Kashiwara operator `f̃ᵢ` commutes with homomorphisms of integrable `U`-modules
([HK] Prop. 4.1.3 (2)). -/
theorem map_kashiwaraF (f : M →ₗ[QuantumGroup R v] M') (m : M) :
    f (kashiwaraF R v M hv hM i m) = kashiwaraF R v M' hv hM' i (f m) :=
  IntegrableSl2.map_fTilde _ _ (nodeSl2 R v M' hv hM' i) (f.restrictScalars k)
    (fun m ↦ map_smul f _ m) (fun m ↦ map_smul f _ m) (fun _ _ hm ↦ map_mem_nodeWt i f hm) m

end LieLean.QuantumGroup
