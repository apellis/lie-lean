/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Rank1Formula
import LieLean.Algebra.QuantumGroup.Integrable
import LieLean.Algebra.QuantumGroup.BraidAction.OrthogonalGeneral

/-!
# The symmetries `Tᵢ` of integrable `U`-modules

Let `M` be an integrable module ([Lus] 3.5.1; `QuantumGroup.IsIntegrable`) over `U = U_q(𝔤)`, with
`v` not a root of unity, and fix a node `i`. Then `M` with `Eᵢ`, `Fᵢ` and the grading by
`⟨i, Λ⟩` (the sum of the weight spaces `M^Λ` with `⟨i, Λ⟩ = n` in degree `n`) is an integrable
`U_{vᵢ}(𝔰𝔩₂)`-module (`QuantumGroup.nodeSl2`), so it carries Lusztig's symmetry
`T''_{i,1}` (`QuantumGroup.IntegrableSl2.T` at `t = vᵢ`). We show that it is compatible with the
automorphism `Tᵢ = T''_{i,1}` of `U` (any algebra endomorphism with Lusztig's generator formulas,
`QuantumGroup.HasBraidGeneratorImages`):
`Tᵢ(u m) = Tᵢ(u) Tᵢ(m)` for all `u ∈ U` and `m ∈ M` (`QuantumGroup.nodeSl2_T_smul`;
[Lus] 37.1.2, [Jan] 8.6, 8.10, 8.13), and that `Tᵢ` maps `M^Λ` to `M^{sᵢΛ}`
(`QuantumGroup.nodeSl2_T_mem_weightSpace`).

For the generators `Eᵢ`, `Fᵢ`, `K_μ` this is the rank-one theory of
`QuantumGroup/ModuleSymmetry/Rank1.lean`. For `Eⱼ` (`j ≠ i`, `r = -aᵢⱼ`) we argue as follows
(our own argument; Jantzen computes `Tᵢ(Eⱼ v)` directly from the definition):
the identity `T(Eⱼ m) = Tᵢ(Eⱼ) T(m)` is stable under `m ↦ Fᵢ m`, because `Eⱼ` commutes with
`Fᵢ`; so it suffices to prove it for primitive vectors `η ∈ Mᵖ`. There
`Tᵢ(Eⱼ) T(η) = (-1)^p vᵢ^p Ψ_{p,r}(Eⱼ η)` by Lusztig's formula for `Tᵢ(Eⱼ)`, and `Eⱼ η` lies in
the span of the strings `F^{(k)} ζ` with `k ≤ r` (it is killed by `Eᵢ^{r+1}`, by the quantum
Serre relation, and by `Fᵢ^{p+1}`), where `T = (-1)^p vᵢ^p Ψ_{p,r}`
(`QuantumGroup.IntegrableSl2.T_eq_psi_of_mem`). The case of `Fⱼ` is the same argument for the
structure with `E` and `F` interchanged.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, §5.2, §37.1.
* [Jan] J. C. Jantzen, *Lectures on quantum groups*, GSM 6, §§8.6–8.13.
-/

open Finset

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

/-! ### The grading by a node -/

variable (R v M) in
/-- The sum of the weight spaces `M^Λ` with `⟨i, Λ⟩ = n`. -/
def nodeWt (i : I) (n : ℤ) : Submodule k M :=
  ⨆ (Λ : Y →+ ℤ) (_ : Λ (R.coroot i) = n), weightSpace R v M Λ

lemma mem_nodeWt_of_mem {i : I} {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) :
    m ∈ nodeWt R v M i (Λ (R.coroot i)) :=
  (le_iSup₂_of_le (f := fun (Λ' : Y →+ ℤ) (_ : Λ' (R.coroot i) = Λ (R.coroot i)) ↦
    weightSpace R v M Λ') Λ rfl le_rfl) hm

lemma nodeWt_induction {i : I} {n : ℤ} {P : M → Prop} {m : M} (hm : m ∈ nodeWt R v M i n)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hmem : ∀ Λ : Y →+ ℤ, Λ (R.coroot i) = n → ∀ x ∈ weightSpace R v M Λ, P x) : P m :=
  Submodule.iSup_induction _ (motive := P) hm
    (fun Λ _ hx ↦ Submodule.iSup_induction _ (motive := P) hx
      (fun hΛ y hy ↦ hmem Λ hΛ y hy) h0 hadd) h0 hadd

lemma E_smul_mem_nodeWt [NeZero v] {i : I} {n : ℤ} {m : M} (hm : m ∈ nodeWt R v M i n)
    (j : I) : E R v j • m ∈ nodeWt R v M i (n + D.cartanMatrix i j) := by
  refine nodeWt_induction (P := fun x ↦ E R v j • x ∈ nodeWt R v M i (n + D.cartanMatrix i j))
    hm (by simp) (fun x y hx hy ↦ by rw [smul_add]; exact add_mem hx hy) fun Λ hΛ x hx ↦ ?_
  have := mem_nodeWt_of_mem (i := i) (E_smul_mem_weightSpace hx j)
  rwa [AddMonoidHom.add_apply, hΛ, R.root_coroot] at this

lemma F_smul_mem_nodeWt [NeZero v] {i : I} {n : ℤ} {m : M} (hm : m ∈ nodeWt R v M i n)
    (j : I) : F R v j • m ∈ nodeWt R v M i (n - D.cartanMatrix i j) := by
  refine nodeWt_induction (P := fun x ↦ F R v j • x ∈ nodeWt R v M i (n - D.cartanMatrix i j))
    hm (by simp) (fun x y hx hy ↦ by rw [smul_add]; exact add_mem hx hy) fun Λ hΛ x hx ↦ ?_
  have := mem_nodeWt_of_mem (i := i) (F_smul_mem_weightSpace hx j)
  rwa [AddMonoidHom.sub_apply, hΛ, R.root_coroot] at this

lemma Kt_smul_of_mem_nodeWt {i : I} {n : ℤ} {m : M} (hm : m ∈ nodeWt R v M i n) :
    Kt R v i • m = (v ^ D.d i) ^ n • m :=
  nodeWt_induction (P := fun x ↦ Kt R v i • x = (v ^ D.d i) ^ n • x) hm (by simp)
    (fun x y hx hy ↦ by rw [smul_add, hx, hy, smul_add]) fun Λ hΛ x hx ↦ by
      rw [Kt_smul_of_mem_weightSpace hx, hΛ]

lemma K_neg_ktilde_smul_of_mem_nodeWt {i : I} {n : ℤ} {m : M} (hm : m ∈ nodeWt R v M i n) :
    K R v (-ktilde R i) • m = (v ^ D.d i) ^ (-n) • m :=
  nodeWt_induction (P := fun x ↦ K R v (-ktilde R i) • x = (v ^ D.d i) ^ (-n) • x) hm (by simp)
    (fun x y hx hy ↦ by rw [smul_add, hx, hy, smul_add]) fun Λ hΛ x hx ↦ by
      rw [K_neg_ktilde_smul_of_mem_weightSpace hx, hΛ]

lemma iSupIndep_nodeWt [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    iSupIndep (nodeWt R v M i) := by
  intro n
  have h := (iSupIndep_weightSpace (R := R) (M := M) hv).disjoint_biSup_biSup
    (s := {Λ : Y →+ ℤ | Λ (R.coroot i) = n}) (t := {Λ : Y →+ ℤ | Λ (R.coroot i) ≠ n})
    (Set.disjoint_left.2 fun _ h1 h2 ↦ h2 h1)
  refine h.mono le_rfl ?_
  refine iSup₂_le fun n' hn' ↦ iSup₂_le fun Λ hΛ ↦ ?_
  exact le_biSup (weightSpace R v M) (show Λ (R.coroot i) ≠ n from hΛ ▸ hn')

lemma iSup_nodeWt (hM : IsIntegrable R v M) (i : I) : ⨆ n, nodeWt R v M i n = ⊤ := by
  rw [eq_top_iff, ← hM.iSup_weightSpace_eq_top]
  exact iSup_le fun Λ ↦ (le_iSup₂_of_le (f := fun (Λ' : Y →+ ℤ)
    (_ : Λ' (R.coroot i) = Λ (R.coroot i)) ↦ weightSpace R v M Λ') Λ rfl le_rfl).trans
    (le_iSup (nodeWt R v M i) (Λ (R.coroot i)))

omit [DecidableEq I] in
lemma pow_d_ne_one (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (i : I) :
    ∀ n : ℕ, 0 < n → (v ^ D.d i) ^ n ≠ 1 := fun n hn ↦ by
  rw [← pow_mul]
  exact hv _ (Nat.mul_pos (D.d_pos i) hn)

/-! ### The rank-one structure at a node -/

variable (R v M) in
/-- The action of `U` on `M` as an algebra homomorphism `U → End_k M`. -/
noncomputable abbrev act : QuantumGroup R v →ₐ[k] Module.End k M := Algebra.lsmul k k M

lemma act_qDivPow (q : k) (n : ℕ) (a : QuantumGroup R v) :
    act R v M (qDivPow q n a) = qDivPow q n (act R v M a) := by
  simp only [qDivPow, map_smul, map_pow]

variable (R v M) in
/-- `M` as an integrable `U_{vᵢ}(𝔰𝔩₂)`-module through `Eᵢ`, `Fᵢ` and the grading by `⟨i, ·⟩`. -/
noncomputable def nodeSl2 [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (hM : IsIntegrable R v M) (i : I) : IntegrableSl2 (v ^ D.d i) M where
  E := act R v M (E R v i)
  F := act R v M (F R v i)
  wt := nodeWt R v M i
  iSupIndep_wt := iSupIndep_nodeWt hv i
  iSup_wt := iSup_nodeWt hM i
  E_mem {n m} h := by
    have := E_smul_mem_nodeWt h i
    rwa [D.cartanMatrix_self] at this
  F_mem {n m} h := by
    have := F_smul_mem_nodeWt h i
    rwa [D.cartanMatrix_self] at this
  E_F_sub {n m} h := by
    change E R v i • F R v i • m - F R v i • E R v i • m = _
    rw [← mul_smul, ← mul_smul, ← sub_smul, E_mul_F_sub]
    simp only [↓reduceIte]
    rw [smul_assoc, sub_smul,
      Kt_smul_of_mem_nodeWt h, K_neg_ktilde_smul_of_mem_nodeWt h, ← sub_smul, smul_smul, qIntZ,
      div_eq_inv_mul]
  exists_E_pow_eq_zero m := by
    obtain ⟨N, hN⟩ := hM.exists_E_pow_smul_eq_zero i m
    exact ⟨N, by rw [← map_pow]; exact hN⟩
  exists_F_pow_eq_zero m := by
    obtain ⟨N, hN⟩ := hM.exists_F_pow_smul_eq_zero i m
    exact ⟨N, by rw [← map_pow]; exact hN⟩

section Node

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M) (i : I)

lemma nodeSl2_E : (nodeSl2 R v M hv hM i).E = act R v M (E R v i) := rfl

lemma nodeSl2_F : (nodeSl2 R v M hv hM i).F = act R v M (F R v i) := rfl

lemma nodeSl2_wt (n : ℤ) : (nodeSl2 R v M hv hM i).wt n = nodeWt R v M i n := rfl

lemma nodeSl2_dE_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) (a : ℕ) :
    (nodeSl2 R v M hv hM i).dE a m ∈ weightSpace R v M (Λ + (a : ℤ) • R.root i) := by
  rw [IntegrableSl2.dE_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [nodeSl2_E, ← map_pow, Algebra.lsmul_apply]
  induction a with
  | zero => simpa using hm
  | succ a ih =>
    rw [pow_succ', mul_smul]
    have := E_smul_mem_weightSpace ih i
    rwa [add_assoc, ← add_one_zsmul, show ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) by push_cast; ring]
      at this

lemma nodeSl2_dF_mem_weightSpace {Λ : Y →+ ℤ} {m : M} (hm : m ∈ weightSpace R v M Λ) (b : ℕ) :
    (nodeSl2 R v M hv hM i).dF b m ∈ weightSpace R v M (Λ - (b : ℤ) • R.root i) := by
  rw [IntegrableSl2.dF_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [nodeSl2_F, ← map_pow, Algebra.lsmul_apply]
  induction b with
  | zero => simpa using hm
  | succ b ih =>
    rw [pow_succ', mul_smul]
    have := F_smul_mem_weightSpace ih i
    rwa [sub_sub, ← add_one_zsmul, show ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) by push_cast; ring]
      at this

/-- `Tᵢ` maps `M^Λ` to `M^{sᵢΛ}`, `sᵢΛ = Λ - ⟨i, Λ⟩ i'`. -/
theorem nodeSl2_T_mem_weightSpace (t : k) {Λ : Y →+ ℤ} {m : M}
    (hm : m ∈ weightSpace R v M Λ) :
    (nodeSl2 R v M hv hM i).T t m ∈ weightSpace R v M (Λ - Λ (R.coroot i) • R.root i) := by
  set V := nodeSl2 R v M hv hM i
  have hm' : m ∈ V.wt (Λ (R.coroot i)) := mem_nodeWt_of_mem hm
  rw [IntegrableSl2.T_of_mem' V t hm', finsum_eq_sum _ (V.hasFiniteSupport_symmTerm t _ m)]
  refine Submodule.sum_mem _ fun ⟨a, c⟩ _ ↦ ?_
  simp only [IntegrableSl2.symmTerm_apply]
  split_ifs with h
  · refine Submodule.smul_mem _ _ ?_
    have hb : (((Λ (R.coroot i) + a + c).toNat : ℕ) : ℤ) = Λ (R.coroot i) + a + c :=
      Int.toNat_of_nonneg h
    have := nodeSl2_dE_mem_weightSpace hv hM i (nodeSl2_dF_mem_weightSpace hv hM i
      (nodeSl2_dE_mem_weightSpace hv hM i hm c) (Λ (R.coroot i) + a + c).toNat) a
    convert this using 2
    rw [hb]
    ext μ
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    ring
  · exact zero_mem _

/-- `Tᵢ(K_μ m) = K_{sᵢμ} Tᵢ(m)`. -/
theorem nodeSl2_T_K (t : k) (μ : Y) (m : M) :
    (nodeSl2 R v M hv hM i).T t (K R v μ • m) =
      K R v (reflY R i μ) • (nodeSl2 R v M hv hM i).T t m := by
  have hm : m ∈ ⨆ Λ, weightSpace R v M Λ := hM.iSup_weightSpace_eq_top ▸ Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun m ↦ (nodeSl2 R v M hv hM i).T t
    (K R v μ • m) = K R v (reflY R i μ) • (nodeSl2 R v M hv hM i).T t m) hm
    (fun Λ x hx ↦ ?_) (by simp) fun x y hx hy ↦ by
      rw [smul_add, map_add, hx, hy, map_add, smul_add]
  rw [hx μ, map_smul, nodeSl2_T_mem_weightSpace hv hM i t hx (reflY R i μ)]
  congr 2
  rw [reflY_apply]
  simp only [map_sub, map_zsmul, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, smul_eq_mul,
    R.root_coroot, D.cartanMatrix_self]
  ring

end Node

/-! ### Compatibility with `Tᵢ` on `U` -/

/-- A quantum Serre relation `S(a, b) = 0` gives `aᵐ b x = 0` whenever `a x = 0`. -/
lemma pow_mul_smul_eq_zero_of_qSerre {q : k} {m : ℕ} {a b : QuantumGroup R v} {x : M}
    (h : qSerre q m a b = 0) (hx : a • x = 0) : (a ^ m * b) • x = 0 := by
  have e : qSerre q m a b • x = 0 := by rw [h, zero_smul]
  rw [qSerre, Finset.sum_smul] at e
  rw [Finset.sum_eq_single 0 (fun r _ hr ↦ ?_) (fun h ↦ (h (by simp)).elim)] at e
  · simpa using e
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    rw [smul_assoc, pow_succ a r, ← mul_assoc, mul_smul (a ^ (m - (r + 1)) * b * a ^ r) a x, hx,
      smul_zero, smul_zero]

section Compat

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M) {i : I}
  {Ti : QuantumGroup R v →ₐ[k] QuantumGroup R v} (H : HasBraidGeneratorImages i Ti)
include H

/-- `Tᵢ(Eᵢ m) = Tᵢ(Eᵢ) Tᵢ(m)`, `Tᵢ(Eᵢ) = -Fᵢ K̃ᵢ`. -/
theorem nodeSl2_T_E_self (m : M) :
    (nodeSl2 R v M hv hM i).T (v ^ D.d i) (E R v i • m) =
      Ti (E R v i) • (nodeSl2 R v M hv hM i).T (v ^ D.d i) m := by
  set V := nodeSl2 R v M hv hM i
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hqr := pow_d_ne_one (D := D) hv i
  rw [H.map_E]
  simp only [↓reduceIte]
  have key := V.ext_wt (f := V.T (v ^ D.d i) ∘ₗ act R v M (E R v i))
    (g := act R v M (braidEi R i) ∘ₗ V.T (v ^ D.d i)) fun n m hm ↦ by
      simp only [LinearMap.comp_apply, Algebra.lsmul_apply]
      have hT := V.T_mem (v ^ D.d i) hm
      rw [show E R v i • m = V.E m from rfl,
        IntegrableSl2.T_E hq0 hqr hq0 (fun _ _ ↦ rfl) hm, braidEi, neg_smul, neg_smul, mul_smul,
        Kt_smul_of_mem_nodeWt hT, smul_comm]
      rfl
  exact LinearMap.congr_fun key m

/-- `Tᵢ(Fᵢ m) = Tᵢ(Fᵢ) Tᵢ(m)`, `Tᵢ(Fᵢ) = -K̃ᵢ⁻¹ Eᵢ`. -/
theorem nodeSl2_T_F_self (m : M) :
    (nodeSl2 R v M hv hM i).T (v ^ D.d i) (F R v i • m) =
      Ti (F R v i) • (nodeSl2 R v M hv hM i).T (v ^ D.d i) m := by
  set V := nodeSl2 R v M hv hM i
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hqr := pow_d_ne_one (D := D) hv i
  rw [H.map_F]
  simp only [↓reduceIte]
  have key := V.ext_wt (f := V.T (v ^ D.d i) ∘ₗ act R v M (F R v i))
    (g := act R v M (braidFi R i) ∘ₗ V.T (v ^ D.d i)) fun n m hm ↦ by
      simp only [LinearMap.comp_apply, Algebra.lsmul_apply]
      have hT : E R v i • V.T (v ^ D.d i) m ∈ nodeWt R v M i (-n + 2) :=
        V.E_mem (V.T_mem (v ^ D.d i) hm)
      rw [show F R v i • m = V.F m from rfl,
        IntegrableSl2.T_F hq0 hqr hq0 (fun _ _ ↦ rfl) hm, braidFi, neg_smul, neg_smul, mul_smul,
        K_neg_ktilde_smul_of_mem_nodeWt hT, show -(-n + 2) = n - 2 by ring]
      rfl
  exact LinearMap.congr_fun key m

/-- `Tᵢ(Eⱼ m) = Tᵢ(Eⱼ) Tᵢ(m)` for `j ≠ i` ([Lus] 37.1.2, [Jan] 8.10). -/
theorem nodeSl2_T_E_ne {j : I} (hji : j ≠ i) (m : M) :
    (nodeSl2 R v M hv hM i).T (v ^ D.d i) (E R v j • m) =
      Ti (E R v j) • (nodeSl2 R v M hv hM i).T (v ^ D.d i) m := by
  set V := nodeSl2 R v M hv hM i
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hqr := pow_d_ne_one (D := D) hv i
  have hij : i ≠ j := Ne.symm hji
  have hr : qFactorial (v ^ D.d i) (negA D i j) ≠ 0 :=
    qFactorial_ne_zero_of_pow_ne_one hq0 hqr _
  have hEF : E R v j * F R v i = F R v i * E R v j := by
    have := E_mul_F_sub (R := R) (v := v) j i
    simp only [hji, ↓reduceIte] at this
    exact sub_eq_zero.1 this
  have hZF : ∀ x, act R v M (E R v j) (V.F x) = V.F (act R v M (E R v j) x) := fun x ↦ by
    change E R v j • F R v i • x = F R v i • E R v j • x
    rw [← mul_smul, hEF, mul_smul]
  have hZwt : ∀ n, ∀ x ∈ V.wt n, act R v M (E R v j) x ∈ V.wt (n - negA D i j) := by
    intro n x hx
    have := E_smul_mem_nodeWt hx j
    rwa [cartanMatrix_eq_neg_negA hij, ← sub_eq_add_neg] at this
  have hZE : ∀ (p : ℕ) η, η ∈ V.wt p → V.E η = 0 →
      (V.E ^ (negA D i j + 1)) (act R v M (E R v j) η) = 0 := by
    intro p η _ hE
    have hs := serre_E (R := R) (v := v) hij
    rw [one_sub_cartanMatrix_toNat hij] at hs
    change (act R v M (E R v i) ^ (negA D i j + 1)) (act R v M (E R v j) η) = 0
    rw [← map_pow, Algebra.lsmul_apply, Algebra.lsmul_apply, ← mul_smul]
    exact pow_mul_smul_eq_zero_of_qSerre hs hE
  have hX : ∀ (p : ℕ) η, η ∈ V.wt p → V.E η = 0 →
      act R v M (Ti (E R v j)) (V.T (v ^ D.d i) η) =
        ((-1) ^ p * (v ^ D.d i) ^ p) • V.psi p (negA D i j) (act R v M (E R v j) η) := by
    intro p η hη hE
    have hT0 : V.T (v ^ D.d i) η = ((-1) ^ p * (v ^ D.d i) ^ p) • V.dF p η := by
      have := IntegrableSl2.T_dF_of_primitive hq0 hqr hq0 (fun _ _ ↦ rfl) hη hE (Nat.zero_le p)
      simpa using this
    rw [hT0, map_smul, H.map_E]
    simp only [hji, ↓reduceIte]
    rw [braidEj_eq_sum hr, map_sum, LinearMap.sum_apply, IntegrableSl2.psi_apply]
    congr 1
    refine sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, map_mul, map_mul, act_qDivPow, act_qDivPow, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.mul_apply]
    change ((-1) ^ s * (v ^ D.d i)⁻¹ ^ s) •
      V.dE (negA D i j - s) (act R v M (E R v j) (V.dE s (V.dF p η))) = _
    split_ifs with hsp
    · rw [IntegrableSl2.dE_dF_of_primitive hq0 hqr hη hE hsp le_rfl, Nat.sub_self, zero_add,
        qBinomial_self, one_smul, IntegrableSl2.comm_dF (V := V) _ hZF]
    · rw [IntegrableSl2.dE_dF_eq_zero_of_lt hq0 hqr hη hE le_rfl (by omega), map_zero,
        map_zero, smul_zero, zero_smul]
  have hG : ∀ x, V.T (v ^ D.d i) (V.F x) =
      act R v M (Ti (F R v i)) (V.T (v ^ D.d i) x) :=
    fun x ↦ nodeSl2_T_F_self hv hM H x
  have hXG : ∀ x, act R v M (Ti (E R v j)) (act R v M (Ti (F R v i)) x) =
      act R v M (Ti (F R v i)) (act R v M (Ti (E R v j)) x) := fun x ↦ by
    change Ti (E R v j) • Ti (F R v i) • x = Ti (F R v i) • Ti (E R v j) • x
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, hEF]
  exact IntegrableSl2.T_comp_eq_of_psi hq0 hqr V (V.T (v ^ D.d i)) (act R v M (E R v j))
    (act R v M (Ti (E R v j))) (act R v M (Ti (F R v i))) (negA D i j)
    (fun p ↦ (-1) ^ p * (v ^ D.d i) ^ p) (fun _ _ hw ↦ IntegrableSl2.T_eq_psi_of_mem hq0 hqr hw)
    hZF hZwt hZE hX hG hXG m

/-- `Tᵢ(Fⱼ m) = Tᵢ(Fⱼ) Tᵢ(m)` for `j ≠ i` ([Lus] 37.1.2, [Jan] 8.10(4)). -/
theorem nodeSl2_T_F_ne {j : I} (hji : j ≠ i) (m : M) :
    (nodeSl2 R v M hv hM i).T (v ^ D.d i) (F R v j • m) =
      Ti (F R v j) • (nodeSl2 R v M hv hM i).T (v ^ D.d i) m := by
  set V := nodeSl2 R v M hv hM i
  have hq0 : v ^ D.d i ≠ 0 := pow_ne_zero _ (NeZero.ne v)
  have hqr := pow_d_ne_one (D := D) hv i
  have hij : i ≠ j := Ne.symm hji
  have hr : qFactorial (v ^ D.d i) (negA D i j) ≠ 0 :=
    qFactorial_ne_zero_of_pow_ne_one hq0 hqr _
  have hEF : E R v i * F R v j = F R v j * E R v i := by
    have := E_mul_F_sub (R := R) (v := v) i j
    simp only [hij, ↓reduceIte] at this
    exact sub_eq_zero.1 this
  have hZF : ∀ x, act R v M (F R v j) (V.flip.F x) = V.flip.F (act R v M (F R v j) x) :=
    fun x ↦ by
      change F R v j • E R v i • x = E R v i • F R v j • x
      rw [← mul_smul, ← hEF, mul_smul]
  have hZwt : ∀ n, ∀ x ∈ V.flip.wt n, act R v M (F R v j) x ∈ V.flip.wt (n - negA D i j) := by
    intro n x hx
    have := F_smul_mem_nodeWt (show x ∈ nodeWt R v M i (-n) from hx) j
    rw [cartanMatrix_eq_neg_negA hij, show -n - -(negA D i j : ℤ) = -(n - negA D i j) by ring]
      at this
    exact this
  have hZE : ∀ (p : ℕ) η, η ∈ V.flip.wt p → V.flip.E η = 0 →
      (V.flip.E ^ (negA D i j + 1)) (act R v M (F R v j) η) = 0 := by
    intro p η _ hE
    have hs := serre_F (R := R) (v := v) hij
    rw [one_sub_cartanMatrix_toNat hij] at hs
    change (act R v M (F R v i) ^ (negA D i j + 1)) (act R v M (F R v j) η) = 0
    rw [← map_pow, Algebra.lsmul_apply, Algebra.lsmul_apply, ← mul_smul]
    exact pow_mul_smul_eq_zero_of_qSerre hs hE
  have hX : ∀ (p : ℕ) η, η ∈ V.flip.wt p → V.flip.E η = 0 →
      act R v M (Ti (F R v j)) (V.T (v ^ D.d i) η) =
        ((-1) ^ negA D i j * (v ^ D.d i) ^ negA D i j) •
          V.flip.psi p (negA D i j) (act R v M (F R v j) η) := by
    intro p η hη hE
    rw [IntegrableSl2.T_of_lowest hq0 hqr hq0 (fun _ _ ↦ rfl) hη hE, H.map_F]
    simp only [hji, ↓reduceIte]
    rw [braidFj_eq_sum (NeZero.ne v) hr, map_sum, LinearMap.sum_apply, IntegrableSl2.psi_apply,
      smul_sum]
    conv_rhs => rw [← sum_range_reflect]
    refine sum_congr rfl fun s hs ↦ ?_
    simp only [mem_range] at hs
    rw [map_smul, map_mul, map_mul, act_qDivPow, act_qDivPow, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Nat.add_sub_cancel,
      show negA D i j - (negA D i j - s) = s by omega]
    change ((-1) ^ s * (v ^ D.d i) ^ s) •
      V.flip.dE s (act R v M (F R v j) (V.flip.dE (negA D i j - s) (V.flip.dF p η))) = _
    split_ifs with hsp
    · rw [IntegrableSl2.dE_dF_of_primitive (V := V.flip) hq0 hqr hη hE hsp le_rfl, Nat.sub_self,
        zero_add, qBinomial_self, one_smul, IntegrableSl2.comm_dF (V := V.flip) _ hZF, smul_smul]
      congr 1
      rw [IntegrableSl2.neg_one_pow_sub (show s ≤ negA D i j by omega),
        IntegrableSl2.inv_pow_sub hq0 (show s ≤ negA D i j by omega)]
      have h1 : ((-1 : k) ^ negA D i j) ^ 2 = 1 := by
        rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
      have h2 : (v ^ D.d i) ^ negA D i j * (v ^ D.d i)⁻¹ ^ negA D i j = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hq0, one_pow]
      linear_combination (-(-1) ^ s * (v ^ D.d i) ^ s) * h2 +
        (-(-1) ^ s * (v ^ D.d i) ^ s * ((v ^ D.d i) ^ negA D i j *
          (v ^ D.d i)⁻¹ ^ negA D i j)) * h1
    · rw [IntegrableSl2.dE_dF_eq_zero_of_lt (V := V.flip) hq0 hqr hη hE le_rfl (by omega),
        map_zero, map_zero, smul_zero, zero_smul, smul_zero]
  have hG : ∀ x, V.T (v ^ D.d i) (V.flip.F x) =
      act R v M (Ti (E R v i)) (V.T (v ^ D.d i) x) :=
    fun x ↦ nodeSl2_T_E_self hv hM H x
  have hXG : ∀ x, act R v M (Ti (F R v j)) (act R v M (Ti (E R v i)) x) =
      act R v M (Ti (E R v i)) (act R v M (Ti (F R v j)) x) := fun x ↦ by
    change Ti (F R v j) • Ti (E R v i) • x = Ti (E R v i) • Ti (F R v j) • x
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, hEF]
  exact IntegrableSl2.T_comp_eq_of_psi hq0 hqr V.flip (V.T (v ^ D.d i)) (act R v M (F R v j))
    (act R v M (Ti (F R v j))) (act R v M (Ti (E R v i))) (negA D i j)
    (fun _ ↦ (-1) ^ negA D i j * (v ^ D.d i) ^ negA D i j)
    (fun _ _ hw ↦ IntegrableSl2.T_eq_flip_psi hq0 hqr hw) hZF hZwt hZE hX hG hXG m

/-- **Compatibility of the symmetries of `U` and of integrable modules**: `Tᵢ(u m) = Tᵢ(u) Tᵢ(m)`
for all `u ∈ U`, `m ∈ M`, where on `M`, `Tᵢ` is Lusztig's `T''_{i,1}` (`IntegrableSl2.T` for
`nodeSl2` at `vᵢ`) and on `U` any algebra endomorphism with Lusztig's generator formulas
([Lus] 37.1.2, over `ℚ(v)`; [Jan] 8.13, for finite-dimensional modules in finite type). Here `k`
is any field and `v ∈ k` any element that is not a root of unity. -/
theorem nodeSl2_T_smul (u : QuantumGroup R v) (m : M) :
    (nodeSl2 R v M hv hM i).T (v ^ D.d i) (u • m) =
      Ti u • (nodeSl2 R v M hv hM i).T (v ^ D.d i) m := by
  refine induction_on R v (P := fun u ↦ ∀ m, (nodeSl2 R v M hv hM i).T (v ^ D.d i) (u • m) =
    Ti u • (nodeSl2 R v M hv hM i).T (v ^ D.d i) m) u ?_ ?_ ?_ ?_ ?_ ?_ m
  · intro c m
    rw [algebraMap_smul, map_smul, AlgHom.commutes, algebraMap_smul]
  · intro l m
    by_cases hl : l = i
    · subst hl
      exact nodeSl2_T_E_self hv hM H m
    · exact nodeSl2_T_E_ne hv hM H hl m
  · intro l m
    by_cases hl : l = i
    · subst hl
      exact nodeSl2_T_F_self hv hM H m
    · exact nodeSl2_T_F_ne hv hM H hl m
  · intro μ m
    rw [H.map_K]
    exact nodeSl2_T_K hv hM i _ μ m
  · intro x y hx hy m
    rw [add_smul, map_add, hx, hy, map_add, add_smul]
  · intro x y hx hy m
    rw [mul_smul, hx, hy, map_mul, mul_smul]

end Compat

end LieLean.QuantumGroup
