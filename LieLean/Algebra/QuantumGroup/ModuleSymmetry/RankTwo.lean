/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Integrable
import LieLean.Algebra.QuantumGroup.BraidAction.GeneralArtin
import LieLean.Algebra.QuantumGroup.BraidAction.ThreeLocalArtin
import LieLean.Algebra.QuantumGroup.BraidAction.TripleEdgeRelation

/-!
# Braid relations for the symmetries of integrable modules

Let `M` be an integrable `U`-module, `v` not a root of unity, and let `Tᵢ` (`i ∈ I`) be Lusztig's
symmetries `T''_{i,1}` of `M` (`QuantumGroup.IntegrableSl2.T` for `QuantumGroup.nodeSl2`). For two
distinct nodes `i, j` with `aᵢⱼ aⱼᵢ ≤ 3` we prove the braid relation of length
`mᵢⱼ = 2, 3, 4, 6` for these operators on `M`, in arbitrary ambient rank and with no condition on
the other nodes (`QuantumGroup.nodeSl2_T_comm`, `nodeSl2_T_braid_three`, `nodeSl2_T_braid_four`,
`nodeSl2_T_braid_six`).

The argument is by conjugation (our own; Lusztig, 39.4, instead uses complete reducibility and
quantum Verma identities). Write the relation as `Tₐ W = W T_b`, where `W` is the common word of
length `mᵢⱼ - 1` and `a, b ∈ {i, j}`. By `QuantumGroup.nodeSl2_T_smul`, the operator `W` on `M`
satisfies `W(u m) = W(u) W(m)` with `W(u)` the corresponding composite of the automorphisms of `U`,
and in rank two `W(E_b) = E_a`, `W(F_b) = F_a` (proved in `BraidAction/`); moreover `W` maps the
`⟨b, ·⟩`-grading to the `⟨a, ·⟩`-grading. So `W` is a morphism of `U_q(𝔰𝔩₂)`-modules from the
structure at `b` to the structure at `a`, and naturality of `T`
(`QuantumGroup.IntegrableSl2.map_T`) gives `W T_b = Tₐ W`.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 39.4.3.
-/

open Finset

namespace LieLean.QuantumGroup

namespace IntegrableSl2

variable {k : Type*} [Field k]

/-- Naturality of `T` (`IntegrableSl2.map_T`), allowing the parameters to be given by equal
expressions. -/
theorem map_T_of_eq {q q' : k} {M M' : Type*} [AddCommGroup M] [Module k M] [AddCommGroup M']
    [Module k M'] (V : IntegrableSl2 q M) (V' : IntegrableSl2 q' M') (hq : q = q')
    (f : M →ₗ[k] M') (hE : ∀ m, f (V.E m) = V'.E (f m)) (hF : ∀ m, f (V.F m) = V'.F (f m))
    (hwt : ∀ n, ∀ m ∈ V.wt n, f m ∈ V'.wt n) {t t' : k} (ht : t = t') (m : M) :
    f (V.T t m) = V'.T t' (f m) := by
  subst hq ht
  exact V.map_T V' f hE hF hwt t m

end IntegrableSl2

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]

section Conj

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M)

/-- `Tₗ` maps `M^Λ` to `M^{Λ ∘ sₗ}`. -/
lemma nodeSl2_T_mem_weightSpace_comp (l : I) (t : k) {Λ : Y →+ ℤ} {m : M}
    (hm : m ∈ weightSpace R v M Λ) :
    (nodeSl2 R v M hv hM l).T t m ∈ weightSpace R v M (Λ.comp (reflY R l)) := by
  have := nodeSl2_T_mem_weightSpace hv hM l t hm
  convert this using 2
  ext μ
  simp only [AddMonoidHom.comp_apply, reflY_apply, map_sub, map_zsmul, smul_eq_mul,
    AddMonoidHom.sub_apply, AddMonoidHom.smul_apply]
  ring

omit [NeZero v] in
/-- An operator mapping each `M^Λ` to `M^{Λ ∘ φ}`, where `φ(b) = a` on coroots, maps the
`⟨a, ·⟩`-grading to the `⟨b, ·⟩`-grading. -/
lemma mem_nodeWt_of_comp {a b : I} (Wm : Module.End k M) (φ : Y →+ Y)
    (hW : ∀ Λ, ∀ m ∈ weightSpace R v M Λ, Wm m ∈ weightSpace R v M (Λ.comp φ))
    (hφ : φ (R.coroot b) = R.coroot a) {n : ℤ} {m : M} (hm : m ∈ nodeWt R v M a n) :
    Wm m ∈ nodeWt R v M b n := by
  refine nodeWt_induction (P := fun m ↦ Wm m ∈ nodeWt R v M b n) hm (by simp)
    (fun x y hx hy ↦ by rw [map_add]; exact add_mem hx hy) fun Λ hΛ x hx ↦ ?_
  have := mem_nodeWt_of_mem (i := b) (hW Λ x hx)
  rwa [AddMonoidHom.comp_apply, hφ, hΛ] at this

/-- **Conjugation of the symmetries**: an operator `W` on `M` with `W(u m) = W(u) W(m)` for an
algebra endomorphism `W` of `U` with `W(E_b) = E_a`, `W(F_b) = F_a`, mapping the `⟨b, ·⟩`-grading
to the `⟨a, ·⟩`-grading, satisfies `W T_b = Tₐ W` (if `d_a = d_b`). -/
theorem nodeSl2_T_conj {a b : I} (Wm : Module.End k M)
    (W : QuantumGroup R v →ₐ[k] QuantumGroup R v) (hW : ∀ (u : QuantumGroup R v) m,
      Wm (u • m) = W u • Wm m) (hE : W (E R v b) = E R v a) (hF : W (F R v b) = F R v a)
    (hwt : ∀ n, ∀ m ∈ nodeWt R v M b n, Wm m ∈ nodeWt R v M a n) (hd : D.d b = D.d a)
    (m : M) :
    Wm ((nodeSl2 R v M hv hM b).T (v ^ D.d b) m) =
      (nodeSl2 R v M hv hM a).T (v ^ D.d a) (Wm m) :=
  IntegrableSl2.map_T_of_eq _ _ (by rw [hd]) Wm
    (fun m ↦ by change Wm (E R v b • m) = E R v a • Wm m; rw [hW, hE])
    (fun m ↦ by change Wm (F R v b • m) = F R v a • Wm m; rw [hW, hF])
    hwt (by rw [hd]) m

end Conj

variable (R v M) in
/-- Lusztig's symmetry `Tₗ = T''_{l,1}` of an integrable module `M`. -/
noncomputable abbrev nodeT [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
    (hM : IsIntegrable R v M) (l : I) : Module.End k M :=
  (nodeSl2 R v M hv hM l).T (v ^ D.d l)

section Relations

variable [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M) {i j : I}
  {Ti Tj : QuantumGroup R v →ₐ[k] QuantumGroup R v}
  (Hi : HasBraidGeneratorImages i Ti) (Hj : HasBraidGeneratorImages j Tj) (hij : i ≠ j)

include Hi Hj hij

omit Hi in
/-- **Length two**: if `aᵢⱼ = 0`, then `Tᵢ Tⱼ = Tⱼ Tᵢ` on `M`. -/
theorem nodeSl2_T_comm (h0 : D.cartanMatrix i j = 0) (m : M) :
    nodeT R v M hv hM i (nodeT R v M hv hM j m) =
      nodeT R v M hv hM j (nodeT R v M hv hM i m) := by
  have h0' : D.cartanMatrix j i = 0 := (D.isGeneralizedCartan_cartanMatrix.zero_comm i j).1 h0
  refine (nodeSl2_T_conj hv hM (nodeT R v M hv hM j) Tj
    (fun u m ↦ nodeSl2_T_smul hv hM Hj u m) ?_ ?_ ?_ rfl m).symm
  · rw [Hj.map_E, ite_eq_right hij, braidEj_eq_of_cartanMatrix_eq_zero h0']
  · rw [Hj.map_F, ite_eq_right hij, braidFj_eq_of_cartanMatrix_eq_zero h0']
  · intro n m hm
    refine mem_nodeWt_of_comp (nodeT R v M hv hM j) (reflY R j)
      (fun Λ m hm ↦ nodeSl2_T_mem_weightSpace_comp hv hM j _ hm) ?_ hm
    simp [reflY_apply, R.root_coroot, h0]

/-- **Length three**: if `aᵢⱼ = aⱼᵢ = -1`, then `Tᵢ Tⱼ Tᵢ = Tⱼ Tᵢ Tⱼ` on `M`. -/
theorem nodeSl2_T_braid_three (h : D.cartanMatrix i j = -1) (h' : D.cartanMatrix j i = -1)
    (m : M) :
    nodeT R v M hv hM i (nodeT R v M hv hM j (nodeT R v M hv hM i m)) =
      nodeT R v M hv hM j (nodeT R v M hv hM i (nodeT R v M hv hM j m)) := by
  have hqi := (shortNode_braidGeneric_of_not_root (D := D) hv i).sub_ne
  refine nodeSl2_T_conj hv hM (nodeT R v M hv hM i * nodeT R v M hv hM j) (Ti.comp Tj)
    (fun u m ↦ ?_) (Hi.three_double_E Hj hij h h' hqi) (Hi.three_double_F Hj hij h h' hqi) ?_
    (D.d_eq_of_simply_laced_edge h h') m
  · simp only [Module.End.mul_apply, AlgHom.comp_apply]
    rw [nodeSl2_T_smul hv hM Hj, nodeSl2_T_smul hv hM Hi]
  · intro n m hm
    refine mem_nodeWt_of_comp _ ((reflY R j).comp (reflY R i)) (fun Λ m hm ↦ ?_) ?_ hm
    · exact nodeSl2_T_mem_weightSpace_comp hv hM i _
        (nodeSl2_T_mem_weightSpace_comp hv hM j _ hm)
    · simp only [AddMonoidHom.comp_apply, reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h',
        D.cartanMatrix_self]
      module

/-- **Length four**: if `aᵢⱼ = -2`, `aⱼᵢ = -1`, then `Tᵢ Tⱼ Tᵢ Tⱼ = Tⱼ Tᵢ Tⱼ Tᵢ` on `M`. -/
theorem nodeSl2_T_braid_four (h : D.cartanMatrix i j = -2) (h' : D.cartanMatrix j i = -1)
    (m : M) :
    nodeT R v M hv hM i (nodeT R v M hv hM j (nodeT R v M hv hM i (nodeT R v M hv hM j m))) =
      nodeT R v M hv hM j (nodeT R v M hv hM i
        (nodeT R v M hv hM j (nodeT R v M hv hM i m))) := by
  have hS (l : I) := braidSerreGeneric_of_not_root (D := D) hv l
  have hq (l : I) := (shortNode_braidGeneric_of_not_root (D := D) hv l).sub_ne
  have hg (l : I) := braidGeneric_of_braidSerreGeneric (hq l) (hS l)
  have hT (l : I) := transformedSerre_of_braidSerreGeneric (R := R) (hq l) (hS l)
  have hsi := sum_ne_zero_of_qFactorial_three (pow_ne_zero (D.d i) (NeZero.ne v))
    (LusztigF.qFactorial_ne_zero_of_not_root (NeZero.ne v) hv i 3)
  have ei := (braidHom_hasBraidGeneratorImages (hg i) (hT i)).unique Hi
  have ej := (braidHom_hasBraidGeneratorImages (hg j) (hT j)).unique Hj
  refine (nodeSl2_T_conj hv hM (nodeT R v M hv hM j * nodeT R v M hv hM i *
    nodeT R v M hv hM j) (Tj.comp (Ti.comp Tj)) (fun u m ↦ ?_) ?_ ?_ ?_ rfl m).symm
  · simp only [Module.End.mul_apply, AlgHom.comp_apply]
    rw [nodeSl2_T_smul hv hM Hj, nodeSl2_T_smul hv hM Hi, nodeSl2_T_smul hv hM Hj]
  · simp only [AlgHom.comp_apply, ← ei, ← ej]
    exact braidHom_double_triple_Ei (hg i) (hT i) (hg j) (hT j) hij h h' hsi
  · simp only [AlgHom.comp_apply, ← ei, ← ej]
    exact braidHom_double_triple_Fi (hg i) (hT i) (hg j) (hT j) hij h h' hsi
  · intro n m hm
    refine mem_nodeWt_of_comp _ (((reflY R j).comp (reflY R i)).comp (reflY R j))
      (fun Λ m hm ↦ ?_) ?_ hm
    · exact nodeSl2_T_mem_weightSpace_comp hv hM j _ (nodeSl2_T_mem_weightSpace_comp hv hM i _
        (nodeSl2_T_mem_weightSpace_comp hv hM j _ hm))
    · simp only [AddMonoidHom.comp_apply, reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h',
        D.cartanMatrix_self]
      module

/-- **Length six**: if `aᵢⱼ = -3`, `aⱼᵢ = -1`, then `(Tᵢ Tⱼ)³ = (Tⱼ Tᵢ)³` on `M`. -/
theorem nodeSl2_T_braid_six (h : D.cartanMatrix i j = -3) (h' : D.cartanMatrix j i = -1)
    (m : M) :
    nodeT R v M hv hM i (nodeT R v M hv hM j (nodeT R v M hv hM i (nodeT R v M hv hM j
      (nodeT R v M hv hM i (nodeT R v M hv hM j m))))) =
      nodeT R v M hv hM j (nodeT R v M hv hM i (nodeT R v M hv hM j (nodeT R v M hv hM i
        (nodeT R v M hv hM j (nodeT R v M hv hM i m))))) := by
  have hq := (shortNode_braidGeneric_of_not_root (D := D) hv i).sub_ne
  have h3 := LusztigF.qFactorial_ne_zero_of_not_root (D := D) (NeZero.ne v) hv i 3
  refine (nodeSl2_T_conj hv hM (nodeT R v M hv hM j * nodeT R v M hv hM i *
    nodeT R v M hv hM j * nodeT R v M hv hM i * nodeT R v M hv hM j)
    (Tj.comp (Ti.comp (Tj.comp (Ti.comp Tj)))) (fun u m ↦ ?_) ?_ ?_ ?_ rfl m).symm
  · simp only [Module.End.mul_apply, AlgHom.comp_apply]
    rw [nodeSl2_T_smul hv hM Hj, nodeSl2_T_smul hv hM Hi, nodeSl2_T_smul hv hM Hj,
      nodeSl2_T_smul hv hM Hi, nodeSl2_T_smul hv hM Hj]
  · simp only [AlgHom.comp_apply]
    exact tripleSix_Ei Hi Hj hij h h' hq h3
  · simp only [AlgHom.comp_apply]
    exact tripleSix_Fi Hi Hj hij h h' hq h3
  · intro n m hm
    refine mem_nodeWt_of_comp _ (((((reflY R j).comp (reflY R i)).comp (reflY R j)).comp
      (reflY R i)).comp (reflY R j)) (fun Λ m hm ↦ ?_) ?_ hm
    · exact nodeSl2_T_mem_weightSpace_comp hv hM j _ (nodeSl2_T_mem_weightSpace_comp hv hM i _
        (nodeSl2_T_mem_weightSpace_comp hv hM j _ (nodeSl2_T_mem_weightSpace_comp hv hM i _
          (nodeSl2_T_mem_weightSpace_comp hv hM j _ hm))))
    · simp only [AddMonoidHom.comp_apply, reflY_apply, map_sub, map_zsmul, R.root_coroot, h, h',
        D.cartanMatrix_self]
      module

end Relations

end LieLean.QuantumGroup
