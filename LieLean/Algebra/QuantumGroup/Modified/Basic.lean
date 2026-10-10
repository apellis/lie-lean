/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.DividedPowers
import LieLean.Algebra.QuantumGroup.PBW.RootVectorWeights

/-!
# The modified quantum group `U̇`

Lusztig's modified form `U̇ = ⊕_{λ', λ''} ₗU_λ''` of `U` ([Lus] 23.1.1), an algebra without unit
with orthogonal idempotents `1_λ` (`λ ∈ X = Hom(Y, ℤ)`).

We use the decomposition of `U` by the weights of conjugation by the torus
(`adWeightSpace R v χ`: `K_μ u = v^{χ(μ)} u K_μ`), and set
`ₗU_λ'' = U_{λ'-λ''} / N(λ', λ'')`, where `N(λ', λ'')` is spanned by the
`(K_μ - v^{⟨μ,λ'⟩}) u` and `u (K_μ - v^{⟨μ,λ''⟩})` with `u ∈ U_{λ'-λ''}`. Lusztig defines
`ₗU_λ''` as the quotient of all of `U` by `Σ (K_μ - v^{⟨μ,λ'⟩}) U + Σ U (K_μ - v^{⟨μ,λ''⟩})` and
observes that only the summand `U(λ' - λ'')` survives ([Lus] 23.1.2); working with the homogeneous
piece from the start makes the product `π(t) π(s) = π(ts)` ([Lus] 23.1.1) well defined without
projections.

## Main definitions and results

* `QuantumGroup.Modified R v`: the algebra `U̇`, a non-unital `k`-algebra;
  `Modified.elt λ' λ'' u hu` is the image `π_{λ',λ''}(u)` of `u ∈ U_{λ'-λ''}`, `Modified.one λ`
  is `1_λ`; `Modified.elt_mul_elt` (`π(t) π(s) = π(ts)` for matching weights, `0` otherwise),
  `Modified.one_mul_one` (`1_λ 1_λ' = δ_{λλ'} 1_λ`).
* `Modified.map φ σ`: the automorphism of `U̇` induced by an algebra automorphism `φ` of `U` with
  `φ(K_μ) = K_{σ μ}`, with `Modified.map_comp`.
* `Modified.braid hv i`: Lusztig's `Tᵢ = T''_{i,1}` on `U̇` ([Lus] 41.1.1), with
  `braid_elt` (`Tᵢ(π_{λ',λ''}(u)) = π_{sᵢλ', sᵢλ''}(Tᵢ u)`), inverse `braidInv` (`T'_{i,-1}`), and
  the braid relations (`Modified.isBraidLiftable_braid`) and Artin group action
  (`Modified.braidArtinHom`) for every Cartan datum, `v ≠ 0` not a root of unity.

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1, 41.1.1.
-/

open LieLean Finset DirectSum

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

/-! ### Conjugation weights -/

section AdWeight

variable {R v} [NeZero v]

lemma mul_mem_adWeightSpace {χ χ' : Y →+ ℤ} {x y : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) (hy : y ∈ adWeightSpace R v χ') :
    x * y ∈ adWeightSpace R v (χ + χ') := fun μ ↦ by
  rw [← mul_assoc, hx μ, smul_mul_assoc, mul_assoc, hy μ, mul_smul_comm, smul_smul, ← mul_assoc,
    AddMonoidHom.add_apply, zpow_add₀ (NeZero.ne v)]

omit [NeZero v] in
lemma K_mem_adWeightSpace (μ : Y) : K R v μ ∈ adWeightSpace R v 0 := fun ν ↦ by
  rw [K_add, AddMonoidHom.zero_apply, zpow_zero, one_smul, K_add, add_comm]

omit [NeZero v] in
lemma algebraMap_mem_adWeightSpace (c : k) :
    algebraMap k (QuantumGroup R v) c ∈ adWeightSpace R v 0 := fun ν ↦ by
  rw [AddMonoidHom.zero_apply, zpow_zero, one_smul, Algebra.commutes]

omit [NeZero v] in
lemma one_mem_adWeightSpace : (1 : QuantumGroup R v) ∈ adWeightSpace R v 0 := by
  simpa using algebraMap_mem_adWeightSpace (R := R) (v := v) 1

lemma mul_K_of_mem_adWeightSpace {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) (μ : Y) :
    x * K R v μ = v ^ (-χ μ) • (K R v μ * x) := by
  rw [hx μ, smul_smul, ← zpow_add₀ (NeZero.ne v), neg_add_cancel, zpow_zero, one_smul]

end AdWeight

/-! ### The components `ₗU_λ''` -/

variable [NeZero v]

/-- The relations `N(λ', λ'')`: the span of `(K_μ - v^{⟨μ,λ'⟩}) u` and `u (K_μ - v^{⟨μ,λ''⟩})`,
`u ∈ U_{λ'-λ''}`. -/
def modRel (l₁ l₂ : Y →+ ℤ) : Submodule k (QuantumGroup R v) :=
  Submodule.span k
    ({x | ∃ μ u, u ∈ adWeightSpace R v (l₁ - l₂) ∧
        x = (K R v μ - algebraMap k _ (v ^ l₁ μ)) * u} ∪
     {x | ∃ μ u, u ∈ adWeightSpace R v (l₁ - l₂) ∧
        x = u * (K R v μ - algebraMap k _ (v ^ l₂ μ))})

variable {R v}

omit [NeZero v] in
lemma sub_mem_adWeightSpace_zero (μ : Y) (c : k) :
    K R v μ - algebraMap k (QuantumGroup R v) c ∈ adWeightSpace R v 0 :=
  sub_mem (K_mem_adWeightSpace μ) (algebraMap_mem_adWeightSpace c)

lemma modRel_le (l₁ l₂ : Y →+ ℤ) : modRel R v l₁ l₂ ≤ adWeightSpace R v (l₁ - l₂) := by
  refine Submodule.span_le.2 ?_
  rintro x (⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩)
  · simpa using mul_mem_adWeightSpace (sub_mem_adWeightSpace_zero μ (v ^ l₁ μ)) hu
  · simpa using mul_mem_adWeightSpace hu (sub_mem_adWeightSpace_zero μ (v ^ l₂ μ))

lemma mul_mem_modRel_left {l₁ l₂ l₃ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ modRel R v l₁ l₂) (hb : b ∈ adWeightSpace R v (l₂ - l₃)) :
    a * b ∈ modRel R v l₁ l₃ := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · refine Submodule.subset_span (Or.inl ⟨μ, u * b, ?_, by rw [mul_assoc]⟩)
      simpa using mul_mem_adWeightSpace hu hb
    · have hub : u * b ∈ adWeightSpace R v (l₁ - l₃) := by
        simpa using mul_mem_adWeightSpace hu hb
      have e : u * (K R v μ - algebraMap k _ (v ^ l₂ μ)) * b =
          v ^ ((l₂ - l₃) μ) • (u * b * (K R v μ - algebraMap k _ (v ^ l₃ μ))) := by
        have hc : v ^ ((l₂ - l₃) μ) * v ^ l₃ μ = v ^ l₂ μ := by
          rw [← zpow_add₀ (NeZero.ne v), AddMonoidHom.sub_apply, sub_add_cancel]
        have hKb := hb μ
        simp only [Algebra.algebraMap_eq_smul_one, mul_sub, sub_mul, mul_assoc, hKb,
          mul_smul_comm, smul_mul_assoc, mul_one, smul_sub, smul_smul, hc]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨μ, u * b, hub, rfl⟩))
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

lemma mul_mem_modRel_right {l₁ l₂ l₃ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ modRel R v l₂ l₃) :
    a * b ∈ modRel R v l₁ l₃ := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · have hau : a * u ∈ adWeightSpace R v (l₁ - l₃) := by
        simpa using mul_mem_adWeightSpace ha hu
      have e : a * ((K R v μ - algebraMap k _ (v ^ l₂ μ)) * u) =
          v ^ (-(l₁ - l₂) μ) • ((K R v μ - algebraMap k _ (v ^ l₁ μ)) * (a * u)) := by
        have hc : v ^ (-(l₁ - l₂) μ) * v ^ l₁ μ = v ^ l₂ μ := by
          rw [← zpow_add₀ (NeZero.ne v), AddMonoidHom.sub_apply]; ring_nf
        have haK := mul_K_of_mem_adWeightSpace ha μ
        simp only [Algebra.algebraMap_eq_smul_one, mul_sub, sub_mul, ← mul_assoc, haK,
          mul_smul_comm, smul_mul_assoc, one_mul, smul_sub, smul_smul, hc]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨μ, a * u, hau, rfl⟩))
    · refine Submodule.subset_span (Or.inr ⟨μ, a * u, ?_, by rw [mul_assoc]⟩)
      simpa using mul_mem_adWeightSpace ha hu
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-! ### The algebra `U̇` -/

variable (R v)

/-- The component `ₗU_λ'' = U_{λ'-λ''} / N(λ', λ'')` of `U̇` ([Lus] 23.1.1 (a)), for
`p = (λ', λ'')`. -/
def Modified.Comp (p : (Y →+ ℤ) × (Y →+ ℤ)) : Type _ :=
  adWeightSpace R v (p.1 - p.2) ⧸
    (modRel R v p.1 p.2).comap (adWeightSpace R v (p.1 - p.2)).subtype

instance (p : (Y →+ ℤ) × (Y →+ ℤ)) : AddCommGroup (Modified.Comp R v p) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (p : (Y →+ ℤ) × (Y →+ ℤ)) : Module k (Modified.Comp R v p) :=
  inferInstanceAs (Module k (_ ⧸ _))

/-- The projection `U_{λ'-λ''} → ₗU_λ''`. -/
def Modified.Comp.mk (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    adWeightSpace R v (p.1 - p.2) →ₗ[k] Modified.Comp R v p :=
  Submodule.mkQ _

omit [NeZero v] in
lemma Modified.Comp.mk_surjective (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    Function.Surjective (Modified.Comp.mk R v p) :=
  Submodule.mkQ_surjective _

omit [NeZero v] in
variable {R v} in
lemma Modified.Comp.mk_eq_zero {p : (Y →+ ℤ) × (Y →+ ℤ)} {x : adWeightSpace R v (p.1 - p.2)} :
    Modified.Comp.mk R v p x = 0 ↔ x.1 ∈ modRel R v p.1 p.2 :=
  Submodule.Quotient.mk_eq_zero _

/-- **Lusztig's modified quantum group** `U̇ = ⊕_{λ', λ''} ₗU_λ''` ([Lus] 23.1.1 (b)), an
associative algebra without unit (`v ≠ 0`). -/
abbrev Modified : Type _ := ⨁ p : (Y →+ ℤ) × (Y →+ ℤ), Modified.Comp R v p

namespace Modified

/-- A decidable equality on pairs of weights (classical), used for `DirectSum.lof`. -/
noncomputable abbrev decEqIdx : DecidableEq ((Y →+ ℤ) × (Y →+ ℤ)) := Classical.decEq _

attribute [local instance] decEqIdx

variable {R v}

/-- The product `U_{λ₁-λ₂} × U_{λ₂-λ₃} → U_{λ₁-λ₃}`. -/
def mulAux (l₁ l₂ l₃ : Y →+ ℤ) :
    adWeightSpace R v (l₁ - l₂) →ₗ[k] adWeightSpace R v (l₂ - l₃) →ₗ[k]
      adWeightSpace R v (l₁ - l₃) :=
  LinearMap.mk₂ k (fun a b ↦ ⟨a.1 * b.1, by simpa using mul_mem_adWeightSpace a.2 b.2⟩)
    (fun a a' b ↦ Subtype.ext (add_mul _ _ _)) (fun c a b ↦ Subtype.ext (smul_mul_assoc _ _ _))
    (fun a b b' ↦ Subtype.ext (mul_add _ _ _)) (fun c a b ↦ Subtype.ext (mul_smul_comm _ _ _))

lemma compMul_aux₁ (l₁ l₂ l₃ : Y →+ ℤ) :
    (modRel R v l₂ l₃).comap (adWeightSpace R v (l₂ - l₃)).subtype ≤
      LinearMap.ker ((mulAux (R := R) (v := v) l₁ l₂ l₃).compr₂ (Submodule.mkQ
        ((modRel R v l₁ l₃).comap (adWeightSpace R v (l₁ - l₃)).subtype))).flip := fun b hb ↦ by
  rw [LinearMap.mem_ker]
  ext a
  exact (Submodule.Quotient.mk_eq_zero _).2 (mul_mem_modRel_right a.2 hb)

lemma compMul_aux₂ (l₁ l₂ l₃ : Y →+ ℤ) :
    (modRel R v l₁ l₂).comap (adWeightSpace R v (l₁ - l₂)).subtype ≤
      LinearMap.ker (Submodule.liftQ _ _ (compMul_aux₁ (R := R) (v := v) l₁ l₂ l₃)).flip :=
  fun a ha ↦ by
    rw [LinearMap.mem_ker]
    ext b
    exact (Submodule.Quotient.mk_eq_zero _).2 (mul_mem_modRel_left ha b.2)

/-- The product `ₗ₁U_ₗ₂ × ₗ₂U_ₗ₃ → ₗ₁U_ₗ₃`, `π(t) π(s) = π(ts)`. -/
def compMul (l₁ l₂ l₃ : Y →+ ℤ) :
    Comp R v (l₁, l₂) →ₗ[k] Comp R v (l₂, l₃) →ₗ[k] Comp R v (l₁, l₃) :=
  Submodule.liftQ _ _ (compMul_aux₂ l₁ l₂ l₃)

lemma compMul_mk (l₁ l₂ l₃ : Y →+ ℤ) (a : adWeightSpace R v (l₁ - l₂))
    (b : adWeightSpace R v (l₂ - l₃)) :
    compMul l₁ l₂ l₃ (Comp.mk R v (l₁, l₂) a) (Comp.mk R v (l₂, l₃) b) =
      Comp.mk R v (l₁, l₃) (mulAux l₁ l₂ l₃ a b) :=
  rfl

open Classical in
/-- The product of two components, as a bilinear map into `U̇`. -/
def mulComp (p q : (Y →+ ℤ) × (Y →+ ℤ)) : Comp R v p →ₗ[k] Comp R v q →ₗ[k] Modified R v :=
  match p, q with
  | (l₁, l₂), (l₃, l₄) =>
    if h : l₂ = l₃ then by
      subst h; exact (compMul l₁ l₂ l₄).compr₂ (DirectSum.lof k _ (Comp R v) (l₁, l₄))
    else 0

lemma mulComp_self (l₁ l₂ l₄ : Y →+ ℤ) (x : Comp R v (l₁, l₂)) (y : Comp R v (l₂, l₄)) :
    mulComp (l₁, l₂) (l₂, l₄) x y =
      DirectSum.lof k _ (Comp R v) (l₁, l₄) (compMul l₁ l₂ l₄ x y) := by
  simp [mulComp, LinearMap.compr₂_apply]

lemma mulComp_of_ne {l₁ l₂ l₃ l₄ : Y →+ ℤ} (h : l₂ ≠ l₃) (x : Comp R v (l₁, l₂))
    (y : Comp R v (l₃, l₄)) : mulComp (l₁, l₂) (l₃, l₄) x y = 0 := by
  simp [mulComp, h]

variable (R v) in
/-- The multiplication of `U̇` as a bilinear map. -/
def mulBil : Modified R v →ₗ[k] Modified R v →ₗ[k] Modified R v :=
  DirectSum.toModule k _ _ fun p ↦ (DirectSum.toModule k _ _ fun q ↦ (mulComp p q).flip).flip

instance : Mul (Modified R v) := ⟨fun x y ↦ mulBil R v x y⟩

lemma mul_def (x y : Modified R v) : x * y = mulBil R v x y := rfl

lemma lof_mul_lof (p q : (Y →+ ℤ) × (Y →+ ℤ)) (x : Comp R v p) (y : Comp R v q) :
    (DirectSum.lof k _ (Comp R v) p x : Modified R v) * DirectSum.lof k _ (Comp R v) q y =
      mulComp p q x y := by
  rw [mul_def, mulBil, DirectSum.toModule_lof, LinearMap.flip_apply, DirectSum.toModule_lof,
    LinearMap.flip_apply]

/-- `π_{λ',λ''}(u)` for `u ∈ U_{λ'-λ''}`. -/
def elt (l₁ l₂ : Y →+ ℤ) (u : QuantumGroup R v) (hu : u ∈ adWeightSpace R v (l₁ - l₂)) :
    Modified R v :=
  DirectSum.lof k _ (Comp R v) (l₁, l₂) (Comp.mk R v (l₁, l₂) ⟨u, hu⟩)

/-- The idempotent `1_λ` ([Lus] 23.1.1 (c)). -/
def one (l : Y →+ ℤ) : Modified R v :=
  elt l l 1 (by rw [sub_self]; exact one_mem_adWeightSpace)

lemma elt_mul_elt (l₁ l₂ l₃ : Y →+ ℤ) {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ adWeightSpace R v (l₂ - l₃)) :
    elt l₁ l₂ a ha * elt l₂ l₃ b hb =
      elt l₁ l₃ (a * b) (by simpa using mul_mem_adWeightSpace ha hb) := by
  rw [elt, elt, lof_mul_lof, mulComp_self, compMul_mk]
  rfl

lemma elt_mul_elt_of_ne {l₁ l₂ l₃ l₄ : Y →+ ℤ} (h : l₂ ≠ l₃) {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ adWeightSpace R v (l₃ - l₄)) :
    elt l₁ l₂ a ha * elt l₃ l₄ b hb = 0 := by
  rw [elt, elt, lof_mul_lof, mulComp_of_ne h]

omit [NeZero v] in
lemma elt_add (l₁ l₂ : Y →+ ℤ) {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ adWeightSpace R v (l₁ - l₂)) :
    elt l₁ l₂ (a + b) (add_mem ha hb) = elt l₁ l₂ a ha + elt l₁ l₂ b hb := by
  rw [elt, elt, elt, ← map_add, ← map_add]
  rfl

omit [NeZero v] in
lemma elt_smul (l₁ l₂ : Y →+ ℤ) (c : k) {a : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) :
    elt l₁ l₂ (c • a) (Submodule.smul_mem _ c ha) = c • elt l₁ l₂ a ha := by
  rw [elt, elt, ← map_smul, ← map_smul]
  rfl

omit [NeZero v] in
lemma elt_congr {l₁ l₂ : Y →+ ℤ} {a b : QuantumGroup R v} (h : a = b)
    (ha : a ∈ adWeightSpace R v (l₁ - l₂)) (hb : b ∈ adWeightSpace R v (l₁ - l₂)) :
    elt l₁ l₂ a ha = elt l₁ l₂ b hb := by
  subst h; rfl

omit [NeZero v] in
lemma elt_eq_zero {l₁ l₂ : Y →+ ℤ} {a : QuantumGroup R v} (ha : a ∈ adWeightSpace R v (l₁ - l₂))
    (h : a ∈ modRel R v l₁ l₂) : elt l₁ l₂ a ha = 0 := by
  rw [elt, (Comp.mk_eq_zero (p := (l₁, l₂)) (x := ⟨a, ha⟩)).2 h, map_zero]

/-- `K_μ π_{λ',λ''}(u) = v^{⟨μ,λ'⟩} π_{λ',λ''}(u)`. -/
lemma elt_K_mul (l₁ l₂ : Y →+ ℤ) (μ : Y) {a : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂))
    (hKa : K R v μ * a ∈ adWeightSpace R v (l₁ - l₂)) :
    elt l₁ l₂ (K R v μ * a) hKa = v ^ l₁ μ • elt l₁ l₂ a ha := by
  have hm : (K R v μ - algebraMap k _ (v ^ l₁ μ)) * a ∈ modRel R v l₁ l₂ :=
    Submodule.subset_span (Or.inl ⟨μ, a, ha, rfl⟩)
  have h : K R v μ * a = (K R v μ - algebraMap k _ (v ^ l₁ μ)) * a + v ^ l₁ μ • a := by
    rw [sub_mul, Algebra.smul_def]; abel
  rw [elt_congr h _ (add_mem (modRel_le _ _ hm) (Submodule.smul_mem _ _ ha)),
    elt_add _ _ (modRel_le _ _ hm) (Submodule.smul_mem _ _ ha), elt_eq_zero _ hm, zero_add,
    elt_smul]

/-- `π_{λ',λ''}(u) K_μ = v^{⟨μ,λ''⟩} π_{λ',λ''}(u)`. -/
lemma elt_mul_K (l₁ l₂ : Y →+ ℤ) (μ : Y) {a : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v (l₁ - l₂))
    (haK : a * K R v μ ∈ adWeightSpace R v (l₁ - l₂)) :
    elt l₁ l₂ (a * K R v μ) haK = v ^ l₂ μ • elt l₁ l₂ a ha := by
  have hm : a * (K R v μ - algebraMap k _ (v ^ l₂ μ)) ∈ modRel R v l₁ l₂ :=
    Submodule.subset_span (Or.inr ⟨μ, a, ha, rfl⟩)
  have h : a * K R v μ = a * (K R v μ - algebraMap k _ (v ^ l₂ μ)) + v ^ l₂ μ • a := by
    rw [mul_sub, ← Algebra.commutes, Algebra.smul_def]; abel
  rw [elt_congr h _ (add_mem (modRel_le _ _ hm) (Submodule.smul_mem _ _ ha)),
    elt_add _ _ (modRel_le _ _ hm) (Submodule.smul_mem _ _ ha), elt_eq_zero _ hm, zero_add,
    elt_smul]

omit [NeZero v] in
lemma elt_index {l₁ l₂ l₁' l₂' : Y →+ ℤ} (h₁ : l₁ = l₁') (h₂ : l₂ = l₂')
    {a b : QuantumGroup R v} (hab : a = b) (ha : a ∈ adWeightSpace R v (l₁ - l₂))
    (hb : b ∈ adWeightSpace R v (l₁' - l₂')) : elt l₁ l₂ a ha = elt l₁' l₂' b hb := by
  subst h₁ h₂ hab; rfl

omit [NeZero v] in
/-- Every element of `U̇` is a finite sum of elements `π_{λ',λ''}(u)`. -/
theorem induction_on {P : Modified R v → Prop} (x : Modified R v) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (helt : ∀ l₁ l₂ u (hu : u ∈ adWeightSpace R v (l₁ - l₂)), P (elt l₁ l₂ u hu)) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | of p y =>
    obtain ⟨⟨u, hu⟩, rfl⟩ := Comp.mk_surjective R v p y
    simpa [elt, DirectSum.lof_eq_of] using helt p.1 p.2 u hu
  | add x y hx hy => exact hadd x y hx hy

lemma add_mul' (x y z : Modified R v) : (x + y) * z = x * z + y * z := by
  simp only [mul_def, map_add, LinearMap.add_apply]

lemma mul_add' (x y z : Modified R v) : x * (y + z) = x * y + x * z := by
  simp only [mul_def, map_add]

lemma zero_mul' (x : Modified R v) : 0 * x = 0 := by
  simp only [mul_def, map_zero, LinearMap.zero_apply]

lemma mul_zero' (x : Modified R v) : x * 0 = 0 := by
  simp only [mul_def, map_zero]

lemma smul_mul' (c : k) (x y : Modified R v) : (c • x) * y = c • (x * y) := by
  simp only [mul_def, map_smul, LinearMap.smul_apply]

lemma mul_smul' (c : k) (x y : Modified R v) : x * (c • y) = c • (x * y) := by
  simp only [mul_def, map_smul]

lemma mul_assoc' (x y z : Modified R v) : x * y * z = x * (y * z) := by
  induction x using induction_on with
  | h0 => simp only [zero_mul']
  | hadd x x' hx hx' => rw [add_mul', add_mul', hx, hx', add_mul']
  | helt a b u hu =>
  induction y using induction_on with
  | h0 => simp only [mul_zero', zero_mul']
  | hadd y y' hy hy' => rw [mul_add', add_mul', hy, hy', add_mul', mul_add']
  | helt c d w hw =>
  induction z using induction_on with
  | h0 => simp only [mul_zero']
  | hadd z z' hz hz' => rw [mul_add', hz, hz', mul_add', mul_add']
  | helt e f t ht =>
  by_cases hbc : b = c
  · subst hbc
    by_cases hde : d = e
    · subst hde
      rw [elt_mul_elt, elt_mul_elt, elt_mul_elt, elt_mul_elt]
      exact elt_congr (mul_assoc _ _ _) _ _
    · rw [elt_mul_elt, elt_mul_elt_of_ne hde, elt_mul_elt_of_ne hde, mul_zero']
  · rw [elt_mul_elt_of_ne hbc, zero_mul']
    by_cases hde : d = e
    · subst hde
      rw [elt_mul_elt, elt_mul_elt_of_ne hbc]
    · rw [elt_mul_elt_of_ne hde, mul_zero']

instance : NonUnitalRing (Modified R v) :=
  { (inferInstance : AddCommGroup (Modified R v)) with
    mul := (· * ·)
    left_distrib := mul_add'
    right_distrib := add_mul'
    zero_mul := zero_mul'
    mul_zero := mul_zero'
    mul_assoc := mul_assoc' }

instance : IsScalarTower k (Modified R v) (Modified R v) := ⟨fun c x y ↦ smul_mul' c x y⟩

instance : SMulCommClass k (Modified R v) (Modified R v) :=
  ⟨fun c x y ↦ (mul_smul' c x y).symm⟩

lemma one_mul_elt (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (l₁ - l₂)) : one l₁ * elt l₁ l₂ u hu = elt l₁ l₂ u hu := by
  rw [one, elt_mul_elt]
  exact elt_congr (one_mul u) _ _

lemma elt_mul_one (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (l₁ - l₂)) : elt l₁ l₂ u hu * one l₂ = elt l₁ l₂ u hu := by
  rw [one, elt_mul_elt]
  exact elt_congr (mul_one u) _ _

/-- `1_λ 1_λ = 1_λ` ([Lus] 23.1.1 (c)). -/
lemma one_mul_one_self (l : Y →+ ℤ) : one (R := R) (v := v) l * one l = one l :=
  elt_mul_one _ _ _

/-- `1_λ 1_λ' = 0` for `λ ≠ λ'` ([Lus] 23.1.1 (c)). -/
lemma one_mul_one_of_ne {l l' : Y →+ ℤ} (h : l ≠ l') : one (R := R) (v := v) l * one l' = 0 :=
  elt_mul_elt_of_ne h _ _

/-! ### Automorphisms induced from `U` -/

omit [DecidableEq I] [NeZero v] in
lemma autY_apply_inv (g : Y ≃ₗ[ℤ] Y) (μ : Y) : g (g⁻¹ μ) = μ := g.apply_symm_apply μ

omit [DecidableEq I] [NeZero v] in
lemma autY_inv_apply (g : Y ≃ₗ[ℤ] Y) (μ : Y) : g⁻¹ (g μ) = μ := g.symm_apply_apply μ

omit [DecidableEq I] [NeZero v] in
lemma autY_mul_apply (g h : Y ≃ₗ[ℤ] Y) (μ : Y) : (g * h) μ = g (h μ) := rfl

variable (R v) in
/-- Pairs `(φ, σ)` of an algebra automorphism `φ` of `U` and an automorphism `σ` of `Y` with
`φ(K_μ) = K_{σ μ}`. -/
def torusAut : Subgroup ((QuantumGroup R v ≃ₐ[k] QuantumGroup R v) × (Y ≃ₗ[ℤ] Y)) where
  carrier := {g | ∀ μ, g.1 (K R v μ) = K R v (g.2 μ)}
  mul_mem' {g h} hg hh μ := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, AlgEquiv.mul_apply,
      autY_mul_apply] at *
    rw [hh μ, hg]
  one_mem' μ := rfl
  inv_mem' {g} hg μ := by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, AlgEquiv.aut_inv] at *
    rw [AlgEquiv.symm_apply_eq, hg, autY_apply_inv]

/-- The action of `(φ, σ)` on weights: `λ ↦ λ ∘ σ⁻¹`. -/
def wt (g : torusAut R v) (l : Y →+ ℤ) : Y →+ ℤ :=
  l.comp (g.1.2⁻¹ : Y ≃ₗ[ℤ] Y).toLinearMap.toAddMonoidHom

omit [NeZero v] in
@[simp] lemma wt_apply (g : torusAut R v) (l : Y →+ ℤ) (μ : Y) : wt g l μ = l (g.1.2⁻¹ μ) := rfl

omit [NeZero v] in
lemma wt_injective (g : torusAut R v) : Function.Injective (wt g) := fun l l' h ↦ by
  ext μ
  have := DFunLike.congr_fun h (g.1.2 μ)
  simpa [autY_inv_apply] using this

omit [NeZero v] in
lemma wt_mul (g h : torusAut R v) (l : Y →+ ℤ) : wt g (wt h l) = wt (g * h) l := by
  ext μ
  simp only [wt_apply, Subgroup.coe_mul, Prod.snd_mul, mul_inv_rev, autY_mul_apply]

omit [NeZero v] in
lemma wt_one (l : Y →+ ℤ) : wt (1 : torusAut R v) l = l := by
  ext μ; rfl

omit [NeZero v] in
lemma map_mem_adWeightSpace (g : torusAut R v) {χ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v χ) : g.1.1 x ∈ adWeightSpace R v (wt g χ) := fun μ ↦ by
  have h := congrArg g.1.1 (hx (g.1.2⁻¹ μ))
  rw [_root_.map_mul, map_smul, _root_.map_mul, g.2, autY_apply_inv] at h
  exact h

omit [NeZero v] in
lemma map_mem_adWeightSpace_sub (g : torusAut R v) {l₁ l₂ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ adWeightSpace R v (l₁ - l₂)) :
    g.1.1 x ∈ adWeightSpace R v (wt g l₁ - wt g l₂) :=
  map_mem_adWeightSpace g hx

omit [NeZero v] in
lemma map_mem_modRel (g : torusAut R v) {l₁ l₂ : Y →+ ℤ} {x : QuantumGroup R v}
    (hx : x ∈ modRel R v l₁ l₂) : g.1.1 x ∈ modRel R v (wt g l₁) (wt g l₂) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨μ, u, hu, rfl⟩ | ⟨μ, u, hu, rfl⟩
    · refine Submodule.subset_span (Or.inl ⟨g.1.2 μ, g.1.1 u, map_mem_adWeightSpace_sub g hu, ?_⟩)
      rw [map_mul, map_sub, g.2, AlgEquiv.commutes, wt_apply, autY_inv_apply]
    · refine Submodule.subset_span (Or.inr ⟨g.1.2 μ, g.1.1 u, map_mem_adWeightSpace_sub g hu, ?_⟩)
      rw [map_mul, map_sub, g.2, AlgEquiv.commutes, wt_apply, autY_inv_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- The map `ₗU_λ'' → _{σλ'}U_{σλ''}` induced by `(φ, σ)`. -/
def mapComp (g : torusAut R v) (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    Comp R v p →ₗ[k] Comp R v (wt g p.1, wt g p.2) :=
  Submodule.mapQ _ _ (g.1.1.toLinearMap.restrict fun _ hx ↦ map_mem_adWeightSpace_sub g hx)
    (fun _ hx ↦ map_mem_modRel g hx)

/-- The linear map `U̇ → U̇` induced by `(φ, σ)`, `π_{λ',λ''}(u) ↦ π_{σλ',σλ''}(φ u)`. -/
def map (g : torusAut R v) : Modified R v →ₗ[k] Modified R v :=
  DirectSum.toModule k _ _ fun p ↦ (DirectSum.lof k _ (Comp R v) (wt g p.1, wt g p.2)).comp
    (mapComp g p)

omit [NeZero v] in
lemma map_elt (g : torusAut R v) (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (l₁ - l₂)) :
    map g (elt l₁ l₂ u hu) =
      elt (wt g l₁) (wt g l₂) (g.1.1 u) (map_mem_adWeightSpace_sub g hu) := by
  rw [map, elt, DirectSum.toModule_lof]
  rfl

lemma map_mul (g : torusAut R v) (x y : Modified R v) : map g (x * y) = map g x * map g y := by
  induction x using induction_on with
  | h0 => simp only [zero_mul, map_zero]
  | hadd x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | helt a b u hu =>
  induction y using induction_on with
  | h0 => simp only [mul_zero, map_zero]
  | hadd y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | helt c d w hw =>
  by_cases hbc : b = c
  · subst hbc
    rw [elt_mul_elt, map_elt, map_elt, map_elt, elt_mul_elt]
    exact elt_congr (_root_.map_mul _ _ _) _ _
  · rw [elt_mul_elt_of_ne hbc, map_zero, map_elt, map_elt,
      elt_mul_elt_of_ne fun h ↦ hbc (wt_injective g h)]

omit [NeZero v] in
lemma map_map (g h : torusAut R v) (x : Modified R v) : map g (map h x) = map (g * h) x := by
  induction x using induction_on with
  | h0 => simp only [map_zero]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | helt a b u hu =>
    rw [map_elt, map_elt, map_elt]
    exact elt_index (wt_mul g h a) (wt_mul g h b) rfl _ _

omit [NeZero v] in
lemma map_one (x : Modified R v) : map (1 : torusAut R v) x = x := by
  induction x using induction_on with
  | h0 => simp only [map_zero]
  | hadd x y hx hy => rw [map_add, hx, hy]
  | helt a b u hu =>
    rw [map_elt]
    exact elt_index (wt_one a) (wt_one b) rfl _ _

variable (R v) in
/-- `(φ, σ) ↦ ` the induced automorphism of `U̇`, a group homomorphism. -/
def mapHom : torusAut R v →* (Modified R v ≃ₗ[k] Modified R v) where
  toFun g := LinearEquiv.ofLinearMap (map g) (map g⁻¹)
    (LinearMap.ext fun x ↦ by simp [map_map, Modified.map_one])
    (LinearMap.ext fun x ↦ by simp [map_map, Modified.map_one])
  map_one' := LinearEquiv.ext fun x ↦ map_one x
  map_mul' g h := LinearEquiv.ext fun x ↦ (map_map g h x).symm

omit [NeZero v] in
@[simp] lemma mapHom_apply (g : torusAut R v) (x : Modified R v) : mapHom R v g x = map g x :=
  rfl

lemma mapHom_mul (g : torusAut R v) (x y : Modified R v) :
    mapHom R v g (x * y) = mapHom R v g x * mapHom R v g y :=
  map_mul g x y

/-! ### Lusztig's `Tᵢ` on `U̇` -/

section Braid

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

include hv in
lemma K_injective {μ ν : Y} (h : K R v μ = K R v ν) : μ = ν := by
  have h' : zeroHom R v (AddMonoidAlgebra.single μ 1) =
      zeroHom R v (AddMonoidAlgebra.single ν 1) := by
    simpa [zeroHom, AddMonoidAlgebra.lift_single] using h
  exact (AddMonoidAlgebra.single_left_inj one_ne_zero).1 (zeroHom_injective R v hv h')

include hv in
/-- An element of `torusAut` is determined by its automorphism of `U`. -/
lemma torusAut_ext {g h : torusAut R v} (h₁ : g.1.1 = h.1.1) : g = h :=
  Subtype.ext (Prod.ext h₁ (LinearEquiv.ext fun μ ↦ K_injective hv (by
    rw [← g.2 μ, ← h.2 μ, h₁])))

variable (R) in
/-- The simple reflection `sᵢ` of `Y` as a `ℤ`-linear automorphism. -/
def reflAut (i : I) : Y ≃ₗ[ℤ] Y :=
  LinearEquiv.ofInvolutive (reflY R i).toIntLinearMap fun μ ↦ reflY_reflY (R := R) i μ

omit [DecidableEq I] [NeZero v] in
@[simp] lemma reflAut_apply (i : I) (μ : Y) : reflAut R i μ = reflY R i μ := rfl

omit [DecidableEq I] [NeZero v] in
@[simp] lemma reflAut_inv_apply (i : I) (μ : Y) : (reflAut R i)⁻¹ μ = reflY R i μ := by
  rw [← reflY_reflY (R := R) i ((reflAut R i)⁻¹ μ)]
  exact congrArg (reflY R i) (autY_apply_inv (reflAut R i) μ)

/-- `(Tᵢ, sᵢ) ∈ torusAut`, `Tᵢ = T''_{i,1}`. -/
def braidAut (i : I) : torusAut R v :=
  ⟨(braidEquivOfNotRoot R hv i, reflAut R i), fun μ ↦
    (braidEquivOfNotRoot_hasImages hv R i).map_K μ⟩

lemma wt_braidAut (i : I) (l : Y →+ ℤ) : wt (braidAut (R := R) hv i) l = l.comp (reflY R i) := by
  ext μ; simp [braidAut]

lemma braidAut_wordProd (ω : List I) :
    ((ω.map (braidAut hv)).prod : torusAut R v).1.1 =
      (ω.map (braidEquivOfNotRoot R hv)).prod := by
  induction ω with
  | nil => rfl
  | cons a ω ih =>
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, Prod.fst_mul, ih]
    rfl

/-- The braid relations for the pairs `(Tᵢ, sᵢ)`. -/
theorem isBraidLiftable_braidAut :
    D.cartanMatrix.coxeterMatrix.IsBraidLiftable (braidAut (R := R) hv) := fun i j hij hm ↦
  torusAut_ext hv (by
    rw [braidAut_wordProd, braidAut_wordProd]
    exact isBraidLiftable_braidEquivOfNotRoot R hv i j hij hm)

/-- **Lusztig's `Tᵢ = T''_{i,1}` on `U̇`** ([Lus] 41.1.1): the automorphism with
`Tᵢ(π_{λ',λ''}(u)) = π_{sᵢλ', sᵢλ''}(Tᵢ u)` (`braid_elt`); it is multiplicative (`braid_mul`). -/
def braid (i : I) : Modified R v ≃ₗ[k] Modified R v := mapHom R v (braidAut hv i)

lemma braid_elt (i : I) (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (l₁ - l₂))
    (hu' : braidEquivOfNotRoot R hv i u ∈
      adWeightSpace R v (l₁.comp (reflY R i) - l₂.comp (reflY R i))) :
    braid hv i (elt l₁ l₂ u hu) =
      elt (l₁.comp (reflY R i)) (l₂.comp (reflY R i)) (braidEquivOfNotRoot R hv i u) hu' := by
  rw [braid, mapHom_apply, map_elt]
  exact elt_index (wt_braidAut hv i l₁) (wt_braidAut hv i l₂) rfl _ _

lemma braid_mul (i : I) (x y : Modified R v) : braid hv i (x * y) = braid hv i x * braid hv i y :=
  mapHom_mul _ x y

/-- `Tᵢ(1_λ) = 1_{sᵢλ}` ([Lus] 41.1.1). -/
lemma braid_one (i : I) (l : Y →+ ℤ) : braid (R := R) hv i (one l) = one (l.comp (reflY R i)) := by
  rw [one, braid_elt hv i l l _ (by rw [_root_.map_one, sub_self]; exact one_mem_adWeightSpace),
    one]
  exact elt_congr (_root_.map_one _) _ _

/-- The inverse of `Tᵢ` on `U̇` is induced by `Tᵢ⁻¹ = T'_{i,-1}` ([Lus] 41.1.1). -/
lemma braid_symm_elt (i : I) (l₁ l₂ : Y →+ ℤ) {u : QuantumGroup R v}
    (hu : u ∈ adWeightSpace R v (l₁ - l₂))
    (hu' : (braidEquivOfNotRoot R hv i).symm u ∈
      adWeightSpace R v (l₁.comp (reflY R i) - l₂.comp (reflY R i))) :
    (braid hv i).symm (elt l₁ l₂ u hu) =
      elt (l₁.comp (reflY R i)) (l₂.comp (reflY R i))
        ((braidEquivOfNotRoot R hv i).symm u) hu' := by
  have hc : ∀ l : Y →+ ℤ, (l.comp (reflY R i)).comp (reflY R i) = l := fun l ↦ by
    ext μ; simp
  rw [LinearEquiv.symm_apply_eq, braid_elt hv i _ _ hu' (by
    rw [hc, hc, AlgEquiv.apply_symm_apply]; exact hu)]
  exact elt_index (hc l₁).symm (hc l₂).symm (AlgEquiv.apply_symm_apply _ _).symm _ _

/-- **The braid relations on `U̇`** ([Lus] 41.1.1) for every Cartan datum, `v ≠ 0` not a root of
unity. -/
theorem isBraidLiftable_braid :
    D.cartanMatrix.coxeterMatrix.IsBraidLiftable (braid (R := R) hv) := fun i j hij hm ↦ by
  have h := congrArg (mapHom R v) (isBraidLiftable_braidAut (R := R) hv i j hij hm)
  rwa [map_list_prod, map_list_prod, List.map_map, List.map_map] at h

/-- **The Artin group action on `U̇`** ([Lus] 41.1.1): `σᵢ ↦ Tᵢ`, by multiplicative linear
automorphisms (`braidArtinHom_mul`). -/
def braidArtinHom :
    D.cartanMatrix.coxeterMatrix.ArtinGroup →* (Modified R v ≃ₗ[k] Modified R v) :=
  (mapHom R v).comp (CoxeterMatrix.artinLift (braidAut hv) (isBraidLiftable_braidAut hv))

@[simp] theorem braidArtinHom_artinGenerator (i : I) :
    braidArtinHom (R := R) hv (D.cartanMatrix.coxeterMatrix.artinGenerator i) = braid hv i := by
  exact congrArg (mapHom R v) (CoxeterMatrix.artinLift_artinGenerator _ _ i)

theorem braidArtinHom_mul (g : D.cartanMatrix.coxeterMatrix.ArtinGroup) (x y : Modified R v) :
    braidArtinHom hv g (x * y) = braidArtinHom hv g x * braidArtinHom hv g y :=
  mapHom_mul _ x y

end Braid

end Modified

end LieLean.QuantumGroup
