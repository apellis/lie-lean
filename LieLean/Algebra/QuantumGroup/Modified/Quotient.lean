/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# `ₗU_λ''` as Lusztig's quotient of `U`

Lusztig defines the component `ₗU_λ''` of `U̇` as the quotient
`U / (Σ_μ (K_μ - v^{⟨μ,λ'⟩}) U + Σ_μ U (K_μ - v^{⟨μ,λ''⟩}))` of all of `U` ([Lus] 23.1.1 (a)),
and observes that only the part of `U` of weight `λ' - λ''` survives ([Lus] 23.1.2). The library
(`QuantumGroup.Modified.Comp`) builds `ₗU_λ''` from the conjugation weight space `U_{λ'-λ''}`
(`adWeightSpace`). Here we prove that the two definitions agree, for `v ≠ 0` not a root of unity.

`adWeightSpace R v χ` is the sum of Lusztig's homogeneous components `U(ν)`, `ν ∈ ℤ[I]`, over the
`ν` whose image in `X = Hom(Y, ℤ)` is `χ`; so `mem_lusztigRel_of_ne` is the vanishing assertion of
[Lus] 23.1.2 (`ₗU_λ''(ν) = 0` unless `λ' - λ'' = ν` in `X`).

## Main results

* `QuantumGroup.isInternal_adWeightSpace`: `U = ⊕_χ U_χ`.
* `QuantumGroup.lusztigRel`: Lusztig's relations
  `Σ_μ (K_μ - v^{⟨μ,λ'⟩}) U + Σ_μ U (K_μ - v^{⟨μ,λ''⟩})`.
* `QuantumGroup.mem_lusztigRel_of_ne`: `U_χ ⊆ lusztigRel λ' λ''` for `χ ≠ λ' - λ''` ([Lus] 23.1.2).
* `QuantumGroup.Modified.compEquivLusztig`: **the comparison isomorphism**
  `ₗU_λ'' = U_{λ'-λ''} / N(λ', λ'') ≃ U / lusztigRel λ' λ''`, induced by the inclusion
  ([Lus] 23.1.1 (a), 23.1.2).

## References

* [Lus] G. Lusztig, *Introduction to quantum groups*, Birkhäuser 1993, 23.1.
-/

open LieLean

noncomputable section

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y) (v : k)

/-! ### `U` is the direct sum of the conjugation weight spaces -/

/-- The character `Σⱼ αⱼ` of a word `w` (as an element of `X = Hom(Y, ℤ)`). -/
def wordChar (w : List I) : Y →+ ℤ := (w.map R.root).sum

variable {R v}

omit [DecidableEq I] in
@[simp] lemma wordChar_nil : wordChar R ([] : List I) = 0 := rfl

omit [DecidableEq I] in
@[simp] lemma wordChar_cons (i : I) (w : List I) :
    wordChar R (i :: w) = R.root i + wordChar R w := by
  simp [wordChar]

section Weights

variable [NeZero v]

lemma plusHom_monomial_mem_adWeightSpace (w : List I) :
    plusHom R v (LusztigF.monomial k w) ∈ adWeightSpace R v (wordChar R w) := by
  induction w with
  | nil => simpa using one_mem_adWeightSpace
  | cons i w ih =>
    rw [LusztigF.monomial_cons, map_mul, plusHom_θ, wordChar_cons]
    exact mul_mem_adWeightSpace (E_mem_adWeightSpace i) ih

lemma minusHom_monomial_mem_adWeightSpace (w : List I) :
    minusHom R v (LusztigF.monomial k w) ∈ adWeightSpace R v (-wordChar R w) := by
  induction w with
  | nil => simpa using one_mem_adWeightSpace
  | cons i w ih =>
    rw [LusztigF.monomial_cons, map_mul, minusHom_θ, wordChar_cons, neg_add]
    exact mul_mem_adWeightSpace (fun μ ↦ K_mul_F R v μ i) ih

lemma triangular_mem_adWeightSpace (w : List I) (μ : Y) (w' : List I) :
    minusHom R v (LusztigF.monomial k w) * K R v μ * plusHom R v (LusztigF.monomial k w') ∈
      adWeightSpace R v (-wordChar R w + wordChar R w') := by
  simpa using mul_mem_adWeightSpace (mul_mem_adWeightSpace
    (minusHom_monomial_mem_adWeightSpace w) (K_mem_adWeightSpace μ))
    (plusHom_monomial_mem_adWeightSpace w')

variable (R v) in
theorem iSup_adWeightSpace : ⨆ χ, adWeightSpace R v χ = ⊤ := by
  rw [eq_top_iff, ← span_triangular (R := R) (NeZero.ne v), triangularSpan, Submodule.span_le]
  rintro _ ⟨w, μ, w', rfl⟩
  exact Submodule.mem_iSup_of_mem _ (triangular_mem_adWeightSpace w μ w')

end Weights

omit [AddCommGroup Y] [DecidableEq I] in
lemma zpow_injective_of_not_root {v : k} (hv0 : v ≠ 0) (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    Function.Injective fun n : ℤ ↦ v ^ n := by
  have key : ∀ a b : ℤ, a < b → v ^ a ≠ v ^ b := fun a b hab h ↦ by
    have h1 : v ^ (b - a) = 1 := by
      rw [zpow_sub₀ hv0, ← h, div_self (zpow_ne_zero _ hv0)]
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hab.le)
    rw [hn, zpow_natCast] at h1
    exact hv n (by omega) h1
  intro a b h
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact absurd h (key a b hab)
  · rfl
  · exact absurd h.symm (key b a hab)

variable (R v) in
/-- Conjugation by `K_μ`. -/
def conjK (μ : Y) : Module.End k (QuantumGroup R v) :=
  LinearMap.mulLeft k (K R v μ) ∘ₗ LinearMap.mulRight k (K R v (-μ))

lemma conjK_apply (μ : Y) (x : QuantumGroup R v) :
    conjK R v μ x = K R v μ * x * K R v (-μ) := by
  simp [conjK, mul_assoc]

lemma conjK_comm (μ ν : Y) : Commute (conjK R v μ) (conjK R v ν) := by
  have key : ∀ μ ν : Y, ∀ x : QuantumGroup R v,
      K R v μ * (K R v ν * x * K R v (-ν)) * K R v (-μ) =
        K R v (μ + ν) * x * K R v (-(μ + ν)) := fun μ ν x ↦ by
    have h : K R v (-ν) * K R v (-μ) = K R v (-(μ + ν)) := by
      rw [K_add]; congr 1; abel
    rw [← K_add, ← h]; simp only [mul_assoc]
  ext x
  simp only [Module.End.mul_apply, conjK_apply]
  rw [key, key, add_comm]

lemma adWeightSpace_le_eigenspace (χ : Y →+ ℤ) (μ : Y) :
    adWeightSpace R v χ ≤ Module.End.eigenspace (conjK R v μ) (v ^ χ μ) := fun x hx ↦ by
  rw [Module.End.mem_eigenspace_iff, conjK_apply]
  exact conj_eq_of_mem_adWeightSpace hx μ

variable (R) in
/-- The conjugation weight spaces are independent (`v ≠ 0` not a root of unity). -/
theorem iSupIndep_adWeightSpace (hv0 : v ≠ 0) (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    iSupIndep (adWeightSpace R v) := by
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (conjK R v)
    (fun μ ν φ ↦ Module.End.mapsTo_maxGenEigenspace_of_comm (conjK_comm ν μ) φ)
  let e : (Y →+ ℤ) → (Y → k) := fun χ μ ↦ v ^ χ μ
  have he : Function.Injective e := fun χ χ' h ↦ by
    ext μ
    exact zpow_injective_of_not_root hv0 hv (congrFun h μ)
  refine (hind.comp he).mono fun χ ↦ le_iInf fun μ ↦ ?_
  exact (adWeightSpace_le_eigenspace χ μ).trans Module.End.eigenspace_le_maxGenEigenspace

open scoped Classical in
variable (R) in
/-- `U = ⊕_χ U_χ` (`v ≠ 0` not a root of unity). -/
theorem isInternal_adWeightSpace [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) :
    DirectSum.IsInternal (adWeightSpace R v) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_adWeightSpace R (NeZero.ne v) hv) (iSup_adWeightSpace R v)

/-! ### Lusztig's relations -/

variable (R v) in
/-- Lusztig's relations `Σ_μ (K_μ - v^{⟨μ,λ'⟩}) U + Σ_μ U (K_μ - v^{⟨μ,λ''⟩})`
([Lus] 23.1.1 (a)). -/
def lusztigRel (l₁ l₂ : Y →+ ℤ) : Submodule k (QuantumGroup R v) :=
  Submodule.span k
    ({x | ∃ μ u, x = (K R v μ - algebraMap k _ (v ^ l₁ μ)) * u} ∪
     {x | ∃ μ u, x = u * (K R v μ - algebraMap k _ (v ^ l₂ μ))})

variable [NeZero v]

omit [NeZero v] in
lemma modRel_le_lusztigRel (l₁ l₂ : Y →+ ℤ) : modRel R v l₁ l₂ ≤ lusztigRel R v l₁ l₂ := by
  refine Submodule.span_le.2 ?_
  rintro x (⟨μ, u, -, rfl⟩ | ⟨μ, u, -, rfl⟩)
  · exact Submodule.subset_span (Or.inl ⟨μ, u, rfl⟩)
  · exact Submodule.subset_span (Or.inr ⟨μ, u, rfl⟩)

/-- **[Lus] 23.1.2**: the part of `U` of weight `χ ≠ λ' - λ''` lies in Lusztig's relations, so it
vanishes in `ₗU_λ''`. -/
theorem mem_lusztigRel_of_ne (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) {l₁ l₂ χ : Y →+ ℤ}
    (hχ : χ ≠ l₁ - l₂) {u : QuantumGroup R v} (hu : u ∈ adWeightSpace R v χ) :
    u ∈ lusztigRel R v l₁ l₂ := by
  obtain ⟨μ, hμ⟩ : ∃ μ, χ μ ≠ (l₁ - l₂) μ := by
    by_contra h; exact hχ (AddMonoidHom.ext fun μ ↦ not_not.1 fun h' ↦ h ⟨μ, h'⟩)
  set c : k := v ^ (χ μ + l₂ μ) - v ^ l₁ μ
  have hc : c ≠ 0 := sub_ne_zero.2 fun h ↦ hμ (by
    have := zpow_injective_of_not_root (NeZero.ne v) hv h
    rw [AddMonoidHom.sub_apply]; omega)
  have e : c • u = (K R v μ - algebraMap k _ (v ^ l₁ μ)) * u -
      v ^ χ μ • (u * (K R v μ - algebraMap k _ (v ^ l₂ μ))) := by
    rw [sub_mul, mul_sub, hu μ]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
      smul_sub, smul_smul, c, sub_smul, ← zpow_add₀ (NeZero.ne v)]
    abel
  have : c • u ∈ lusztigRel R v l₁ l₂ := by
    rw [e]
    exact sub_mem (Submodule.subset_span (Or.inl ⟨μ, u, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨μ, u, rfl⟩)))
  simpa [smul_smul, inv_mul_cancel₀ hc] using Submodule.smul_mem _ c⁻¹ this

variable (R v) in
/-- The weight spaces other than `χ`. -/
def otherWeights (χ : Y →+ ℤ) : Submodule k (QuantumGroup R v) :=
  ⨆ (χ' : Y →+ ℤ) (_ : χ' ≠ χ), adWeightSpace R v χ'

lemma sup_otherWeights (χ : Y →+ ℤ) :
    adWeightSpace R v χ ⊔ otherWeights R v χ = ⊤ := by
  rw [eq_top_iff, ← iSup_adWeightSpace R v, iSup_le_iff]
  intro χ'
  by_cases h : χ' = χ
  · subst h; exact le_sup_left
  · exact le_sup_of_le_right (le_biSup (fun χ' ↦ adWeightSpace R v χ') h)

lemma inf_otherWeights (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (χ : Y →+ ℤ) :
    adWeightSpace R v χ ⊓ otherWeights R v χ = ⊥ :=
  ((iSupIndep_adWeightSpace R (NeZero.ne v) hv).disjoint_biSup (x := χ) (y := {χ' | χ' ≠ χ})
    (by simp)).eq_bot

lemma mul_mem_otherWeights_left {χ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ adWeightSpace R v 0) (hb : b ∈ otherWeights R v χ) :
    a * b ∈ otherWeights R v χ := by
  induction hb using Submodule.iSup_induction' with
  | mem χ' x hx =>
    induction hx using Submodule.iSup_induction' with
    | mem h x hx =>
      exact Submodule.mem_iSup_of_mem χ' (Submodule.mem_iSup_of_mem h (by
        simpa using mul_mem_adWeightSpace ha hx))
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy

lemma mul_mem_otherWeights_right {χ : Y →+ ℤ} {a b : QuantumGroup R v}
    (ha : a ∈ otherWeights R v χ) (hb : b ∈ adWeightSpace R v 0) :
    a * b ∈ otherWeights R v χ := by
  induction ha using Submodule.iSup_induction' with
  | mem χ' x hx =>
    induction hx using Submodule.iSup_induction' with
    | mem h x hx =>
      exact Submodule.mem_iSup_of_mem χ' (Submodule.mem_iSup_of_mem h (by
        simpa using mul_mem_adWeightSpace hx hb))
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy

lemma otherWeights_le_lusztigRel (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (l₁ l₂ : Y →+ ℤ) :
    otherWeights R v (l₁ - l₂) ≤ lusztigRel R v l₁ l₂ :=
  iSup₂_le fun _ h _ hx ↦ mem_lusztigRel_of_ne hv h hx

/-- `lusztigRel λ' λ'' = N(λ', λ'') ⊔ (the weight spaces other than λ' - λ'')`. -/
theorem lusztigRel_eq (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (l₁ l₂ : Y →+ ℤ) :
    lusztigRel R v l₁ l₂ = modRel R v l₁ l₂ ⊔ otherWeights R v (l₁ - l₂) := by
  refine le_antisymm ?_ (sup_le (modRel_le_lusztigRel l₁ l₂) (otherWeights_le_lusztigRel hv l₁ l₂))
  have hdec : ∀ u : QuantumGroup R v, ∃ a ∈ adWeightSpace R v (l₁ - l₂),
      ∃ b ∈ otherWeights R v (l₁ - l₂), u = a + b := fun u ↦
    Submodule.mem_sup.1 (by rw [sup_otherWeights]; trivial) |>.imp fun a ⟨ha, b, hb, e⟩ ↦
      ⟨ha, b, hb, e.symm⟩
  refine Submodule.span_le.2 ?_
  rintro x (⟨μ, u, rfl⟩ | ⟨μ, u, rfl⟩)
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec u
    rw [mul_add]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span (Or.inl ⟨μ, a, ha, rfl⟩)))
      (Submodule.mem_sup_right (mul_mem_otherWeights_left (sub_mem_adWeightSpace_zero μ _) hb))
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec u
    rw [add_mul]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨μ, a, ha, rfl⟩)))
      (Submodule.mem_sup_right (mul_mem_otherWeights_right hb (sub_mem_adWeightSpace_zero μ _)))

/-- `U_{λ'-λ''} ∩ lusztigRel λ' λ'' = N(λ', λ'')`. -/
theorem adWeightSpace_inf_lusztigRel (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (l₁ l₂ : Y →+ ℤ) :
    adWeightSpace R v (l₁ - l₂) ⊓ lusztigRel R v l₁ l₂ = modRel R v l₁ l₂ := by
  rw [lusztigRel_eq hv, inf_comm, sup_inf_assoc_of_le _ (modRel_le l₁ l₂), inf_comm,
    inf_otherWeights hv, sup_bot_eq]

namespace Modified

variable (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)

/-- The map `ₗU_λ'' → U / lusztigRel λ' λ''` induced by the inclusion `U_{λ'-λ''} ⊆ U`. -/
def compToLusztig (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    Comp R v p →ₗ[k] QuantumGroup R v ⧸ lusztigRel R v p.1 p.2 :=
  Submodule.mapQ _ _ (adWeightSpace R v (p.1 - p.2)).subtype
    (fun _ hx ↦ modRel_le_lusztigRel p.1 p.2 hx)

omit [NeZero v] in
lemma compToLusztig_mk (p : (Y →+ ℤ) × (Y →+ ℤ)) (x : adWeightSpace R v (p.1 - p.2)) :
    compToLusztig p (Comp.mk R v p x) = Submodule.Quotient.mk x.1 := rfl

include hv in
lemma compToLusztig_bijective (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    Function.Bijective (compToLusztig (R := R) (v := v) p) := by
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := Comp.mk_surjective R v p z
    rw [LinearMap.mem_ker, compToLusztig_mk, Submodule.Quotient.mk_eq_zero] at hz
    rw [Submodule.mem_bot, Comp.mk_eq_zero, ← adWeightSpace_inf_lusztigRel hv]
    exact ⟨x.2, hz⟩
  · intro z
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
      (show u ∈ adWeightSpace R v (p.1 - p.2) ⊔ otherWeights R v (p.1 - p.2) by
        rw [sup_otherWeights]; trivial)
    refine ⟨Comp.mk R v p ⟨a, ha⟩, ?_⟩
    rw [compToLusztig_mk, Submodule.Quotient.eq]
    simpa using neg_mem (otherWeights_le_lusztigRel hv p.1 p.2 hb)

/-- **The comparison isomorphism** ([Lus] 23.1.1 (a), 23.1.2): the component
`ₗU_λ'' = U_{λ'-λ''} / N(λ', λ'')` of `U̇` (as built in `Modified.Comp`) is Lusztig's quotient
`U / (Σ_μ (K_μ - v^{⟨μ,λ'⟩}) U + Σ_μ U (K_μ - v^{⟨μ,λ''⟩}))`, by the map induced by the inclusion
`U_{λ'-λ''} ⊆ U`; `v ≠ 0` not a root of unity (Lusztig: `v` transcendental). -/
def compEquivLusztig (p : (Y →+ ℤ) × (Y →+ ℤ)) :
    Comp R v p ≃ₗ[k] QuantumGroup R v ⧸ lusztigRel R v p.1 p.2 :=
  LinearEquiv.ofBijective (compToLusztig p) (compToLusztig_bijective hv p)

@[simp] lemma compEquivLusztig_mk (p : (Y →+ ℤ) × (Y →+ ℤ)) (x : adWeightSpace R v (p.1 - p.2)) :
    compEquivLusztig hv p (Comp.mk R v p x) = Submodule.Quotient.mk x.1 := rfl

end Modified

end LieLean.QuantumGroup
