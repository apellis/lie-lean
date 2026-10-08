/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorModuleCrystal

/-!
# The crystal of a tensor product of crystal bases

For crystal bases `(L₁, B₁)`, `(L₂, B₂)` of finite-dimensional integrable `U_q(𝔰𝔩₂)`-modules, the
class `b₁ ⊗ b₂` of `x ⊗ y` (`[x] = b₁`, `[y] = b₂`) in `L₁ ⊗ L₂ / c L₁ ⊗ L₂`
(`QuantumGroup.IntegrableSl2.IsCrystalBase.tmulQ`) satisfies Kashiwara's tensor product rule
(`QuantumGroup.IntegrableSl2.IsCrystalBase.fTildeQ_tmulQ`,
`QuantumGroup.IntegrableSl2.IsCrystalBase.eTildeQ_tmulQ`; [HK] (4.11), (4.12)).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.4.
-/

open TensorProduct Pointwise


/-! ### Isomorphisms of seminormal crystals -/

namespace Crystal

variable {ι X : Type*} [AddCommGroup X] {D : CartanDatum ι X} {B B' : Type*}
  {C : Crystal D B} {C' : Crystal D B'}

lemma eIter_map_of_e (Φ : B → B') (he : ∀ i b, C'.e i (Φ b) = (C.e i b).map Φ) (i : ι) (n : ℕ)
    (b : B) : C'.eIter i n (Φ b) = (C.eIter i n b).map Φ := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [eIter_succ, eIter_succ, he]
    cases C.e i b with
    | none => rfl
    | some b' => exact ih b'

lemma ε_eq_of_e (hC : C.IsSeminormal) (hC' : C'.IsSeminormal) (Φ : B → B')
    (he : ∀ i b, C'.e i (Φ b) = (C.e i b).map Φ) (i : ι) (b : B) : C'.ε i (Φ b) = C.ε i b := by
  obtain ⟨m, hm⟩ := hC'.exists_ε_eq i (Φ b)
  obtain ⟨n, hn⟩ := hC.exists_ε_eq i b
  have key : ∀ a : ℕ, ((a : WithBot ℤ) ≤ m ↔ (a : WithBot ℤ) ≤ n) := fun a ↦ by
    rw [← hm, ← hn, ← (hC' i (Φ b) a).1, ← (hC i b a).1, eIter_map_of_e Φ he, Option.isSome_map]
  have h1 := (key m).1 le_rfl
  have h2 := (key n).2 le_rfl
  rw [hm, hn]
  norm_cast at h1 h2 ⊢
  omega

/-- A bijection between seminormal crystals preserving weights and commuting with the `ẽᵢ` is
an isomorphism. -/
def equivOfE (hC : C.IsSeminormal) (hC' : C'.IsSeminormal) (Φ : B ≃ B')
    (hwt : ∀ b, C'.wt (Φ b) = C.wt b) (he : ∀ i b, C'.e i (Φ b) = (C.e i b).map Φ) :
    Crystal.Equiv C C' where
  toEquiv := Φ
  wt_map := hwt
  ε_map := ε_eq_of_e hC hC' Φ he
  e_map := he
  f_map i b := by
    change C'.f i (Φ b) = (C.f i b).map Φ
    cases h : C.f i b with
    | none =>
      rw [Option.map_none, Option.eq_none_iff_forall_ne_some]
      intro b'' hb''
      obtain ⟨b', rfl⟩ := Φ.surjective b''
      rw [C'.f_eq_some_iff, he, Option.map_eq_some_iff] at hb''
      obtain ⟨b₀, hb₀, he₀⟩ := hb''
      rw [Φ.injective he₀, ← C.f_eq_some_iff, h] at hb₀
      cases hb₀
    | some b' =>
      rw [Option.map_some, C'.f_eq_some_iff, he, (C.f_eq_some_iff i b b').1 h, Option.map_some]

end Crystal

namespace LieLean.QuantumGroup

namespace IntegrableSl2

namespace IsCrystalBase

/-! ### `ẽ`, `f̃` on the classes of a string -/

section Strings

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M} {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M} {c : A} {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}
  (hB : V.IsCrystalBase hq0 hq L c B) (hc : ¬IsUnit c)
include hB

lemma fQ_strCls (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) (hx : (x.2 : ℕ) < hB.hwt hc x.1) :
    V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c (hB.strCls hc x) =
      hB.strCls hc ⟨x.1, ⟨x.2 + 1, by omega⟩⟩ := by
  simp only [strCls]
  rw [← Module.End.mul_apply, ← pow_succ']

lemma fQ_strCls_eq_zero (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1))
    (hx : (x.2 : ℕ) = hB.hwt hc x.1) :
    V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c (hB.strCls hc x) = 0 := by
  have := (hB.fQ_pow_strCls_eq_zero_iff hc x 1).2 (by omega)
  simpa using this

lemma eQ_strCls (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) (hx : 0 < (x.2 : ℕ)) :
    V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c (hB.strCls hc x) =
      hB.strCls hc ⟨x.1, ⟨x.2 - 1, by omega⟩⟩ := by
  have := hB.eQ_pow_fQ_pow x.1.1 x.1.2.1 1 ((x.2 : ℕ) - 1)
    (by rw [show 1 + ((x.2 : ℕ) - 1) = x.2 by omega]; exact hB.strCls_ne_zero hc x)
  rw [show 1 + ((x.2 : ℕ) - 1) = x.2 by omega, pow_one] at this
  exact this

lemma eQ_strCls_eq_zero (x : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) (hx : (x.2 : ℕ) = 0) :
    V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c (hB.strCls hc x) = 0 := by
  have := (hB.eQ_pow_strCls_eq_zero_iff hc x 1).2 (by omega)
  simpa using this

lemma hvec_ne_zero (h : hB.highest) : hB.hvec hc h ≠ 0 := fun h0 ↦
  hB.hvec_notMem hc h (h0 ▸ zero_mem _)

lemma eps_eq {b₂ : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)}
    (t : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) (ht : hB.strCls hc t = b₂) {e₂ : ℕ}
    (he : ∀ a, (V.eTildeQ hq0 hq hB.isKashiwaraStable.eTilde_mem c ^ a) b₂ = 0 ↔ e₂ < a) :
    e₂ = t.2 := by
  subst ht
  have h1 := (he e₂).symm.trans (hB.eQ_pow_strCls_eq_zero_iff hc t e₂)
  have h2 := (he t.2).symm.trans (hB.eQ_pow_strCls_eq_zero_iff hc t t.2)
  simp only [lt_self_iff_false, false_iff, iff_false] at h1 h2
  omega

lemma phi_eq {b₁ : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)}
    (s : Σ h : hB.highest, Fin (hB.hwt hc h + 1)) (hs : hB.strCls hc s = b₁) {φ₁ : ℕ}
    (hφ : ∀ a, (V.fTildeQ hq0 hq hB.isKashiwaraStable.fTilde_mem c ^ a) b₁ = 0 ↔ φ₁ < a) :
    φ₁ + s.2 = hB.hwt hc s.1 := by
  subst hs
  have h1 := (hφ φ₁).symm.trans (hB.fQ_pow_strCls_eq_zero_iff hc s φ₁)
  have h2 := (hφ (φ₁ + 1)).symm.trans (hB.fQ_pow_strCls_eq_zero_iff hc s (φ₁ + 1))
  simp only [lt_self_iff_false, false_iff, lt_add_iff_pos_right, Nat.lt_one_iff,
    true_iff] at h1 h2
  omega

end Strings

/-! ### Classes of pure tensors -/

section Tensor

variable {k : Type*} [Field k] {q : k} {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁]
  [AddCommGroup M₂] [Module k M₂] {V₁ : IntegrableSl2 q M₁} {V₂ : IntegrableSl2 q M₂}
  {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂]
  {L₁ : Submodule A M₁} {L₂ : Submodule A M₂} {c : A}
  {B₁ : Set (L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))}
  {B₂ : Set (L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂))}
  (hB₁ : V₁.IsCrystalBase hq0 hq L₁ c B₁) (hB₂ : V₂.IsCrystalBase hq0 hq L₂ c B₂)
  (hc : ¬IsUnit c)
  [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M₁] [FiniteDimensional k M₂]

/-- The class `β₁ ⊗ β₂ = [x ⊗ y]` (`[x] = β₁`, `[y] = β₂`) in `L₁ ⊗ L₂ / c L₁ ⊗ L₂`. -/
noncomputable def tmulQ (β₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))
    (β₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)) :
    tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A ⧸
      (Ideal.span {c} • ⊤ : Submodule A
        (tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A)) :=
  Submodule.Quotient.mk ⟨_, hB₁.tmul_mem_tensorLattice hB₂ hc
    (Submodule.Quotient.mk_surjective _ β₁).choose (Submodule.Quotient.mk_surjective _ β₂).choose⟩

lemma tmulQ_mk (x : L₁) (y : L₂) :
    hB₁.tmulQ hB₂ hc (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨_, hB₁.tmul_mem_tensorLattice hB₂ hc x y⟩ := by
  unfold tmulQ
  have h1 := (Submodule.Quotient.mk_surjective (Ideal.span {c} • ⊤ : Submodule A L₁)
    (Submodule.Quotient.mk x)).choose_spec
  have h2 := (Submodule.Quotient.mk_surjective (Ideal.span {c} • ⊤ : Submodule A L₂)
    (Submodule.Quotient.mk y)).choose_spec
  rw [mk_eq_mk_iff] at h1 h2 ⊢
  exact tmul_sub_tmul_mem_smul (fun x hx y hy ↦ hB₁.tmul_mem_tensorLattice hB₂ hc ⟨x, hx⟩ ⟨y, hy⟩)
    (Submodule.coe_mem _) y.2 h1 h2

lemma tmulQ_zero_left (β₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)) :
    hB₁.tmulQ hB₂ hc 0 β₂ = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ β₂
  have h0 : (0 : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)) = Submodule.Quotient.mk 0 :=
    (Submodule.Quotient.mk_zero _).symm
  have : (⟨((0 : L₁) : M₁) ⊗ₜ[k] (y : M₂), hB₁.tmul_mem_tensorLattice hB₂ hc 0 y⟩ :
      tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A) = 0 :=
    Subtype.ext (by simp)
  rw [h0, tmulQ_mk, this, Submodule.Quotient.mk_zero]

lemma tmulQ_zero_right (β₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)) :
    hB₁.tmulQ hB₂ hc β₁ 0 = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ β₁
  have h0 : (0 : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)) = Submodule.Quotient.mk 0 :=
    (Submodule.Quotient.mk_zero _).symm
  have : (⟨(x : M₁) ⊗ₜ[k] ((0 : L₂) : M₂), hB₁.tmul_mem_tensorLattice hB₂ hc x 0⟩ :
      tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A) = 0 :=
    Subtype.ext (by simp)
  rw [h0, tmulQ_mk, this, Submodule.Quotient.mk_zero]

lemma tmulQ_strCls (s : Σ h : hB₁.highest, Fin (hB₁.hwt hc h + 1))
    (t : Σ h : hB₂.highest, Fin (hB₂.hwt hc h + 1)) :
    hB₁.tmulQ hB₂ hc (hB₁.strCls hc s) (hB₂.strCls hc t) = Submodule.Quotient.mk
      ⟨tensorVec V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) (s, t),
        tensorVec_mem V₁ V₂ _ _ _ _ (s, t)⟩ := by
  rw [hB₁.strCls_eq hc, hB₂.strCls_eq hc, tmulQ_mk]
  rfl

/-- The classes `b₁ ⊗ b₂` (`b₁ ∈ B₁`, `b₂ ∈ B₂`) are distinct. -/
theorem tmulQ_injective {b₁ b₁' : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)}
    {b₂ b₂' : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)} (hb₁ : b₁ ∈ B₁) (hb₁' : b₁' ∈ B₁)
    (hb₂ : b₂ ∈ B₂) (hb₂' : b₂' ∈ B₂) (h : hB₁.tmulQ hB₂ hc b₁ b₂ = hB₁.tmulQ hB₂ hc b₁' b₂') :
    b₁ = b₁' ∧ b₂ = b₂' := by
  obtain ⟨s, rfl⟩ := hB₁.exists_strCls_eq hc b₁ hb₁
  obtain ⟨s', rfl⟩ := hB₁.exists_strCls_eq hc b₁' hb₁'
  obtain ⟨t, rfl⟩ := hB₂.exists_strCls_eq hc b₂ hb₂
  obtain ⟨t', rfl⟩ := hB₂.exists_strCls_eq hc b₂' hb₂'
  rw [tmulQ_strCls, tmulQ_strCls] at h
  have := mk_tensorVec_injective hq0 hq (hB₁.hvec_prim hc) (hB₂.hvec_prim hc)
    (hB₁.eq_stringLattice hc).2.1 (hB₂.eq_stringLattice hc).2.1 hc h
  simp only [Prod.mk.injEq] at this
  rw [this.1, this.2]
  exact ⟨rfl, rfl⟩

variable {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖq : algebraMap A k ϖ = q)
  (hϖc : ϖ ∈ Ideal.span {c})

omit [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M₁] [FiniteDimensional k M₂] in
lemma mk_tensorVecOpt (o : Option (TensorPos (hB₁.hwt hc) (hB₂.hwt hc))) :
    (Submodule.Quotient.mk ⟨_, tensorVecOpt_mem (V₁ := V₁) (V₂ := V₂) (A := A) o⟩ :
      tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A ⧸
        (Ideal.span {c} • ⊤ : Submodule A
          (tensorLattice V₁ V₂ (hB₁.hwt hc) (hB₂.hwt hc) (hB₁.hvec hc) (hB₂.hvec hc) A))) =
      o.elim 0 fun y ↦ Submodule.Quotient.mk ⟨_, tensorVec_mem V₁ V₂ _ _ _ _ y⟩ := by
  rcases o with _ | y
  · change Submodule.Quotient.mk _ = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 (zero_mem _)
  · rfl

include hϖ hϖq hϖc

/-- **Tensor product rule for `f̃`** ([HK] (4.12)): `f̃ (b₁ ⊗ b₂) = f̃ b₁ ⊗ b₂` if
`φ(b₁) > ε(b₂)`, and `b₁ ⊗ f̃ b₂` otherwise. -/
theorem fTildeQ_tmulQ {b₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)}
    {b₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)} (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂)
    {e₂ φ₁ : ℕ}
    (he : ∀ a, (V₂.eTildeQ hq0 hq hB₂.isKashiwaraStable.eTilde_mem c ^ a) b₂ = 0 ↔ e₂ < a)
    (hφ : ∀ a, (V₁.fTildeQ hq0 hq hB₁.isKashiwaraStable.fTilde_mem c ^ a) b₁ = 0 ↔ φ₁ < a) :
    (tensor V₁ V₂ hq0 hq).fTildeQ hq0 hq
      (hB₁.isCrystalBase_tensor hB₂ hc hϖ hϖq hϖc).isKashiwaraStable.fTilde_mem c
      (hB₁.tmulQ hB₂ hc b₁ b₂) =
      if e₂ < φ₁ then
        hB₁.tmulQ hB₂ hc (V₁.fTildeQ hq0 hq hB₁.isKashiwaraStable.fTilde_mem c b₁) b₂
      else hB₁.tmulQ hB₂ hc b₁ (V₂.fTildeQ hq0 hq hB₂.isKashiwaraStable.fTilde_mem c b₂) := by
  obtain ⟨s, hs⟩ := hB₁.exists_strCls_eq hc b₁ hb₁
  obtain ⟨t, ht⟩ := hB₂.exists_strCls_eq hc b₂ hb₂
  have he' := hB₂.eps_eq hc t ht he
  have hφ' := hB₁.phi_eq hc s hs hφ
  subst hs ht
  rw [tmulQ_strCls, fTildeQ_mk_tensorVec hq0 hq hϖ hϖq (hB₁.hvec_prim hc) (hB₂.hvec_prim hc)
    (hB₁.hvec_ne_zero hc) (hB₂.hvec_ne_zero hc) hϖc, mk_tensorVecOpt hB₁ hB₂ hc]
  have hs2 := s.2.2
  have ht2 := t.2.2
  by_cases h1 : (t.2 : ℕ) < hB₁.hwt hc s.1 - s.2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), hB₁.fQ_strCls hc s (by omega),
      tmulQ_strCls]
    simp only [nextPos, h1, ↓reduceDIte, Option.elim_some]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    by_cases h2 : (t.2 : ℕ) + 1 ≤ hB₂.hwt hc t.1
    · rw [hB₂.fQ_strCls hc t (by omega), tmulQ_strCls]
      simp only [nextPos, h1, h2, ↓reduceDIte, Option.elim_some]
    · rw [hB₂.fQ_strCls_eq_zero hc t (by omega), tmulQ_zero_right]
      simp only [nextPos, h1, h2, ↓reduceDIte, Option.elim_none]

/-- **Tensor product rule for `ẽ`** ([HK] (4.11)): `ẽ (b₁ ⊗ b₂) = ẽ b₁ ⊗ b₂` if
`φ(b₁) ≥ ε(b₂)`, and `b₁ ⊗ ẽ b₂` otherwise. -/
theorem eTildeQ_tmulQ {b₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)}
    {b₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)} (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂)
    {e₂ φ₁ : ℕ}
    (he : ∀ a, (V₂.eTildeQ hq0 hq hB₂.isKashiwaraStable.eTilde_mem c ^ a) b₂ = 0 ↔ e₂ < a)
    (hφ : ∀ a, (V₁.fTildeQ hq0 hq hB₁.isKashiwaraStable.fTilde_mem c ^ a) b₁ = 0 ↔ φ₁ < a) :
    (tensor V₁ V₂ hq0 hq).eTildeQ hq0 hq
      (hB₁.isCrystalBase_tensor hB₂ hc hϖ hϖq hϖc).isKashiwaraStable.eTilde_mem c
      (hB₁.tmulQ hB₂ hc b₁ b₂) =
      if e₂ ≤ φ₁ then
        hB₁.tmulQ hB₂ hc (V₁.eTildeQ hq0 hq hB₁.isKashiwaraStable.eTilde_mem c b₁) b₂
      else hB₁.tmulQ hB₂ hc b₁ (V₂.eTildeQ hq0 hq hB₂.isKashiwaraStable.eTilde_mem c b₂) := by
  obtain ⟨s, hs⟩ := hB₁.exists_strCls_eq hc b₁ hb₁
  obtain ⟨t, ht⟩ := hB₂.exists_strCls_eq hc b₂ hb₂
  have he' := hB₂.eps_eq hc t ht he
  have hφ' := hB₁.phi_eq hc s hs hφ
  subst hs ht
  rw [tmulQ_strCls, eTildeQ_mk_tensorVec hq0 hq hϖ hϖq (hB₁.hvec_prim hc) (hB₂.hvec_prim hc)
    (hB₁.hvec_ne_zero hc) (hB₂.hvec_ne_zero hc) hϖc, mk_tensorVecOpt hB₁ hB₂ hc]
  have hs2 := s.2.2
  have ht2 := t.2.2
  by_cases h1 : (t.2 : ℕ) ≤ hB₁.hwt hc s.1 - s.2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    by_cases h2 : (s.2 : ℕ) = 0
    · rw [hB₁.eQ_strCls_eq_zero hc s h2, tmulQ_zero_left]
      have h1' : (t.2 : ℕ) ≤ hB₁.hwt hc s.1 := by omega
      simp only [prevPos, h2, h1', Nat.sub_zero, ↓reduceIte, ↓reduceDIte, Option.elim_none]
    · rw [hB₁.eQ_strCls hc s (by omega), tmulQ_strCls]
      simp only [prevPos, h1, h2, ↓reduceIte, ↓reduceDIte, Option.elim_some]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hB₂.eQ_strCls hc t (by omega),
      tmulQ_strCls]
    simp only [prevPos, h1, ↓reduceIte, Option.elim_some]

end Tensor

end IsCrystalBase

/-! ### `q` versus `q⁻¹` on residues -/

section Inv

variable {k : Type*} [Field k] {q : k} {M : Type*} [AddCommGroup M] [Module k M]
  {V : IntegrableSl2 q M} {hq0 : q ≠ 0} {hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  {L : Submodule A M}

lemma inv_eTildeQ (hLe : ∀ m ∈ L, V.eTilde hq0 hq m ∈ L)
    (hLe' : ∀ m ∈ L, V.inv.eTilde (inv_ne_zero hq0) (inv_pow_ne_one hq) m ∈ L) (c : A) :
    V.inv.eTildeQ (inv_ne_zero hq0) (inv_pow_ne_one hq) hLe' c = V.eTildeQ hq0 hq hLe c := by
  refine LinearMap.ext fun b ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [eTildeQ_mk, eTildeQ_mk]
  congr 1
  exact Subtype.ext (show V.inv.eTilde _ _ (x : M) = V.eTilde hq0 hq x by rw [inv_eTilde])

lemma inv_fTildeQ (hLf : ∀ m ∈ L, V.fTilde hq0 hq m ∈ L)
    (hLf' : ∀ m ∈ L, V.inv.fTilde (inv_ne_zero hq0) (inv_pow_ne_one hq) m ∈ L) (c : A) :
    V.inv.fTildeQ (inv_ne_zero hq0) (inv_pow_ne_one hq) hLf' c = V.fTildeQ hq0 hq hLf c := by
  refine LinearMap.ext fun b ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [fTildeQ_mk, fTildeQ_mk]
  congr 1
  exact Subtype.ext (show V.inv.fTilde _ _ (x : M) = V.fTilde hq0 hq x by rw [inv_fTilde])

end Inv

end IntegrableSl2

/-! ### The crystal of `B₁ ⊗ B₂` for integrable `U`-modules -/

lemma IsCrystalBase.e_eq_none_iff {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} {v : k} [NeZero v]
    {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1} {M : Type*} [AddCommGroup M] [Module k M]
    [Module (QuantumGroup R v) M] [IsScalarTower k (QuantumGroup R v) M]
    {hM : IsIntegrable R v M} {A : Type*} [CommRing A] [Algebra A k] [Module A M]
    [IsScalarTower A k M] {L : Submodule A M} {hL : IsCrystalLattice hv hM L} {c : A}
    {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))} (hB : IsCrystalBase hL c B) (i : I)
    (b : B) : hB.e i b = none ↔ hL.eQ c i b.1 = 0 := by
  unfold IsCrystalBase.e
  split_ifs with h <;> simp [h]


namespace TensorModule

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1}
  {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [Module (QuantumGroup R v) M₁]
  [IsScalarTower k (QuantumGroup R v) M₁]
  [AddCommGroup M₂] [Module k M₂] [Module (QuantumGroup R v) M₂]
  [IsScalarTower k (QuantumGroup R v) M₂]
  {h₁ : IsIntegrable R v M₁} {h₂ : IsIntegrable R v M₂}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M₁] [IsScalarTower A k M₁]
  [Module A M₂] [IsScalarTower A k M₂] {L₁ : Submodule A M₁} {L₂ : Submodule A M₂} {c : A}

variable (k) in
/-- The class `β₁ ⊗ β₂ = [x ⊗ y]` (`[x] = β₁`, `[y] = β₂`) in `L₁ ⊗ L₂ / c L₁ ⊗ L₂`. -/
noncomputable def tmulL (β₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))
    (β₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)) :
    lattice k A L₁ L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A (lattice k A L₁ L₂)) :=
  Submodule.Quotient.mk ⟨_, tmul_mem_lattice (k := k)
    (Submodule.Quotient.mk_surjective _ β₁).choose.2
    (Submodule.Quotient.mk_surjective _ β₂).choose.2⟩

lemma tmulL_mk (x : L₁) (y : L₂) :
    tmulL k (Submodule.Quotient.mk x : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))
      (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨_, tmul_mem_lattice (k := k) x.2 y.2⟩ :=
  mk_tmul_eq (Submodule.Quotient.mk_surjective _ _).choose_spec
    (Submodule.Quotient.mk_surjective _ _).choose_spec

omit [IsScalarTower A k M₂] in
lemma tmulL_mem_base {B₁ : Set (L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))}
    {B₂ : Set (L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂))} {b₁ b₂} (hb₁ : b₁ ∈ B₁)
    (hb₂ : b₂ ∈ B₂) : tmulL k b₁ b₂ ∈ base k B₁ B₂ :=
  ⟨_, _, by rw [(Submodule.Quotient.mk_surjective _ b₁).choose_spec]; exact hb₁,
    by rw [(Submodule.Quotient.mk_surjective _ b₂).choose_spec]; exact hb₂, rfl⟩

lemma tmulL_zero_left (β₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)) :
    tmulL k (0 : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)) β₂ = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ β₂
  rw [← Submodule.Quotient.mk_zero, tmulL_mk, ← Submodule.Quotient.mk_zero]
  congr 1
  exact Subtype.ext (by simp)

lemma tmulL_zero_right (β₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)) :
    tmulL k β₁ (0 : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ β₁
  rw [← Submodule.Quotient.mk_zero, tmulL_mk, ← Submodule.Quotient.mk_zero]
  congr 1
  exact Subtype.ext (by simp)

section Crystal

variable [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M₁] [FiniteDimensional k M₂]
  {hL₁ : IsCrystalLattice hv h₁ L₁} {hL₂ : IsCrystalLattice hv h₂ L₂}
  {B₁ : Set (L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))}
  {B₂ : Set (L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂))}
  (hB₁ : IsCrystalBase hL₁ c B₁) (hB₂ : IsCrystalBase hL₂ c B₂) (hc : ¬IsUnit c)
  {ϖ : A} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖv : algebraMap A k ϖ = v⁻¹)
  (hϖc : ϖ ∈ Ideal.span {c})
include hB₁ hB₂ hc

lemma mem_lattice_iff_tensorLattice (i : I) (m : TensorModule k M₁ M₂) :
    m ∈ lattice k A L₁ L₂ ↔ flip M₁ M₂ m ∈ IntegrableSl2.tensorLattice
      (nodeSl2 R v M₂ hv h₂ i).inv (nodeSl2 R v M₁ hv h₁ i).inv
      ((hB₂.isCrystalBase_nodeSl2 i).inv.hwt hc) ((hB₁.isCrystalBase_nodeSl2 i).inv.hwt hc)
      ((hB₂.isCrystalBase_nodeSl2 i).inv.hvec hc) ((hB₁.isCrystalBase_nodeSl2 i).inv.hvec hc)
      A := by
  rw [(hB₂.isCrystalBase_nodeSl2 i).inv.tensorLattice_eq (hB₁.isCrystalBase_nodeSl2 i).inv hc,
    mem_lattice_iff]

lemma quotEquiv_tmulL (i : I) (b₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁))
    (b₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)) :
    IntegrableSl2.quotEquiv (flip M₁ M₂) (mem_lattice_iff_tensorLattice hB₁ hB₂ hc i) c
      (tmulL k b₁ b₂) =
      (hB₂.isCrystalBase_nodeSl2 i).inv.tmulQ (hB₁.isCrystalBase_nodeSl2 i).inv hc b₂ b₁ := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b₁
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b₂
  rw [tmulL_mk, IntegrableSl2.quotEquiv_mk, IntegrableSl2.IsCrystalBase.tmulQ_mk]
  rfl

include hϖ hϖv hϖc

/-- **Tensor product rule for `f̃ᵢ`** on `B₁ ⊗ B₂`: with the library's coproduct,
`f̃ᵢ (b₁ ⊗ b₂) = b₁ ⊗ f̃ᵢ b₂` if `φᵢ(b₂) > εᵢ(b₁)`, and `f̃ᵢ b₁ ⊗ b₂` otherwise. -/
theorem fQ_tmulL (hL : IsCrystalLattice hv (isIntegrable h₁ h₂) (lattice k A L₁ L₂)) (i : I)
    {b₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)}
    {b₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)} (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂)
    {e₁ φ₂ : ℕ} (he : ∀ a, (hL₁.eQ c i ^ a) b₁ = 0 ↔ e₁ < a)
    (hφ : ∀ a, (hL₂.fQ c i ^ a) b₂ = 0 ↔ φ₂ < a) :
    hL.fQ c i (tmulL k b₁ b₂) =
      if e₁ < φ₂ then tmulL k b₁ (hL₂.fQ c i b₂) else tmulL k (hL₁.fQ c i b₁) b₂ := by
  have hϖi : ϖ ^ D.d i ∈ IsLocalRing.maximalIdeal A := Ideal.pow_mem_of_mem _ hϖ _ (D.d_pos i)
  have hϖiv : algebraMap A k (ϖ ^ D.d i) = (v ^ D.d i)⁻¹ := by rw [map_pow, hϖv, inv_pow]
  have hϖic : ϖ ^ D.d i ∈ Ideal.span {c} := Ideal.pow_mem_of_mem _ hϖc _ (D.d_pos i)
  have hW := (hB₂.isCrystalBase_nodeSl2 i).inv.isCrystalBase_tensor
    (hB₁.isCrystalBase_nodeSl2 i).inv hc hϖi hϖiv hϖic
  apply (IntegrableSl2.quotEquiv (flip M₁ M₂) (mem_lattice_iff_tensorLattice hB₁ hB₂ hc i)
    c).injective
  have key := IntegrableSl2.quotEquiv_fTildeQ (flip M₁ M₂)
    (mem_lattice_iff_tensorLattice hB₁ hB₂ hc i) (flip_kashiwaraF hv h₁ h₂ i)
    (hL.kashiwaraF_mem i) hW.isKashiwaraStable.fTilde_mem c (tmulL k b₁ b₂)
  simp only [IsCrystalLattice.fQ]
  rw [key, quotEquiv_tmulL hB₁ hB₂ hc,
    IntegrableSl2.IsCrystalBase.fTildeQ_tmulQ _ _ hc hϖi hϖiv hϖic hb₂ hb₁
      (fun a ↦ by rw [IntegrableSl2.inv_eTildeQ]; exact he a)
      (fun a ↦ by rw [IntegrableSl2.inv_fTildeQ]; exact hφ a)]
  by_cases h : e₁ < φ₂ <;> simp only [h, ↓reduceIte]
  · rw [quotEquiv_tmulL hB₁ hB₂ hc, IntegrableSl2.inv_fTildeQ (hL₂.kashiwaraF_mem i)]
  · rw [quotEquiv_tmulL hB₁ hB₂ hc, IntegrableSl2.inv_fTildeQ (hL₁.kashiwaraF_mem i)]

/-- **Tensor product rule for `ẽᵢ`** on `B₁ ⊗ B₂`: with the library's coproduct,
`ẽᵢ (b₁ ⊗ b₂) = b₁ ⊗ ẽᵢ b₂` if `φᵢ(b₂) ≥ εᵢ(b₁)`, and `ẽᵢ b₁ ⊗ b₂` otherwise. -/
theorem eQ_tmulL (hL : IsCrystalLattice hv (isIntegrable h₁ h₂) (lattice k A L₁ L₂)) (i : I)
    {b₁ : L₁ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₁)}
    {b₂ : L₂ ⧸ (Ideal.span {c} • ⊤ : Submodule A L₂)} (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂)
    {e₁ φ₂ : ℕ} (he : ∀ a, (hL₁.eQ c i ^ a) b₁ = 0 ↔ e₁ < a)
    (hφ : ∀ a, (hL₂.fQ c i ^ a) b₂ = 0 ↔ φ₂ < a) :
    hL.eQ c i (tmulL k b₁ b₂) =
      if e₁ ≤ φ₂ then tmulL k b₁ (hL₂.eQ c i b₂) else tmulL k (hL₁.eQ c i b₁) b₂ := by
  have hϖi : ϖ ^ D.d i ∈ IsLocalRing.maximalIdeal A := Ideal.pow_mem_of_mem _ hϖ _ (D.d_pos i)
  have hϖiv : algebraMap A k (ϖ ^ D.d i) = (v ^ D.d i)⁻¹ := by rw [map_pow, hϖv, inv_pow]
  have hϖic : ϖ ^ D.d i ∈ Ideal.span {c} := Ideal.pow_mem_of_mem _ hϖc _ (D.d_pos i)
  have hW := (hB₂.isCrystalBase_nodeSl2 i).inv.isCrystalBase_tensor
    (hB₁.isCrystalBase_nodeSl2 i).inv hc hϖi hϖiv hϖic
  apply (IntegrableSl2.quotEquiv (flip M₁ M₂) (mem_lattice_iff_tensorLattice hB₁ hB₂ hc i)
    c).injective
  have key := IntegrableSl2.quotEquiv_eTildeQ (flip M₁ M₂)
    (mem_lattice_iff_tensorLattice hB₁ hB₂ hc i) (flip_kashiwaraE hv h₁ h₂ i)
    (hL.kashiwaraE_mem i) hW.isKashiwaraStable.eTilde_mem c (tmulL k b₁ b₂)
  simp only [IsCrystalLattice.eQ]
  rw [key, quotEquiv_tmulL hB₁ hB₂ hc,
    IntegrableSl2.IsCrystalBase.eTildeQ_tmulQ _ _ hc hϖi hϖiv hϖic hb₂ hb₁
      (fun a ↦ by rw [IntegrableSl2.inv_eTildeQ]; exact he a)
      (fun a ↦ by rw [IntegrableSl2.inv_fTildeQ]; exact hφ a)]
  by_cases h : e₁ ≤ φ₂ <;> simp only [h, ↓reduceIte]
  · rw [quotEquiv_tmulL hB₁ hB₂ hc, IntegrableSl2.inv_eTildeQ (hL₂.kashiwaraE_mem i)]
  · rw [quotEquiv_tmulL hB₁ hB₂ hc, IntegrableSl2.inv_eTildeQ (hL₁.kashiwaraE_mem i)]

omit [IsLocalRing A] [IsFractionRing A k] [FiniteDimensional k M₁] [FiniteDimensional k M₂]
  hϖ hϖv hϖc in
lemma wt_tmulL {hL : IsCrystalLattice hv (isIntegrable h₁ h₂) (lattice k A L₁ L₂)}
    (hB : IsCrystalBase hL c (base k B₁ B₂)) (b₁ : B₁) (b₂ : B₂) :
    hB.wt ⟨tmulL k b₁.1 b₂.1, tmulL_mem_base b₁.2 b₂.2⟩ = hB₁.wt b₁ + hB₂.wt b₂ := by
  obtain ⟨x, hx, hxb⟩ := hB₁.exists_mk_eq b₁
  obtain ⟨y, hy, hyb⟩ := hB₂.exists_mk_eq b₂
  refine hB.wt_eq hc _ ⟨_, tmul_mem_lattice x.2 y.2⟩ (tmul_mem_weightSpace hx hy) ?_
  change _ = tmulL k b₁.1 b₂.1
  rw [← hxb, ← hyb, tmulL_mk]

/-- **The crystal of a tensor product** ([HK] Thm. 4.4.1): the crystal of the crystal base
`(L₁ ⊗ L₂, B₁ ⊗ B₂)` of `M₁ ⊗ M₂` is isomorphic to the tensor product (Kashiwara's convention,
`Crystal.tensor`) of the crystals of `B₂` and `B₁`, by `b₂ ⊗ b₁ ↦ [b₁ ⊗ b₂]`; the factors are
exchanged because the library's coproduct is Lusztig's (`I` nonempty). -/
theorem nonempty_crystalEquiv [Nonempty I]
    (hL : IsCrystalLattice hv (isIntegrable h₁ h₂) (lattice k A L₁ L₂))
    (hB : IsCrystalBase hL c (base k B₁ B₂)) :
    Nonempty (Crystal.Equiv ((hB₂.crystal hc).tensor (hB₁.crystal hc)) (hB.crystal hc)) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  let Φ : B₂ × B₁ → base k B₁ B₂ := fun p ↦ ⟨tmulL k p.2.1 p.1.1, tmulL_mem_base p.2.2 p.1.2⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨b₂, b₁⟩ ⟨b₂', b₁'⟩ h
    have h' := congrArg (IntegrableSl2.quotEquiv (flip M₁ M₂)
      (mem_lattice_iff_tensorLattice hB₁ hB₂ hc i₀) c) (congrArg Subtype.val h)
    simp only [Φ, quotEquiv_tmulL hB₁ hB₂ hc] at h'
    obtain ⟨e2, e1⟩ := IntegrableSl2.IsCrystalBase.tmulQ_injective _ _ hc b₂.2 b₂'.2 b₁.2 b₁'.2 h'
    exact Prod.ext (Subtype.ext e2) (Subtype.ext e1)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨b, x, y, hx, hy, rfl⟩
    exact ⟨(⟨_, hy⟩, ⟨_, hx⟩), Subtype.ext (tmulL_mk x y)⟩
  refine ⟨Crystal.equivOfE ((hB₂.isSeminormal_crystal hc).tensor (hB₁.isSeminormal_crystal hc))
    (hB.isSeminormal_crystal hc) (Equiv.ofBijective Φ ⟨hinj, hsurj⟩) ?_ ?_⟩
  · rintro ⟨b₂, b₁⟩
    change hB.wt (Φ (b₂, b₁)) = hB₂.wt b₂ + hB₁.wt b₁
    rw [wt_tmulL hB₁ hB₂ hc hB, add_comm]
  · rintro i ⟨b₂, b₁⟩
    obtain ⟨φ₂, hφ₂⟩ : ∃ n : ℕ, (hB₂.eps hc i b₂ : ℤ) + hB₂.wt b₂ (R.coroot i) = n := by
      have h0 := (hB₂.isSeminormal_crystal hc).φ_nonneg i b₂
      change ((0 : ℤ) : WithBot ℤ) ≤ (((hB₂.eps hc i b₂ : ℤ) + hB₂.wt b₂ (R.coroot i) : ℤ) :
        WithBot ℤ) at h0
      rw [WithBot.coe_le_coe] at h0
      exact ⟨_, (Int.toNat_of_nonneg h0).symm⟩
    have hφ : ∀ a, (hL₂.fQ c i ^ a) b₂.1 = 0 ↔ φ₂ < a := fun a ↦ by
      rw [hB₂.fQ_pow_eq_zero_iff hc i b₂ a, hφ₂]
      norm_cast
    have key := eQ_tmulL hB₁ hB₂ hc hϖ hϖv hϖc hL i b₁.2 b₂.2
      (hB₁.eQ_pow_eq_zero_iff hc i b₁) hφ
    have hcond : ((hB₁.crystal hc).ε i b₁ ≤ (hB₂.crystal hc).φ i b₂) ↔
        hB₁.eps hc i b₁ ≤ φ₂ := by
      change (((hB₁.eps hc i b₁ : ℤ)) : WithBot ℤ) ≤
        (((hB₂.eps hc i b₂ : ℤ) + hB₂.wt b₂ (R.coroot i) : ℤ) : WithBot ℤ) ↔ _
      rw [hφ₂, WithBot.coe_le_coe]
      norm_cast
    change hB.e i (Φ (b₂, b₁)) = ((hB₂.crystal hc).tensor (hB₁.crystal hc) |>.e i (b₂, b₁)).map Φ
    by_cases h : hB₁.eps hc i b₁ ≤ φ₂
    · simp only [h, ↓reduceIte] at key
      have ht : ((hB₂.crystal hc).tensor (hB₁.crystal hc)).e i (b₂, b₁) =
          ((hB₂.crystal hc).e i b₂).map (·, b₁) := by
        simp only [Crystal.tensor, hcond.2 h, ↓reduceIte]
      rw [ht, IsCrystalBase.crystal_e]
      by_cases h0 : hL₂.eQ c i b₂.1 = 0
      · rw [(hB₂.e_eq_none_iff i b₂).2 h0, Option.map_none, Option.map_none,
          hB.e_eq_none_iff i]
        change hL.eQ c i (tmulL k b₁.1 b₂.1) = 0
        rw [key, h0, tmulL_zero_right]
      · rw [(hB₂.e_eq_some_iff hc i b₂ ⟨_, hB₂.eQ_mem_of_ne i b₂ h0⟩).2 rfl, Option.map_some,
          Option.map_some, hB.e_eq_some_iff hc]
        exact key
    · simp only [h, ↓reduceIte] at key
      have ht : ((hB₂.crystal hc).tensor (hB₁.crystal hc)).e i (b₂, b₁) =
          ((hB₁.crystal hc).e i b₁).map (b₂, ·) := by
        simp only [Crystal.tensor, mt hcond.1 h, ↓reduceIte]
      rw [ht, IsCrystalBase.crystal_e]
      by_cases h0 : hL₁.eQ c i b₁.1 = 0
      · rw [(hB₁.e_eq_none_iff i b₁).2 h0, Option.map_none, Option.map_none,
          hB.e_eq_none_iff i]
        change hL.eQ c i (tmulL k b₁.1 b₂.1) = 0
        rw [key, h0, tmulL_zero_left]
      · rw [(hB₁.e_eq_some_iff hc i b₁ ⟨_, hB₁.eQ_mem_of_ne i b₁ h0⟩).2 rfl, Option.map_some,
          Option.map_some, hB.e_eq_some_iff hc]
        exact key

end Crystal

end TensorModule

end LieLean.QuantumGroup
