/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CharacterRing
import LieLean.Algebra.Lie.KacMoody.Super.GabberKac.VermaWeights

/-!
# Expansion of characters in Verma characters

Let `V` be a `G(A, τ)`-module whose weights lie in finitely many cones `Λ - Q₊`, with
finite-dimensional weight spaces, on which the Casimir operator acts by a scalar `c`. Then, above
any weight `ν`, the character of `V` is an integral combination of characters of Verma modules
`M̄(κ)` with `(κ + 2ρ | κ) = c`: there are integers `a_κ` with
`dim V_μ = ∑_κ a_κ dim M̄(κ)_μ` for all `μ ≥ ν` (`IsCasimirModule.exists_expansion`). This is the
form of [Kac78] §2 (cf. [Kac] Prop. 9.7 and §9.8) used in the proof of the super Gabber–Kac
theorem. The proof is by induction: a maximal weight vector `v` defines a map `M̄(μ₀) → V`, and
both its kernel and its cokernel are again of this type; the kernel lives strictly below `μ₀`.

## Main definitions

* `Matrix.Realization.SuperEnveloping.IsCasimirModule`: the hypotheses above.

## Main results

* `Matrix.Realization.SuperEnveloping.IsCasimirModule.exists_expansion`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §9.7–9.8.
-/

universe u v w

open Module Matrix.Realization.WeightOrd

noncomputable section

namespace Matrix.Realization.SuperEnveloping

variable {ι : Type u} {K : Type v} {H : Type w} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup H] [Module K H] {A : Matrix ι ι ℤ} {P : Realization A K H} {p : ι → ZMod 2}
  [CharZero K]

/-- The enveloping superalgebra `U(G̃(A, τ))`. -/
local notation "𝒰" => SuperEnveloping P p

omit [DecidableEq ι] in
variable (P) in
/-- Only finitely many weights lie above `ν` and in one of finitely many cones. -/
lemma finite_setOf_le_le (Λs : Finset (Dual K H)) (ν : Dual K H) :
    {κ | (∃ Λ ∈ Λs, toWeightOrd P Λ ≤ toWeightOrd P κ) ∧
      toWeightOrd P κ ≤ toWeightOrd P ν}.Finite := by
  classical
  let c : Dual K H → ι → ℤ := fun Λ ↦
    if hc : ∃ c, P.rootOf c = Λ - ν then hc.choose else 0
  refine (Λs.finite_toSet.biUnion fun Λ _ ↦ ((Set.Finite.pi (t := fun i ↦ Set.Icc 0 (c Λ i))
    fun i ↦ Set.finite_Icc _ _).image fun d ↦ Λ - P.rootOf d)).subset ?_
  rintro κ ⟨⟨Λ, hΛ, hΛκ⟩, hκν⟩
  obtain ⟨d, hd, rfl⟩ := (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).1 hΛκ
  obtain ⟨e, he, hκ⟩ := (toWeightOrd_le_iff P).1 hκν
  have hld : P.rootOf (d + e) = Λ - ν := by
    rw [map_add, ← hκ]
    abel
  have hex : ∃ c, P.rootOf c = Λ - ν := ⟨_, hld⟩
  have hc : c Λ = d + e := P.rootOf_injective (by
    simp only [c, hex, ↓reduceDIte]
    rw [hex.choose_spec, hld])
  refine Set.mem_biUnion hΛ ⟨d, fun i _ ↦ ⟨hd i, ?_⟩, rfl⟩
  rw [hc, Pi.add_apply, le_add_iff_nonneg_right]
  exact he i

section Module

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (P.SuperEnveloping p) V]
  [IsScalarTower K (P.SuperEnveloping p) V]

omit [CharZero K] in
/-- A module which is the sum of its weight spaces, with weights in the cones `Λ - Q₊`,
`Λ ∈ Λs`, is bounded. -/
lemma isBounded_of_iSup {Λs : Finset (Dual K H)} (hV : ⨆ μ, modWeightSpace P p V μ = ⊤)
    (hc : ∀ μ, modWeightSpace P p V μ ≠ ⊥ → ∃ Λ ∈ Λs, ∃ d : ι → ℤ, 0 ≤ d ∧ μ = Λ - P.rootOf d) :
    IsBounded P p V Λs := by
  intro v
  have hv : v ∈ ⨆ μ, modWeightSpace P p V μ := hV ▸ Submodule.mem_top
  rw [Submodule.iSup_eq_span] at hv
  refine Submodule.span_le.2 (fun w hw ↦ ?_) hv
  obtain ⟨μ, hw⟩ := Set.mem_iUnion.1 hw
  by_cases h0 : w = 0
  · rw [h0]
    exact Submodule.zero_mem _
  obtain ⟨Λ, hΛ, d, hd, hμ⟩ := hc μ ((Submodule.ne_bot_iff _).2 ⟨w, hw, h0⟩)
  exact Submodule.subset_span ⟨Λ, hΛ, d, hd, hμ ▸ hw⟩

variable (N : Submodule (P.SuperEnveloping p) V)

omit [CharZero K] in
lemma finiteDimensional_modWeightSpace_quotient (hV : ⨆ μ, modWeightSpace P p V μ = ⊤)
    (μ : Dual K H) [FiniteDimensional K (modWeightSpace P p V μ)] :
    FiniteDimensional K (modWeightSpace P p (V ⧸ N) μ) := by
  rw [modWeightSpace_quotient N hV]
  infer_instance

omit [CharZero K] in
lemma finiteDimensional_modWeightSpace_submodule (μ : Dual K H)
    [FiniteDimensional K (modWeightSpace P p V μ)] :
    FiniteDimensional K (modWeightSpace P p N μ) := by
  have e := Submodule.equivMapOfInjective (N.subtype.restrictScalars K)
    (fun x y h ↦ Subtype.ext h) (modWeightSpace P p N μ)
  rw [map_modWeightSpace_submodule] at e
  have : FiniteDimensional K ↥(modWeightSpace P p V μ ⊓ N.restrictScalars K) :=
    Submodule.finiteDimensional_of_le inf_le_left
  exact Module.Finite.equiv e.symm

end Module

variable [FiniteDimensional K H]

variable (P p) in
/-- The hypotheses of the expansion theorem: `V` is a `G(A, τ)`-module with weights in the cones
`Λ - Q₊`, `Λ ∈ Λs`, finite-dimensional weight spaces, on which the Casimir operator acts by the
scalar `c`. -/
structure IsCasimirModule (S : A.Symmetrization) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (P.SuperEnveloping p) V] [IsScalarTower K (P.SuperEnveloping p) V]
    (Λs : Finset (Dual K H)) (c : K) : Prop where
  isGModule : IsGModule P p V
  isBounded : IsBounded P p V Λs
  finiteDimensional : ∀ μ, FiniteDimensional K (modWeightSpace P p V μ)
  casimir_eq : ∀ v, casimir S isBounded.isPosFinite v = c • v

namespace IsCasimirModule

variable {S : A.Symmetrization} {Λs : Finset (Dual K H)} {c : K}

section Module

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (P.SuperEnveloping p) V]
  [IsScalarTower K (P.SuperEnveloping p) V]

/-- Quotients. -/
lemma quotient (hV : IsCasimirModule P p S V Λs c) (N : Submodule (P.SuperEnveloping p) V) :
    IsCasimirModule P p S (V ⧸ N) Λs c where
  isGModule r hr x := by
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    rw [← map_smul, hV.isGModule r hr y, map_zero]
  isBounded := hV.isBounded.of_surjective N.mkQ N.mkQ_surjective
  finiteDimensional μ := by
    have := hV.finiteDimensional μ
    exact finiteDimensional_modWeightSpace_quotient N hV.isBounded.iSup_modWeightSpace_eq_top μ
  casimir_eq x := by
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    rw [← map_casimir S hV.isBounded.isPosFinite, hV.casimir_eq y, LinearMap.map_smul_of_tower]

/-- Submodules. -/
lemma submodule (hV : IsCasimirModule P p S V Λs c) (N : Submodule (P.SuperEnveloping p) V) :
    IsCasimirModule P p S N Λs c where
  isGModule r hr x := Subtype.ext (hV.isGModule r hr x)
  isBounded := isBounded_of_iSup
    (iSup_modWeightSpace_submodule N hV.isBounded.iSup_modWeightSpace_eq_top) fun μ hμ ↦ by
      obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hμ
      refine hV.isBounded.exists_eq_sub (w := (x : V)) (fun a ↦ ?_)
        fun h ↦ hx0 (Subtype.ext h)
      simpa using congr_arg Subtype.val (hx a)
  finiteDimensional μ := by
    have := hV.finiteDimensional μ
    exact finiteDimensional_modWeightSpace_submodule N μ
  casimir_eq x := Subtype.ext (by
    rw [← N.subtype_apply, map_casimir S _ hV.isBounded.isPosFinite, N.subtype_apply,
      hV.casimir_eq]
    rfl)

end Module

section Expansion

variable (hA : A.IsGeneralizedCartan)

include hA in
/-- The Verma module `M̄(μ₀)`, for `μ₀` in one of the cones. -/
lemma gVerma {μ₀ : Dual K H} (hμ₀ : ∃ Λ ∈ Λs, toWeightOrd P Λ ≤ toWeightOrd P μ₀) :
    IsCasimirModule P p S (GVerma P p μ₀) Λs (P.dualBilinForm S (μ₀ + 2 • P.rho) μ₀) where
  isGModule := GVerma.isGModule
  isBounded := isBounded_of_iSup GVerma.isBounded.iSup_modWeightSpace_eq_top fun μ hμ ↦ by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hμ
    obtain ⟨Λ', hΛ', d, hd, rfl⟩ := GVerma.isBounded.exists_eq_sub hx hx0
    rw [Finset.mem_singleton] at hΛ'
    subst hΛ'
    obtain ⟨Λ, hΛ, hΛμ⟩ := hμ₀
    obtain ⟨d', hd', rfl⟩ := (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).1 hΛμ
    exact ⟨Λ, hΛ, d' + d, add_nonneg hd' hd, by rw [map_add]; abel⟩
  finiteDimensional _ := inferInstance
  casimir_eq v := casimir_eq_smul_of_forall_eq_smul GVerma.isGModule _ hA
    (fun a ↦ GVerma.h_smul_hwv a) GVerma.e_smul_hwv
    (fun w ↦ by obtain ⟨t, ht⟩ := GVerma.exists_eq_fAlg_smul_hwv w; exact ⟨_, ht.symm⟩) v

include hA in
/-- The inductive step of `exists_expansion`, for a finite set `F` of weights closed upwards
inside the cones: induction on the set `T` of weights below a nonzero weight space in `F`, then
on the total dimension of the weight spaces in `F`. -/
private theorem expansion_aux (F : Finset (Dual K H))
    (hF : ∀ κ μ, κ ∈ F → toWeightOrd P μ ≤ toWeightOrd P κ →
      (∃ Λ ∈ Λs, toWeightOrd P Λ ≤ toWeightOrd P μ) → μ ∈ F)
    (T : Finset (Dual K H)) (n : ℕ) (V : Type (max u v w)) [AddCommGroup V] [Module K V]
    [Module (P.SuperEnveloping p) V] [IsScalarTower K (P.SuperEnveloping p) V]
    (hV : IsCasimirModule P p S V Λs c)
    (hT : ∀ κ ∈ F, (∃ μ ∈ F, modWeightSpace P p V μ ≠ ⊥ ∧ toWeightOrd P μ ≤ toWeightOrd P κ) →
      κ ∈ T)
    (hn : ∑ μ ∈ F, finrank K (modWeightSpace P p V μ) = n) :
    ∃ a : Dual K H →₀ ℤ, (∀ κ ∈ a.support, P.dualBilinForm S (κ + 2 • P.rho) κ = c ∧ κ ∈ F) ∧
      ∀ μ ∈ F, (finrank K (modWeightSpace P p V μ) : ℤ) =
        a.sum fun κ m ↦ m * (GVerma.vermaDim P p (κ - μ) : ℤ) := by
  induction T using Finset.strongInduction generalizing n V with
  | H T ihT =>
  induction n using Nat.strong_induction_on generalizing V with
  | _ n ihn =>
  classical
  by_cases hall : ∀ μ ∈ F, modWeightSpace P p V μ = ⊥
  · refine ⟨0, by simp, fun μ hμ ↦ ?_⟩
    rw [Finsupp.sum_zero_index, hall μ hμ, finrank_bot, Nat.cast_zero]
  push Not at hall
  -- a maximal nonzero weight space in `F`
  have hfin : (toWeightOrd P '' {μ | μ ∈ F ∧ modWeightSpace P p V μ ≠ ⊥}).Finite :=
    (F.finite_toSet.subset fun μ hμ ↦ hμ.1).image _
  obtain ⟨_, ⟨μ₀, ⟨hμ₀F, hne⟩, rfl⟩, hmin⟩ := hfin.isPWO.exists_minimal
    (hall.imp fun μ hμ ↦ ⟨_, hμ, rfl⟩)
  have hmin' : ∀ μ ∈ F, modWeightSpace P p V μ ≠ ⊥ → toWeightOrd P μ ≤ toWeightOrd P μ₀ →
      μ = μ₀ := fun μ hμ hμne hle ↦
    (toWeightOrd P).injective (le_antisymm hle (hmin ⟨μ, ⟨hμ, hμne⟩, rfl⟩ hle))
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨Λ₀, hΛ₀, d₀, hd₀, hμ₀⟩ := hV.isBounded.exists_eq_sub hv hv0
  have hcone : ∃ Λ ∈ Λs, toWeightOrd P Λ ≤ toWeightOrd P μ₀ :=
    ⟨Λ₀, hΛ₀, (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).2 ⟨d₀, hd₀, hμ₀⟩⟩
  -- `v` is a highest weight vector
  have he : ∀ i, e P p i • v = 0 := by
    intro i
    by_contra h0
    have hmem := smul_mem_modWeightSpace V (e_mem_weightSpace P p i) hv
    obtain ⟨Λ, hΛ, d, hd, heq⟩ := hV.isBounded.exists_eq_sub hmem h0
    have hup : toWeightOrd P (P.root i + μ₀) ≤ toWeightOrd P μ₀ :=
      (toWeightOrd_le_iff P).2 ⟨Pi.single i 1, Pi.single_nonneg.2 zero_le_one, by simp⟩
    have hF' : P.root i + μ₀ ∈ F := hF μ₀ _ hμ₀F hup
      ⟨Λ, hΛ, (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).2 ⟨d, hd, heq⟩⟩
    have h1 := hmin' _ hF' ((Submodule.ne_bot_iff _).2 ⟨_, hmem, h0⟩) hup
    rw [add_eq_right, ← rootOf_single, ← map_zero P.rootOf] at h1
    simpa using congr_fun (P.rootOf_injective h1) i
  have hh : ∀ a, h P p a • v = algebraMap K (P.SuperEnveloping p) (μ₀ a) • v := fun a ↦ by
    rw [algebraMap_smul]
    exact hv a
  set φ := GVerma.lift hV.isGModule v he hh
  have hφ : φ (GVerma.hwv P p μ₀) = v := GVerma.lift_hwv _ _ _ _
  -- the Casimir scalar
  have hc0 : P.dualBilinForm S (μ₀ + 2 • P.rho) μ₀ = c := by
    have h1 := casimir_apply_of_e_smul_eq_zero (S := S) hV.isBounded.isPosFinite hV.isGModule hv he
    rw [hV.casimir_eq] at h1
    exact (smul_left_injective K hv0 h1).symm
  have hVerma : IsCasimirModule P p S (GVerma P p μ₀) Λs c := hc0 ▸ gVerma hA hcone
  -- the kernel
  set Kr := LinearMap.ker φ
  have hKr := hVerma.submodule Kr
  have hKr0 : modWeightSpace P p Kr μ₀ = ⊥ := by
    refine eq_bot_iff.2 fun x hx ↦ ?_
    have hx' : (x : GVerma P p μ₀) ∈ modWeightSpace P p (GVerma P p μ₀) μ₀ := fun a ↦ by
      simpa using congr_arg Subtype.val (hx a)
    rw [GVerma.modWeightSpace_self, Submodule.mem_span_singleton] at hx'
    obtain ⟨t, ht⟩ := hx'
    have hx0 : φ x = 0 := x.2
    rw [← ht, LinearMap.map_smul_of_tower, hφ, smul_eq_zero] at hx0
    rw [Submodule.mem_bot]
    refine Subtype.ext ?_
    rw [← ht, hx0.resolve_right hv0, zero_smul]
    rfl
  have hμ₀T : μ₀ ∈ T := hT μ₀ hμ₀F ⟨μ₀, hμ₀F, hne, le_rfl⟩
  obtain ⟨aK, haK, haK'⟩ := ihT (T.erase μ₀) (Finset.erase_ssubset hμ₀T) _ Kr hKr
    (fun κ hκF ⟨μ, hμF, hμne, hμκ⟩ ↦ by
      obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hμne
      have hx' : (x : GVerma P p μ₀) ∈ modWeightSpace P p (GVerma P p μ₀) μ :=
        fun a ↦ by simpa using congr_arg Subtype.val (hx a)
      obtain ⟨Λ', hΛ', d, hd, hμd⟩ := GVerma.isBounded.exists_eq_sub hx'
        fun h ↦ hx0 (Subtype.ext h)
      rw [Finset.mem_singleton.1 hΛ'] at hμd
      have hle : toWeightOrd P μ₀ ≤ toWeightOrd P μ :=
        (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).2 ⟨d, hd, hμd⟩
      have hneq : μ ≠ μ₀ := fun h ↦ hμne (h ▸ hKr0)
      have hlt : toWeightOrd P μ₀ < toWeightOrd P κ :=
        (lt_of_le_of_ne hle fun h ↦ hneq ((toWeightOrd P).injective h).symm).trans_le hμκ
      exact Finset.mem_erase.2 ⟨fun h ↦ hlt.ne (by rw [h]),
        hT κ hκF ⟨μ₀, hμ₀F, hne, hlt.le⟩⟩) rfl
  -- the cokernel
  set R := LinearMap.range φ
  have hQ := hV.quotient R
  have htop := hV.isBounded.iSup_modWeightSpace_eq_top
  have hsplit : ∀ μ, finrank K (modWeightSpace P p V μ) =
      finrank K (modWeightSpace P p R μ) + finrank K (modWeightSpace P p (V ⧸ R) μ) :=
    fun μ ↦ by
      have := hV.finiteDimensional μ
      exact finrank_modWeightSpace_eq_add R htop μ
  have hR0 : 0 < finrank K (modWeightSpace P p R μ₀) := by
    have := hV.finiteDimensional μ₀
    have := finiteDimensional_modWeightSpace_submodule R μ₀
    refine Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨⟨v, GVerma.hwv P p μ₀, hφ⟩, fun a ↦ Subtype.ext (hv a)⟩, fun h ↦ hv0 ?_⟩
    simpa using congr_arg (fun x : modWeightSpace P p R μ₀ ↦ ((x : R) : V)) h
  obtain ⟨aQ, haQ, haQ'⟩ := ihn _ (hn ▸ Finset.sum_lt_sum (fun μ _ ↦ by rw [hsplit μ]; omega)
      ⟨μ₀, hμ₀F, by rw [hsplit μ₀]; omega⟩) (V ⧸ R) hQ
    (fun κ hκF ⟨μ, hμF, hμne, hμκ⟩ ↦ hT κ hκF ⟨μ, hμF, fun h0 ↦ hμne (by
      rw [modWeightSpace_quotient R htop, h0, Submodule.map_bot]), hμκ⟩) rfl
  -- combine
  refine ⟨aQ + Finsupp.single μ₀ 1 - aK, fun κ hκ ↦ ?_, fun μ hμF ↦ ?_⟩
  · have : κ ∈ aQ.support ∨ κ = μ₀ ∨ κ ∈ aK.support := by
      by_contra hcon
      push Not at hcon
      apply Finsupp.mem_support_iff.1 hκ
      rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.notMem_support_iff.1 hcon.1,
        Finsupp.notMem_support_iff.1 hcon.2.2, Finsupp.single_eq_of_ne hcon.2.1]
      simp
    rcases this with h | rfl | h
    · exact haQ κ h
    · exact ⟨hc0, hμ₀F⟩
    · exact haK κ h
  · have e2 := finrank_modWeightSpace_eq_add Kr
      GVerma.isBounded.iSup_modWeightSpace_eq_top μ
    have e3 : finrank K (modWeightSpace P p (GVerma P p μ₀ ⧸ Kr) μ) =
        finrank K (modWeightSpace P p R μ) :=
      finrank_modWeightSpace_equiv (LinearMap.quotKerEquivRange φ) μ
    have e4 := GVerma.finrank_modWeightSpace (P := P) (p := p) (Λ := μ₀) μ
    rw [Finsupp.sum_sub_index (fun _ _ _ ↦ sub_mul _ _ _),
      Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _),
      Finsupp.sum_single_index (zero_mul _), ← haQ' μ hμF, ← haK' μ hμF, hsplit μ]
    omega

include hA in
/-- **Expansion in Verma characters** ([Kac78] §2, cf. [Kac] Prop. 9.7): if the Casimir operator
acts by `c` on `V`, then above any weight `ν` the character of `V` is an integral combination of
characters of Verma modules `M̄(κ)` with `(κ + 2ρ | κ) = c` and `κ` in the cones. -/
theorem exists_expansion {V : Type (max u v w)} [AddCommGroup V] [Module K V]
    [Module (P.SuperEnveloping p) V] [IsScalarTower K (P.SuperEnveloping p) V]
    (hV : IsCasimirModule P p S V Λs c) (ν : Dual K H) :
    ∃ a : Dual K H →₀ ℤ, (∀ κ ∈ a.support, P.dualBilinForm S (κ + 2 • P.rho) κ = c ∧
        ∃ Λ ∈ Λs, toWeightOrd P Λ ≤ toWeightOrd P κ) ∧
      ∀ μ, toWeightOrd P μ ≤ toWeightOrd P ν →
        (finrank K (modWeightSpace P p V μ) : ℤ) =
          a.sum fun κ m ↦ m * (GVerma.vermaDim P p (κ - μ) : ℤ) := by
  classical
  set F := (finite_setOf_le_le P Λs ν).toFinset
  have hmemF : ∀ κ, κ ∈ F ↔ (∃ Λ ∈ Λs, toWeightOrd P Λ ≤ toWeightOrd P κ) ∧
      toWeightOrd P κ ≤ toWeightOrd P ν := fun κ ↦ Set.Finite.mem_toFinset _
  have hF : ∀ κ μ, κ ∈ F → toWeightOrd P μ ≤ toWeightOrd P κ →
      (∃ Λ ∈ Λs, toWeightOrd P Λ ≤ toWeightOrd P μ) → μ ∈ F := fun κ μ hκ hμκ hμ ↦
    (hmemF μ).2 ⟨hμ, hμκ.trans ((hmemF κ).1 hκ).2⟩
  obtain ⟨a, ha, haF⟩ := expansion_aux hA F hF F _ V hV (fun κ hκ _ ↦ hκ) rfl
  refine ⟨a, fun κ hκ ↦ ⟨(ha κ hκ).1, ((hmemF κ).1 (ha κ hκ).2).1⟩, fun μ hμ ↦ ?_⟩
  by_cases hμF : μ ∈ F
  · exact haF μ hμF
  have h0 : modWeightSpace P p V μ = ⊥ := by
    by_contra hne
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
    obtain ⟨Λ, hΛ, d, hd, heq⟩ := hV.isBounded.exists_eq_sub hx hx0
    exact hμF ((hmemF μ).2
      ⟨⟨Λ, hΛ, (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).2 ⟨d, hd, heq⟩⟩, hμ⟩)
  rw [h0, finrank_bot, Nat.cast_zero, Finsupp.sum]
  refine (Finset.sum_eq_zero fun κ hκ ↦ ?_).symm
  have hd : GVerma.vermaDim P p (κ - μ) = 0 := by
    by_contra hne
    obtain ⟨d, hd, heq⟩ := GVerma.exists_eq_rootOf_of_vermaDim_ne_zero hne
    obtain ⟨⟨Λ, hΛ, hΛκ⟩, -⟩ := (hmemF κ).1 (ha κ hκ).2
    refine hμF ((hmemF μ).2 ⟨⟨Λ, hΛ, hΛκ.trans ?_⟩, hμ⟩)
    exact (toWeightOrd_le_toWeightOrd_iff_exists_eq_sub P).2 ⟨d, hd, by rw [← heq, sub_sub_cancel]⟩
  rw [hd, Nat.cast_zero, mul_zero]

end Expansion

end IsCasimirModule

end Matrix.Realization.SuperEnveloping
