/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.Serre

/-!
# The Kac–Moody algebra `𝔤(A)`

For a square integer matrix `A` with realization `(𝔥, Π, Π^∨)` over a field `K` of characteristic
zero, the Lie algebra `𝔤(A)` is the quotient of the auxiliary Lie algebra `𝔤̃(A)` by its maximal
ideal `𝔯` meeting `𝔥` trivially ([Kac] §1.3).

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra`: the Lie algebra `𝔤(A) = 𝔤̃(A)/𝔯`.
* `Matrix.Realization.KacMoodyAlgebra.e`, `f`, `h`: the Chevalley generators and `𝔥 → 𝔤(A)`.
* `Matrix.Realization.KacMoodyAlgebra.rootSpace`: the root space `𝔤_μ`.
* `Matrix.Realization.KacMoodyAlgebra.chevalleyInvolution`: the Chevalley involution of `𝔤(A)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.h_injective`: `𝔥 ↪ 𝔤(A)`.
* `Matrix.Realization.KacMoodyAlgebra.triangular_eq_zero`,
  `Matrix.Realization.KacMoodyAlgebra.exists_triangular`: the triangular decomposition
  `𝔤(A) = 𝔫₋ ⊕ 𝔥 ⊕ 𝔫₊`.
* `Matrix.Realization.KacMoodyAlgebra.rootSpace_eq_map`: `𝔤_μ` is the image of `𝔤̃_μ`; hence
  `𝔤_0 = 𝔥` (`rootSpace_zero`), `dim 𝔤_α < ∞` for `α ≠ 0`, `𝔤_{αᵢ} = K eᵢ` with `eᵢ ≠ 0`
  (`finrank_rootSpace_root`), and `𝔤_{k αᵢ} = 0` for `k ≥ 2` (`rootSpace_nsmul_root_eq_bot`).
* `Matrix.Realization.KacMoodyAlgebra.serre_e`, `serre_f`: for a generalized Cartan matrix, the
  Serre relations `(ad eᵢ)^{1 - aᵢⱼ} eⱼ = 0 = (ad fᵢ)^{1 - aᵢⱼ} fⱼ` (`i ≠ j`) hold in `𝔤(A)`
  ([Kac] §3.3).

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, §1.2–1.3, §3.3.
-/

open FreeLieAlgebra Module LieModule LieAlgebra

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

/-- The Kac–Moody algebra `𝔤(A) = 𝔤̃(A)/𝔯` of [Kac] §1.3. -/
abbrev KacMoodyAlgebra : Type _ := P.AuxLieAlgebra ⧸ AuxLieAlgebra.maxIdeal P

namespace KacMoodyAlgebra

/-- The quotient map `𝔤̃(A) → 𝔤(A)`. -/
def π : P.AuxLieAlgebra →ₗ⁅K⁆ P.KacMoodyAlgebra := LieIdeal.mkHom _

lemma π_surjective : Function.Surjective (π P) := LieIdeal.mkHom_surjective _

lemma π_eq_zero_iff {x : P.AuxLieAlgebra} : π P x = 0 ↔ x ∈ AuxLieAlgebra.maxIdeal P :=
  LieIdeal.mkHom_eq_zero_iff _

/-- The generator `eᵢ` of `𝔤(A)`. -/
def e (i : ι) : P.KacMoodyAlgebra := π P (AuxLieAlgebra.e P i)

/-- The generator `fᵢ` of `𝔤(A)`. -/
def f (i : ι) : P.KacMoodyAlgebra := π P (AuxLieAlgebra.f P i)

/-- The embedding `𝔥 → 𝔤(A)`. -/
def h : H →ₗ[K] P.KacMoodyAlgebra := (π P).toLinearMap ∘ₗ AuxLieAlgebra.h P

@[simp] lemma π_e (i : ι) : π P (AuxLieAlgebra.e P i) = e P i := rfl
@[simp] lemma π_f (i : ι) : π P (AuxLieAlgebra.f P i) = f P i := rfl
@[simp] lemma π_h (a : H) : π P (AuxLieAlgebra.h P a) = h P a := rfl

lemma lie_h_h (a b : H) : ⁅h P a, h P b⁆ = 0 := by
  rw [← π_h, ← π_h, ← LieHom.map_lie, AuxLieAlgebra.lie_h_h, map_zero]

lemma lie_e_f (i j : ι) : ⁅e P i, f P j⁆ = if i = j then h P (P.coroot i) else 0 := by
  rw [← π_e, ← π_f, ← LieHom.map_lie, AuxLieAlgebra.lie_e_f]
  split_ifs <;> simp

@[simp] lemma lie_e_f_self (i : ι) : ⁅e P i, f P i⁆ = h P (P.coroot i) := by
  simp [lie_e_f]

lemma lie_e_f_of_ne {i j : ι} (hij : i ≠ j) : ⁅e P i, f P j⁆ = 0 := by
  simp [lie_e_f, hij]

lemma lie_h_e (a : H) (i : ι) : ⁅h P a, e P i⁆ = P.root i a • e P i := by
  rw [← π_h, ← π_e, ← LieHom.map_lie, AuxLieAlgebra.lie_h_e, map_smul]

lemma lie_h_f (a : H) (i : ι) : ⁅h P a, f P i⁆ = -(P.root i a • f P i) := by
  rw [← π_h, ← π_f, ← LieHom.map_lie, AuxLieAlgebra.lie_h_f, map_neg, map_smul]

/-- The morphism from the free Lie algebra on `ι` onto `𝔫₋ ⊆ 𝔤(A)`. -/
def fHom : FreeLieAlgebra K ι →ₗ⁅K⁆ P.KacMoodyAlgebra := (π P).comp (AuxLieAlgebra.fHom P)

/-- The morphism from the free Lie algebra on `ι` onto `𝔫₊ ⊆ 𝔤(A)`. -/
def eHom : FreeLieAlgebra K ι →ₗ⁅K⁆ P.KacMoodyAlgebra := (π P).comp (AuxLieAlgebra.eHom P)

@[simp] lemma fHom_of (i : ι) : fHom P (FreeLieAlgebra.of K i) = f P i := by simp [fHom]
@[simp] lemma eHom_of (i : ι) : eHom P (FreeLieAlgebra.of K i) = e P i := by simp [eHom]

/-- Every element of `𝔤(A)` is of the form `n₋ + h + n₊` ([Kac] §1.3). -/
lemma exists_triangular (x : P.KacMoodyAlgebra) :
    ∃ y a z, x = fHom P y + h P a + eHom P z := by
  obtain ⟨x, rfl⟩ := π_surjective P x
  obtain ⟨⟨y, a, z⟩, rfl⟩ := (AuxLieAlgebra.triangularEquiv P).surjective x
  exact ⟨y, a, z, by simp [fHom, eHom, map_add]⟩

variable [CharZero K]

/-- The triangular decomposition `𝔤(A) = 𝔫₋ ⊕ 𝔥 ⊕ 𝔫₊` is direct ([Kac] §1.3). -/
theorem triangular_eq_zero {y z : FreeLieAlgebra K ι} {a : H}
    (hyaz : fHom P y + h P a + eHom P z = 0) : fHom P y = 0 ∧ a = 0 ∧ eHom P z = 0 := by
  have hmem : AuxLieAlgebra.fHom P y + AuxLieAlgebra.h P a + AuxLieAlgebra.eHom P z ∈
      AuxLieAlgebra.maxIdeal P := by
    rw [← π_eq_zero_iff]; simpa [fHom, eHom, map_add] using hyaz
  have hmem' : AuxLieAlgebra.fHom P y + AuxLieAlgebra.h P a + AuxLieAlgebra.eHom P z ∈
      (AuxLieAlgebra.maxIdeal P).toSubmodule := hmem
  rw [AuxLieAlgebra.maxIdeal_eq, Submodule.mem_sup] at hmem'
  obtain ⟨r₁, ⟨hr₁, y', rfl⟩, r₂, ⟨hr₂, z', rfl⟩, hr⟩ := hmem'
  have hr' : AuxLieAlgebra.fHom P y' + AuxLieAlgebra.eHom P z' =
      AuxLieAlgebra.fHom P y + AuxLieAlgebra.h P a + AuxLieAlgebra.eHom P z := hr
  have h0 : AuxLieAlgebra.triangularMap P (y - y', a, z - z') =
      AuxLieAlgebra.triangularMap P 0 := by
    rw [AuxLieAlgebra.triangularMap_apply, map_zero, map_sub, map_sub]
    have : AuxLieAlgebra.fHom P y - AuxLieAlgebra.fHom P y' + AuxLieAlgebra.h P a +
        (AuxLieAlgebra.eHom P z - AuxLieAlgebra.eHom P z') =
        (AuxLieAlgebra.fHom P y + AuxLieAlgebra.h P a + AuxLieAlgebra.eHom P z) -
          (AuxLieAlgebra.fHom P y' + AuxLieAlgebra.eHom P z') := by abel
    rw [this, hr', sub_self]
  have hinj := AuxLieAlgebra.triangularMap_injective P h0
  simp only [Prod.mk_eq_zero, sub_eq_zero] at hinj
  obtain ⟨rfl, rfl, rfl⟩ := hinj
  refine ⟨(π_eq_zero_iff P).mpr hr₁, rfl, (π_eq_zero_iff P).mpr hr₂⟩

/-- The map `𝔥 → 𝔤(A)` is injective ([Kac] §1.3). -/
theorem h_injective : Function.Injective (h P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have := triangular_eq_zero P (y := 0) (z := 0) (a := a) (by simp [ha])
  exact this.2.1

/-! ### Root spaces -/

/-- The root space `𝔤_μ = {x ∈ 𝔤(A) | ∀ h, [h, x] = ⟨μ, h⟩ x}`. -/
abbrev rootSpace (μ : Dual K H) : Submodule K P.KacMoodyAlgebra :=
  weightSpaceOfMap P.KacMoodyAlgebra (h P) μ

omit [CharZero K] in
lemma π_mem_rootSpace {μ : Dual K H} {x : P.AuxLieAlgebra}
    (hx : x ∈ AuxLieAlgebra.rootSpace P μ) : π P x ∈ rootSpace P μ := by
  intro a
  rw [← π_h, ← LieHom.map_lie, hx a, map_smul]

omit [CharZero K] in
/-- The root space `𝔤_μ` is the image of the root space `𝔤̃_μ` ([Kac] §1.3). -/
theorem rootSpace_eq_map (μ : Dual K H) :
    rootSpace P μ = (AuxLieAlgebra.rootSpace P μ).map (π P).toLinearMap := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨x, rfl⟩ := π_surjective P x
    have htop := AuxLieAlgebra.iSup_rootSpace_eq_top P
    have hx' : (π P).toLinearMap x ∈
        ⨆ ν, (AuxLieAlgebra.rootSpace P ν).map (π P).toLinearMap := by
      rw [← Submodule.map_iSup]
      refine Submodule.mem_map_of_mem ?_
      exact (iSup₂_le fun ν _ ↦ le_iSup (fun ν ↦ AuxLieAlgebra.rootSpace P ν) ν)
        (htop ▸ Submodule.mem_top)
    refine mem_of_mem_iSup_of_le (h P)
      (fun ν ↦ (AuxLieAlgebra.rootSpace P ν).map (π P).toLinearMap) ?_ hx hx'
    intro ν
    rw [Submodule.map_le_iff_le_comap]
    exact fun y hy ↦ π_mem_rootSpace P hy
  · rw [Submodule.map_le_iff_le_comap]
    exact fun y hy ↦ π_mem_rootSpace P hy

/-- `𝔤_0 = 𝔥` ([Kac] §1.3). -/
theorem rootSpace_zero : rootSpace P 0 = LinearMap.range (h P) := by
  rw [rootSpace_eq_map, AuxLieAlgebra.rootSpace_zero, h, LinearMap.range_comp]

/-- `𝔤_{k αᵢ} = 0` for `k ≥ 2` ([Kac] §1.3). -/
theorem rootSpace_nsmul_root_eq_bot (i : ι) {n : ℕ} (hn : 2 ≤ n) :
    rootSpace P (n • P.root i) = ⊥ := by
  rw [rootSpace_eq_map, AuxLieAlgebra.rootSpace_nsmul_root_eq_bot P i hn, Submodule.map_bot]

/-- `𝔤_{αᵢ} = K eᵢ` ([Kac] §1.3). -/
theorem rootSpace_root (i : ι) : rootSpace P (P.root i) = K ∙ e P i := by
  rw [rootSpace_eq_map, AuxLieAlgebra.rootSpace_root, Submodule.map_span, Set.image_singleton]
  rfl

lemma e_ne_zero (i : ι) : e P i ≠ 0 := by
  intro he
  have := lie_e_f_self P i
  rw [he, zero_lie, ← map_zero (h P)] at this
  exact P.linearIndependent_coroot.ne_zero i (h_injective P this).symm
/-- `𝔤_{-αᵢ} = K fᵢ`. -/
theorem rootSpace_neg_root (i : ι) : rootSpace P (-P.root i) = K ∙ f P i := by
  rw [rootSpace_eq_map, AuxLieAlgebra.rootSpace_neg_root, Submodule.map_span,
    Set.image_singleton]
  rfl

/-- `𝔤_{-k αᵢ} = 0` for `k ≥ 2`. -/
theorem rootSpace_neg_nsmul_root_eq_bot (i : ι) {n : ℕ} (hn : 2 ≤ n) :
    rootSpace P (-(n • P.root i)) = ⊥ := by
  rw [rootSpace_eq_map, AuxLieAlgebra.rootSpace_neg_nsmul_root_eq_bot P i hn, Submodule.map_bot]

/-- `dim 𝔤_{αᵢ} = 1` ([Kac] §1.3). -/
theorem finrank_rootSpace_root (i : ι) : finrank K (rootSpace P (P.root i)) = 1 := by
  rw [rootSpace_root, finrank_span_singleton (e_ne_zero P i)]

lemma f_ne_zero (i : ι) : f P i ≠ 0 := by
  intro hf
  have := lie_e_f_self P i
  rw [hf, lie_zero, ← map_zero (h P)] at this
  exact P.linearIndependent_coroot.ne_zero i (h_injective P this).symm

/-- `dim 𝔤_{-αᵢ} = 1`. -/
theorem finrank_rootSpace_neg_root (i : ι) : finrank K (rootSpace P (-P.root i)) = 1 := by
  rw [rootSpace_neg_root, finrank_span_singleton (f_ne_zero P i)]

/-- The root spaces `𝔤_{±α}`, `α ∈ Q₊ \ {0}`, are finite-dimensional ([Kac] §1.3). -/
theorem finiteDimensional_rootSpace {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    FiniteDimensional K (rootSpace P μ) := by
  have := AuxLieAlgebra.finiteDimensional_rootSpace P hμ
  rw [rootSpace_eq_map]
  infer_instance

theorem finiteDimensional_rootSpace_neg {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    FiniteDimensional K (rootSpace P (-μ)) := by
  have := AuxLieAlgebra.finiteDimensional_rootSpace_neg P hμ
  rw [rootSpace_eq_map]
  infer_instance

omit [CharZero K] in
/-- `𝔤(A)` is the sum of its root spaces `𝔤_μ`, `μ ∈ -(Q₊ \ 0) ∪ {0} ∪ (Q₊ \ 0)`. -/
theorem iSup_rootSpace_eq_top : ⨆ μ ∈ AuxLieAlgebra.allWeights P, rootSpace P μ = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨x, rfl⟩ := π_surjective P x
  have hx : x ∈ ⨆ μ ∈ AuxLieAlgebra.allWeights P, AuxLieAlgebra.rootSpace P μ := by
    rw [AuxLieAlgebra.iSup_rootSpace_eq_top]; trivial
  have := Submodule.mem_map_of_mem (f := (π P).toLinearMap) hx
  rw [Submodule.map_iSup] at this
  simp_rw [Submodule.map_iSup] at this
  exact (iSup₂_mono fun μ _ ↦ (rootSpace_eq_map P μ).ge :
    (⨆ μ ∈ AuxLieAlgebra.allWeights P, (AuxLieAlgebra.rootSpace P μ).map (π P).toLinearMap) ≤
      ⨆ μ ∈ AuxLieAlgebra.allWeights P, rootSpace P μ) this

/-! ### The Chevalley involution -/

/-- The Chevalley involution of `𝔤(A)`: `eᵢ ↦ -fᵢ`, `fᵢ ↦ -eᵢ`, `h ↦ -h` ([Kac] (1.3.4)). -/
def chevalleyInvolution : P.KacMoodyAlgebra →ₗ⁅K⁆ P.KacMoodyAlgebra :=
  LieIdeal.lift _ ((π P).comp (AuxLieAlgebra.chevalleyInvolution P)) fun x hx ↦ by
    simp only [LieHom.mem_ker, LieHom.comp_apply]
    exact (π_eq_zero_iff P).mpr (AuxLieAlgebra.chevalleyInvolution_mem_maxIdeal P hx)

@[simp] lemma chevalleyInvolution_π (x : P.AuxLieAlgebra) :
    chevalleyInvolution P (π P x) = π P (AuxLieAlgebra.chevalleyInvolution P x) := rfl

@[simp] lemma chevalleyInvolution_e (i : ι) : chevalleyInvolution P (e P i) = -f P i := by
  rw [← π_e, chevalleyInvolution_π, AuxLieAlgebra.chevalleyInvolution_e, map_neg, π_f]

@[simp] lemma chevalleyInvolution_f (i : ι) : chevalleyInvolution P (f P i) = -e P i := by
  rw [← π_f, chevalleyInvolution_π, AuxLieAlgebra.chevalleyInvolution_f, map_neg, π_e]

@[simp] lemma chevalleyInvolution_h (a : H) : chevalleyInvolution P (h P a) = -h P a := by
  rw [← π_h, chevalleyInvolution_π, AuxLieAlgebra.chevalleyInvolution_h, map_neg, π_h]

@[simp] lemma chevalleyInvolution_chevalleyInvolution (x : P.KacMoodyAlgebra) :
    chevalleyInvolution P (chevalleyInvolution P x) = x := by
  obtain ⟨x, rfl⟩ := π_surjective P x
  simp

/-! ### The Serre relations -/

variable (hA : A.IsGeneralizedCartan)
include hA

/-- The Serre relations `(ad eᵢ)^{1 - aᵢⱼ} eⱼ = 0` hold in `𝔤(A)` for `i ≠ j` ([Kac]
§3.3). -/
theorem serre_e {i j : ι} (hij : i ≠ j) :
    (ad K _ (e P i) ^ (-A i j).toNat) ⁅e P i, e P j⁆ = 0 := by
  have := (π_eq_zero_iff P).mpr (AuxLieAlgebra.serreE_mem_maxIdeal P hA hij)
  rwa [AuxLieAlgebra.serreE, LieHom.map_ad_pow, LieHom.map_lie] at this

/-- The Serre relations `(ad fᵢ)^{1 - aᵢⱼ} fⱼ = 0` hold in `𝔤(A)` for `i ≠ j` ([Kac]
§3.3). -/
theorem serre_f {i j : ι} (hij : i ≠ j) :
    (ad K _ (f P i) ^ (-A i j).toNat) ⁅f P i, f P j⁆ = 0 := by
  have := (π_eq_zero_iff P).mpr (AuxLieAlgebra.serreF_mem_maxIdeal P hA hij)
  rwa [AuxLieAlgebra.serreF, LieHom.map_ad_pow, LieHom.map_lie] at this

end KacMoodyAlgebra

end Matrix.Realization

end
