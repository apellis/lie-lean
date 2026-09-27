/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.Homology.Complex
import LieLean.LinearAlgebra.Eigenspace.Weight

/-!
# Weight decomposition of the Chevalley–Eilenberg complex

Let `L` be a Lie algebra and `M` an `L`-module over a field `K`, and suppose that a vector space
`H` acts on `L` by derivations `D a` and on `M` by endomorphisms `φ a` compatibly with the action
of `L`: `φ a (x m) = (D a x) m + x (φ a m)`. (The main example: `L = 𝔫₋` in a Kac–Moody algebra,
`H = 𝔥` acting by the adjoint action, `M` a `𝔤`-module.) Then `H` acts on `⋀L ⊗ M` by the
operators `θ(a) = θ(D a, φ a)` (`LieModule.ChevalleyEilenberg.derivExt`), which commute with the
Chevalley–Eilenberg differential. Consequently the chains, cycles, boundaries and homology of
`L` with coefficients in `M` decompose into weight spaces for `H`, as soon as `L` and `M` are sums
of weight spaces.

## Main definitions

* `LieModule.ChevalleyEilenberg.DerivAction`: the data `(D, φ)` of a compatible action.
* `LieModule.ChevalleyEilenberg.DerivAction.θ`: the action `a ↦ θ(a)` of `H` on `⋀L ⊗ M`.
* `LieModule.ChevalleyEilenberg.DerivAction.chainWeightSpace`: the weight space `(⋀L ⊗ M)_μ`.
* `LieModule.ChevalleyEilenberg.DerivAction.homologyWeightSpace`: the weight space
  `H_k(L, M)_μ`, the image of the weight-`μ` cycles in `(⋀L ⊗ M) / B_k`.

## Main results

* `LieModule.ChevalleyEilenberg.DerivAction.diff_θ`: `d ∘ θ(a) = θ(a) ∘ d`.
* `LieModule.ChevalleyEilenberg.DerivAction.iSup_chainWeightSpace`: `⋀L ⊗ M` is the sum of its
  weight spaces if `L` and `M` are.
* `LieModule.ChevalleyEilenberg.DerivAction.iSup_inf_chainWeightSpace`: every `θ`-stable subspace
  (e.g. the chains, cycles or boundaries of degree `k`) is the sum of its weight components.
* `LieModule.ChevalleyEilenberg.DerivAction.iSup_homologyWeightSpace`,
  `iSupIndep_homologyWeightSpace`: `H_k(L, M) = ⊕_μ H_k(L, M)_μ`.
* `LieModule.ChevalleyEilenberg.DerivAction.homologyWeightSpace_eq`: `H_k(L, M)_μ` is the
  weight space of `H_k(L, M)` for the induced action of `H`.
* `LieModule.ChevalleyEilenberg.DerivAction.finrank_homologyWeightSpace_add`:
  `dim H_k(L, M)_μ + dim (B_k)_μ = dim (Z_k)_μ`.

## References

* H. Garland, J. Lepowsky, *Lie algebra homology and the Macdonald–Kac formulas*, Invent. Math.
  **34** (1976), 37–76, §3 (check).
-/

open Module TensorProduct ExteriorAlgebra

noncomputable section

namespace LieModule.ChevalleyEilenberg

variable (K H L M : Type*) [Field K] [AddCommGroup H] [Module K H] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M]

/-- An action of a vector space `H` on a Lie algebra `L` by derivations `D a` and on an
`L`-module `M` by endomorphisms `φ a`, compatible with the action of `L` on `M`. -/
structure DerivAction where
  /-- The action of `H` on `L`. -/
  D : H →ₗ[K] Module.End K L
  /-- The action of `H` on `M`. -/
  φ : H →ₗ[K] Module.End K M
  D_lie : ∀ (a : H) (x y : L), D a ⁅x, y⁆ = ⁅D a x, y⁆ + ⁅x, D a y⁆
  φ_lie : ∀ (a : H) (x : L) (m : M), φ a ⁅x, m⁆ = ⁅D a x, m⁆ + ⁅x, φ a m⁆

namespace DerivAction

variable {K H L M} (ρ : DerivAction K H L M)

local notation "E" => ExteriorAlgebra K L ⊗[K] M

/-! ### The action of `H` on the complex -/

/-- The action `θ(a) = θ(D a, φ a)` of `a ∈ H` on `⋀L ⊗ M`. -/
def θ : H →ₗ[K] Module.End K E where
  toFun a := derivExt (ρ.D a) (ρ.φ a)
  map_add' a b := by rw [map_add, map_add, derivExt_add]
  map_smul' c a := by rw [map_smul, map_smul, derivExt_smul, RingHom.id_apply]

lemma θ_apply (a : H) : ρ.θ a = derivExt (ρ.D a) (ρ.φ a) := rfl

@[simp] lemma θ_one_tmul (a : H) (m : M) : ρ.θ a (1 ⊗ₜ m) = 1 ⊗ₜ ρ.φ a m :=
  derivExt_one_tmul _ _ m

lemma θ_wedge (a : H) (y : L) (c : E) :
    ρ.θ a (wedge K L M y c) = wedge K L M (ρ.D a y) c + wedge K L M y (ρ.θ a c) :=
  derivExt_wedge _ _ y c

variable [LieModule K L M]

/-- The action of `H` commutes with the Chevalley–Eilenberg differential. -/
theorem diff_comp_θ (a : H) : diff K L M ∘ₗ ρ.θ a = ρ.θ a ∘ₗ diff K L M :=
  diff_comp_derivExt (ρ.D_lie a) (ρ.φ_lie a)

lemma diff_θ (a : H) (c : E) : diff K L M (ρ.θ a c) = ρ.θ a (diff K L M c) :=
  LinearMap.congr_fun (ρ.diff_comp_θ a) c

omit [LieModule K L M] in
lemma θ_mem_chainsIn (a : H) {k : ℕ} {c : E} (hc : c ∈ chainsIn K L M k) :
    ρ.θ a c ∈ chainsIn K L M k :=
  derivExt_mem_chainsIn _ _ hc

lemma θ_mem_cycles (a : H) {k : ℕ} {c : E} (hc : c ∈ cycles K L M k) :
    ρ.θ a c ∈ cycles K L M k :=
  ⟨ρ.θ_mem_chainsIn a hc.1, LinearMap.mem_ker.mpr (by
    rw [diff_θ, LinearMap.mem_ker.mp hc.2, map_zero])⟩

lemma θ_mem_boundaries (a : H) {k : ℕ} {c : E} (hc : c ∈ boundaries K L M k) :
    ρ.θ a c ∈ boundaries K L M k := by
  obtain ⟨c, hc, rfl⟩ := hc
  exact ⟨_, ρ.θ_mem_chainsIn a hc, ρ.diff_θ a c⟩

/-- The action of `H` on `(⋀L ⊗ M) / B_k` induced by `θ`. -/
def θQ (k : ℕ) : H →ₗ[K] Module.End K (E ⧸ boundaries K L M k) where
  toFun a := Submodule.mapQ _ _ (ρ.θ a) fun _ hc ↦ ρ.θ_mem_boundaries a hc
  map_add' a b := by
    ext c
    simp
  map_smul' r a := by
    ext c
    simp

lemma θQ_mk (k : ℕ) (a : H) (c : E) :
    ρ.θQ k a (Submodule.Quotient.mk c) = Submodule.Quotient.mk (ρ.θ a c) := rfl

/-! ### Weight spaces of the chains -/

/-- The weight space `(⋀L ⊗ M)_μ = {c | θ(a) c = μ(a) c for all a ∈ H}`. -/
def chainWeightSpace (μ : Dual K H) : Submodule K E := Module.End.weightSpaceOf ρ.θ μ

omit [LieModule K L M] in
variable {ρ} in
lemma mem_chainWeightSpace {μ : Dual K H} {c : E} :
    c ∈ ρ.chainWeightSpace μ ↔ ∀ a, ρ.θ a c = μ a • c := Iff.rfl

omit [LieModule K L M] in
lemma one_tmul_mem_chainWeightSpace {ν : Dual K H} {m : M}
    (hm : m ∈ Module.End.weightSpaceOf ρ.φ ν) :
    (1 : ExteriorAlgebra K L) ⊗ₜ m ∈ ρ.chainWeightSpace ν :=
  mem_chainWeightSpace.mpr fun a ↦ by
    rw [θ_one_tmul, Module.End.mem_weightSpaceOf.mp hm a, tmul_smul]

omit [LieModule K L M] in
lemma wedge_mem_chainWeightSpace {γ μ : Dual K H} {y : L}
    (hy : y ∈ Module.End.weightSpaceOf ρ.D γ) {c : E} (hc : c ∈ ρ.chainWeightSpace μ) :
    wedge K L M y c ∈ ρ.chainWeightSpace (γ + μ) :=
  mem_chainWeightSpace.mpr fun a ↦ by
    rw [θ_wedge, Module.End.mem_weightSpaceOf.mp hy a, mem_chainWeightSpace.mp hc a, map_smul,
      map_smul, LinearMap.smul_apply, LinearMap.add_apply, add_smul]

lemma diff_mem_chainWeightSpace {μ : Dual K H} {c : E} (hc : c ∈ ρ.chainWeightSpace μ) :
    diff K L M c ∈ ρ.chainWeightSpace μ :=
  mem_chainWeightSpace.mpr fun a ↦ by rw [← diff_θ, mem_chainWeightSpace.mp hc a, map_smul]

omit [LieModule K L M] in
/-- If `L` and `M` are sums of weight spaces, then so is `⋀L ⊗ M`. -/
theorem iSup_chainWeightSpace (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤)
    (hM : ⨆ ν, Module.End.weightSpaceOf ρ.φ ν = ⊤) : ⨆ μ, ρ.chainWeightSpace μ = ⊤ := by
  refine eq_top_iff.mpr fun c _ ↦ induction (fun m ↦ ?_) (fun y c hc ↦ ?_)
    (fun _ _ h h' ↦ add_mem h h') c
  · have hm : m ∈ ⨆ ν, Module.End.weightSpaceOf ρ.φ ν := hM ▸ Submodule.mem_top
    induction hm using Submodule.iSup_induction' with
    | mem ν m hm => exact Submodule.mem_iSup_of_mem ν (ρ.one_tmul_mem_chainWeightSpace hm)
    | zero => simp
    | add m m' _ _ hm hm' => rw [tmul_add]; exact add_mem hm hm'
  · have hy : y ∈ ⨆ γ, Module.End.weightSpaceOf ρ.D γ := hL ▸ Submodule.mem_top
    induction hy using Submodule.iSup_induction' with
    | mem γ y hy =>
      induction hc using Submodule.iSup_induction' with
      | mem μ c hc => exact Submodule.mem_iSup_of_mem _ (ρ.wedge_mem_chainWeightSpace hy hc)
      | zero => simp
      | add c c' _ _ hc hc' => rw [map_add]; exact add_mem hc hc'
    | zero => simp
    | add y y' _ _ hy hy' => rw [map_add, LinearMap.add_apply]; exact add_mem hy hy'

omit [LieModule K L M] in
/-- A subspace of `⋀L ⊗ M` stable under the action of `H` is the sum of its intersections with
the weight spaces (if `L` and `M` are sums of weight spaces). -/
theorem iSup_inf_chainWeightSpace (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤)
    (hM : ⨆ ν, Module.End.weightSpaceOf ρ.φ ν = ⊤)
    (N : Submodule K E) (hN : ∀ a, ∀ c ∈ N, ρ.θ a c ∈ N) :
    ⨆ μ, N ⊓ ρ.chainWeightSpace μ = N := by
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  have h := Module.End.inf_iSup_weightSpaceOf_le ρ.θ N hN
  have htop : ⨆ μ, Module.End.weightSpaceOf ρ.θ μ = ⊤ := ρ.iSup_chainWeightSpace hL hM
  rw [htop, inf_top_eq] at h
  exact h

/-! ### Weight spaces of the homology -/

/-- The weight space of `(⋀L ⊗ M) / B_k` for the action of `H` induced by `θ`. -/
def quotWeightSpace (k : ℕ) (μ : Dual K H) : Submodule K (E ⧸ boundaries K L M k) :=
  Module.End.weightSpaceOf (ρ.θQ k) μ

/-- The weight space `H_k(L, M)_μ ⊆ H_k(L, M)`: the image of the cycles of weight `μ`. -/
def homologyWeightSpace (k : ℕ) (μ : Dual K H) : Submodule K (E ⧸ boundaries K L M k) :=
  (cycles K L M k ⊓ ρ.chainWeightSpace μ).map (boundaries K L M k).mkQ

lemma homologyWeightSpace_le_homology (k : ℕ) (μ : Dual K H) :
    ρ.homologyWeightSpace k μ ≤ homology K L M k :=
  Submodule.map_mono inf_le_left

lemma homologyWeightSpace_le_quotWeightSpace (k : ℕ) (μ : Dual K H) :
    ρ.homologyWeightSpace k μ ≤ ρ.quotWeightSpace k μ := by
  rintro _ ⟨c, ⟨-, hc⟩, rfl⟩ a
  rw [Submodule.mkQ_apply, θQ_mk, mem_chainWeightSpace.mp hc a]
  rfl

/-- The weight spaces of `H_k(L, M)` are independent. -/
theorem iSupIndep_homologyWeightSpace (k : ℕ) : iSupIndep (ρ.homologyWeightSpace k) :=
  (Module.End.iSupIndep_weightSpaceOf (ρ.θQ k)).mono (ρ.homologyWeightSpace_le_quotWeightSpace k)

/-- `H_k(L, M)` is the sum of its weight spaces (if `L` and `M` are sums of weight spaces). -/
theorem iSup_homologyWeightSpace (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤)
    (hM : ⨆ ν, Module.End.weightSpaceOf ρ.φ ν = ⊤) (k : ℕ) :
    ⨆ μ, ρ.homologyWeightSpace k μ = homology K L M k := by
  rw [homology, ← ρ.iSup_inf_chainWeightSpace hL hM (cycles K L M k)
    (fun a _ hc ↦ ρ.θ_mem_cycles a hc), Submodule.map_iSup]
  rfl

/-- `H_k(L, M)_μ` is the `μ`-weight space of `H_k(L, M)` for the induced action of `H`. -/
theorem homologyWeightSpace_eq (hL : ⨆ γ, Module.End.weightSpaceOf ρ.D γ = ⊤)
    (hM : ⨆ ν, Module.End.weightSpaceOf ρ.φ ν = ⊤) (k : ℕ) (μ : Dual K H) :
    ρ.homologyWeightSpace k μ = homology K L M k ⊓ ρ.quotWeightSpace k μ := by
  refine le_antisymm (le_inf (ρ.homologyWeightSpace_le_homology k μ)
    (ρ.homologyWeightSpace_le_quotWeightSpace k μ)) fun x ⟨hx, hx'⟩ ↦ ?_
  rw [← ρ.iSup_homologyWeightSpace hL hM k] at hx
  exact Module.End.mem_of_mem_iSup_of_le (ρ.θQ k) _
    (ρ.homologyWeightSpace_le_quotWeightSpace k) hx' hx

/-- `dim H_k(L, M)_μ + dim (B_k)_μ = dim (Z_k)_μ`. -/
theorem finrank_homologyWeightSpace_add (k : ℕ) (μ : Dual K H)
    [FiniteDimensional K ↥(cycles K L M k ⊓ ρ.chainWeightSpace μ)] :
    finrank K (ρ.homologyWeightSpace k μ) +
        finrank K ↥(boundaries K L M k ⊓ ρ.chainWeightSpace μ) =
      finrank K ↥(cycles K L M k ⊓ ρ.chainWeightSpace μ) := by
  set Z := cycles K L M k ⊓ ρ.chainWeightSpace μ
  set B := boundaries K L M k
  -- an additive group structure on `Z` compatible with its additive monoid structure
  let _ : AddCommGroup Z := Module.addCommMonoidToAddCommGroup K
  have := LinearMap.finrank_range_add_finrank_ker (LinearMap.domRestrict B.mkQ Z)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at this
  have hZB : Z ⊓ B = B ⊓ ρ.chainWeightSpace μ :=
    le_antisymm (fun c ⟨hc, hc'⟩ ↦ ⟨hc', hc.2⟩)
      fun c ⟨hc, hc'⟩ ↦ ⟨⟨boundaries_le_cycles k hc, hc'⟩, hc⟩
  rw [hZB] at this
  rw [homologyWeightSpace, ← this]

end DerivAction

end LieModule.ChevalleyEilenberg
