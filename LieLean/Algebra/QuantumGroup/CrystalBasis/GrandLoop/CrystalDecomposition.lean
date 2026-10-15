/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.CrystalBaseUniqueness
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.RatFunc
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorCrystalEquiv

/-!
# The crystal of a crystal base in `𝒪_int`

Let `M` be a module in `𝒪_int` and `(L, B)` a crystal base of `M`. By the uniqueness of crystal
bases ([HK] Thm. 5.2.1, [Kas] Thm. 4.3; `GrandLoop.exists_equiv_of_isCategoryOInt`), `(L, B)` is
isomorphic to `⊕ⱼ (L(λⱼ), B(λⱼ))` for dominant weights `λⱼ`. Here we deduce the consequences for
the crystal of `B` stated in [Kas] §4.5, (4.6):

* the crystal of `B` is isomorphic to the disjoint union `⊔ⱼ B(λⱼ)` of the crystals of the
  `L_q(λⱼ)`, and its highest weight elements are the images of the `u_{λⱼ}`, of weight `λⱼ`;
* consequently the crystal of `B` is normal (`Crystal.IsNormal`, relative to the path model), since
  each `B(λⱼ)` is normal (`GrandLoop.isNormal_crystalHW`).

## Main definitions

* `IsCrystalBase.crystalEquivOfEquiv`: an isomorphism of crystal bases ([HK] Def. 4.2.9 (2))
  induces an isomorphism of their crystals.
* `IsCrystalBase.sigmaCrystalEquiv`: the crystal of `(⊕ⱼ Lⱼ, ⊔ⱼ Bⱼ)` is the disjoint union of the
  crystals of the `(Lⱼ, Bⱼ)`.
* `Crystal.Equiv.mapDatum`: isomorphisms of crystals pushed forward along a morphism of Cartan
  data.

## Main results

* `GrandLoop.exists_crystalEquiv_sigma_of_isCategoryOInt`: the crystal of a crystal base of a
  module in `𝒪_int` is `⊔ⱼ B(λⱼ)`, with highest weight elements the `u_{λⱼ}` ([Kas] (4.6)).
* `GrandLoop.isNormal_crystal_of_isCategoryOInt`: this crystal is normal, for every morphism of
  Cartan data to a realization over `ℝ`; `GrandLoop.isNormal_crystal_of_isCategoryOInt'` for the
  standard real realization, and `GrandLoop.isNormal_crystal_of_isCategoryOInt_ratFunc` over `ℚ(v)`
  with no hypothesis left.

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.2, §5.2.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §4.5, §7.6.
-/

open Pointwise

noncomputable section

namespace Crystal

variable {ι X X' : Type*} [AddCommGroup X] [AddCommGroup X'] {D : CartanDatum ι X}
  {D' : CartanDatum ι X'} (ψ : D.Hom D') {B₁ B₂ : Type*} {C₁ : Crystal D B₁} {C₂ : Crystal D B₂}

/-- An isomorphism of crystals is an isomorphism of the crystals pushed forward along a morphism of
Cartan data. -/
def Equiv.mapDatum (Φ : Equiv C₁ C₂) : Equiv (C₁.mapDatum ψ) (C₂.mapDatum ψ) where
  toEquiv := Φ.toEquiv
  wt_map b := congrArg ψ.toFun (Φ.wt_map b)
  ε_map := Φ.ε_map
  e_map := Φ.e_map
  f_map := Φ.f_map

@[simp] lemma Equiv.mapDatum_apply (Φ : Equiv C₁ C₂) (b : B₁) : Φ.mapDatum ψ b = Φ b := rfl

/-- Pushing forward commutes with disjoint unions. -/
lemma sigma_mapDatum {α : Type*} {B : α → Type*} (C : ∀ a, Crystal D (B a)) :
    (Crystal.sigma C).mapDatum ψ = Crystal.sigma fun a ↦ (C a).mapDatum ψ := rfl

/-- The highest weight elements of a disjoint union are those of the summands. -/
lemma isHighestWeight_sigma_iff {α : Type*} {B : α → Type*} (C : ∀ a, Crystal D (B a)) (a : α)
    (b : B a) : (Crystal.sigma C).IsHighestWeight ⟨a, b⟩ ↔ (C a).IsHighestWeight b :=
  forall_congr' fun _ ↦ Option.map_eq_none_iff

end Crystal

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]
  {M' : Type*} [AddCommGroup M'] [Module k M'] [Module (QuantumGroup R v) M']
  [IsScalarTower k (QuantumGroup R v) M']
  [NeZero v] {hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1} {hM : IsIntegrable R v M}
  {hM' : IsIntegrable R v M'}
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]
  [Module A M'] [IsScalarTower A k M']

/-! ### Isomorphisms of crystal bases -/

/-- The isomorphism `L / cL ≃ L' / cL'` induced by an isomorphism of integrable `U`-modules
intertwines `ẽᵢ`. -/
lemma IsCrystalLattice.quotEquiv_eQ {L : Submodule A M} (hL : IsCrystalLattice hv hM L)
    {L' : Submodule A M'} (hL' : IsCrystalLattice hv hM' L') (ψ : M ≃ₗ[QuantumGroup R v] M')
    (hLL' : ∀ m, m ∈ L ↔ ψ m ∈ L') (c : A) (i : I) (b : L ⧸ (Ideal.span {c} • ⊤ : Submodule A L)) :
    IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c (hL.eQ c i b) =
      hL'.eQ c i (IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  exact map_kashiwaraE hv hM i hM' ψ.toLinearMap x

namespace IsCrystalBase

variable {L : Submodule A M} {hL : IsCrystalLattice hv hM L} {c : A}
  {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}

variable {L' : Submodule A M'} {hL' : IsCrystalLattice hv hM' L'}
  {B' : Set (L' ⧸ (Ideal.span {c} • ⊤ : Submodule A L'))}

/-- **Isomorphic crystal bases have isomorphic crystals.** An isomorphism `ψ : M ≃ M'` of
integrable `U`-modules mapping `L` onto `L'` and inducing a bijection `B ≃ B'` (an isomorphism of
crystal bases, [HK] Def. 4.2.9 (2)) induces an isomorphism of crystals `B ≃ B'`. -/
def crystalEquivOfEquiv (hB : IsCrystalBase hL c B) (hB' : IsCrystalBase hL' c B')
    (hc : ¬IsUnit c) (ψ : M ≃ₗ[QuantumGroup R v] M') (hLL' : ∀ m, m ∈ L ↔ ψ m ∈ L')
    (hBB' : ∀ b, b ∈ B ↔ IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b ∈ B') :
    Crystal.Equiv (hB.crystal hc) (hB'.crystal hc) :=
  Crystal.equivOfE (hB.isSeminormal_crystal hc) (hB'.isSeminormal_crystal hc)
    ((IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c).toEquiv.subtypeEquiv hBB')
    (fun b ↦ by
      obtain ⟨x, hx, hxb⟩ := hB.exists_mk_eq b
      refine hB'.wt_eq hc _ ⟨ψ x, (hLL' x).1 x.2⟩ (map_mem_weightSpace ψ.toLinearMap hx) ?_
      change _ = IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b.1
      rw [← hxb]
      rfl)
    (fun i b ↦ by
      rw [crystal_e, crystal_e]
      cases h : hB.e i b with
      | none =>
        rw [Option.map_none, e_eq_none_iff]
        rw [e_eq_none_iff] at h
        change hL'.eQ c i (IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b.1) = 0
        rw [← hL.quotEquiv_eQ hL' ψ hLL', h, map_zero]
      | some b' =>
        rw [e_eq_some_iff hB hc] at h
        rw [Option.map_some, e_eq_some_iff hB' hc]
        change hL'.eQ c i (IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b.1) =
          IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b'.1
        rw [← hL.quotEquiv_eQ hL' ψ hLL', h])

lemma coe_crystalEquivOfEquiv_apply (hB : IsCrystalBase hL c B) (hB' : IsCrystalBase hL' c B')
    (hc : ¬IsUnit c) (ψ : M ≃ₗ[QuantumGroup R v] M') (hLL' : ∀ m, m ∈ L ↔ ψ m ∈ L')
    (hBB' : ∀ b, b ∈ B ↔ IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b ∈ B') (b : B) :
    (hB.crystalEquivOfEquiv hB' hc ψ hLL' hBB' b : _) =
      IntegrableSl2.quotEquiv (ψ.restrictScalars k) hLL' c b := rfl

end IsCrystalBase

/-! ### Direct sums -/

section DirectSum

variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ j, AddCommGroup (N j)]
  [∀ j, Module k (N j)] [∀ j, Module (QuantumGroup R v) (N j)]
  [∀ j, IsScalarTower k (QuantumGroup R v) (N j)] {hN : ∀ j, IsIntegrable R v (N j)}
  [∀ j, Module A (N j)] [∀ j, IsScalarTower A k (N j)] {L : ∀ j, Submodule A (N j)}
  {hL : ∀ j, IsCrystalLattice hv (hN j) (L j)} {c : A}
  {B : ∀ j, Set (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j)))}

/-- The map `⊔ⱼ Bⱼ → ⊔ⱼ Bⱼ ⊆ (⊕ⱼ Lⱼ) / c (⊕ⱼ Lⱼ)` underlying `IsCrystalBase.sigmaCrystalEquiv`. -/
def dfinsuppBaseMk (B : ∀ j, Set (L j ⧸ (Ideal.span {c} • ⊤ : Submodule A (L j))))
    (x : Σ j, B j) : dfinsuppBase L c B :=
  ⟨dfinsuppQuotIncl L c x.1 x.2.1, Set.mem_iUnion.2 ⟨x.1, x.2.1, x.2.2, rfl⟩⟩

lemma dfinsuppBaseMk_bijective (hc : ¬IsUnit c) (hB : ∀ j, IsCrystalBase (hL j) c (B j)) :
    Function.Bijective (dfinsuppBaseMk (L := L) (c := c) B) := by
  refine ⟨fun ⟨j, b⟩ ⟨l, b'⟩ h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · have h' : dfinsuppQuotIncl L c j b.1 = dfinsuppQuotIncl L c l b'.1 := congrArg Subtype.val h
    by_cases hjl : j = l
    · subst hjl
      rw [(dfinsuppQuotIncl_injective L c j).eq_iff] at h'
      rw [Subtype.ext h']
    · have := congrArg (dfinsuppQuotProj L c l) h'
      rw [dfinsuppQuotProj_incl_of_ne L c hjl, dfinsuppQuotProj_incl_self] at this
      exact absurd (this ▸ b'.2) ((hB l).zero_notMem hc)
  · obtain ⟨j, b, hb, rfl⟩ := Set.mem_iUnion.1 hx
    exact ⟨⟨j, b, hb⟩, rfl⟩

/-- **The crystal of a direct sum of crystal bases is the disjoint union of their crystals.** For
crystal bases `(Lⱼ, Bⱼ)` of `Nⱼ`, the crystal of the crystal base `(⊕ⱼ Lⱼ, ⊔ⱼ Bⱼ)` of `⊕ⱼ Nⱼ`
(`IsCrystalBase.dfinsupp`, [HK] Thm. 4.2.10) is `⊔ⱼ Bⱼ` (cf. [Kas] §7.6). -/
def IsCrystalBase.sigmaCrystalEquiv (hc : ¬IsUnit c) (hB : ∀ j, IsCrystalBase (hL j) c (B j)) :
    Crystal.Equiv (Crystal.sigma fun j ↦ (hB j).crystal hc)
      ((IsCrystalBase.dfinsupp hc hB).crystal hc) :=
  Crystal.equivOfE (Crystal.IsSeminormal.sigma fun j ↦ (hB j).isSeminormal_crystal hc)
    ((IsCrystalBase.dfinsupp hc hB).isSeminormal_crystal hc)
    (Equiv.ofBijective _ (dfinsuppBaseMk_bijective hc hB))
    (fun ⟨j, b⟩ ↦ by
      obtain ⟨x, hx, hxb⟩ := (hB j).exists_mk_eq b
      refine (IsCrystalBase.dfinsupp hc hB).wt_eq hc _ (dfinsuppLatticeIncl L j x)
        (map_mem_weightSpace (DFinsupp.lsingle j) hx) ?_
      change _ = dfinsuppQuotIncl L c j b.1
      rw [← hxb]
      rfl)
    (fun i ⟨j, b⟩ ↦ by
      change (IsCrystalBase.dfinsupp hc hB).e i (dfinsuppBaseMk B ⟨j, b⟩) =
        (((hB j).e i b).map (Sigma.mk j)).map (dfinsuppBaseMk B)
      have hQe := (IsCrystalLattice.dfinsupp hL).eQ_dfinsuppQuotIncl hL c i j
      cases h : (hB j).e i b with
      | none =>
        rw [Option.map_none, Option.map_none, IsCrystalBase.e_eq_none_iff]
        rw [IsCrystalBase.e_eq_none_iff] at h
        change (IsCrystalLattice.dfinsupp hL).eQ c i (dfinsuppQuotIncl L c j b.1) = 0
        rw [hQe, h, map_zero]
      | some b' =>
        rw [IsCrystalBase.e_eq_some_iff _ hc] at h
        rw [Option.map_some, Option.map_some, IsCrystalBase.e_eq_some_iff _ hc]
        change (IsCrystalLattice.dfinsupp hL).eQ c i (dfinsuppQuotIncl L c j b.1) =
          dfinsuppQuotIncl L c j b'.1
        rw [hQe, h])

@[simp] lemma IsCrystalBase.sigmaCrystalEquiv_apply (hc : ¬IsUnit c)
    (hB : ∀ j, IsCrystalBase (hL j) c (B j)) (x : Σ j, B j) :
    IsCrystalBase.sigmaCrystalEquiv hc hB x = dfinsuppBaseMk B x := rfl

end DirectSum

/-! ### Crystal bases in `𝒪_int` -/

namespace GrandLoop

variable [CharZero k] {hvt : Transcendental ℚ v} {hR : R.IsXRegular} {ϖ : A}
  [Finite I] [IsDomain A] [IsDiscreteValuationRing A]
  (hinj : Function.Injective (algebraMap A k)) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A)
  (hϖv : algebraMap A k ϖ = v⁻¹)
  (hk : ∀ c : k, ∃ (m : ℕ) (a : A), algebraMap A k (ϖ ^ m) * c = algebraMap A k a)
  (hfund : ∀ j : I, ∃ Λ : Dom R, ∀ i, Λ.1 (R.coroot i) = if i = j then 1 else 0)
  {L : Submodule A M} {hL : IsCrystalLattice (pow_ne_one_of_transcendental' hvt) hM L}
  {B : Set (L ⧸ (Ideal.span {ϖ} • ⊤ : Submodule A L))}

include hinj hϖ hϖv hk hfund

/-- The highest weight elements of `B(λ)` are `u_λ`. -/
lemma isHighestWeight_crystalHW_iff (Λ : Dom R)
    (b : IrreducibleModule.base hR (pow_ne_one_of_transcendental' hvt) Λ.2 A ϖ) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).IsHighestWeight b ↔
      b = topHW hvt hR hinj hϖ Λ := by
  refine ⟨fun h ↦ Crystal.eq_of_isHighestWeight
    (exists_fWord_crystalHW hvt hR hinj hϖ hϖv hk hfund Λ b) h, ?_⟩
  rintro rfl
  exact e_topHW hinj hϖ hϖv hk hfund Λ

lemma wt_topHW (Λ : Dom R) :
    (crystalHW hvt hR hinj hϖ hϖv hk hfund Λ).wt (topHW hvt hR hinj hϖ Λ) = Λ.1 := by
  rw [topHW, wt_mkHW]
  simp

/-- **The crystal of a crystal base in `𝒪_int`** ([Kas] §4.5, (4.6); [HK] Thm. 5.2.1). Let `M` be a
module in `𝒪_int` and `(L, B)` a crystal base of `M`. Then the crystal of `B` is isomorphic to the
disjoint union `⊔ⱼ B(λⱼ)` of the crystals of the crystal bases `(L(λⱼ), B(λⱼ))` of the `L_q(λⱼ)`,
for dominant weights `λⱼ` (indexed by a set of submodules of `M`), and the highest weight elements
of `B` are exactly the images of the `u_{λⱼ}`, of weight `λⱼ`. Kashiwara states the
correspondence between irreducible summands of `M`, connected components of `B` and highest weight
elements of `B` schematically. -/
theorem exists_crystalEquiv_sigma_of_isCategoryOInt (hO : IsCategoryOInt R v M)
    (hB : IsCrystalBase hL ϖ B) :
    ∃ (s : Set (Submodule (QuantumGroup R v) M)) (Λ : s → Dom R)
      (Φ : Crystal.Equiv (Crystal.sigma fun j ↦ crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ j))
        (hB.crystal (not_isUnit_ϖ hϖ))),
      (∀ b, (hB.crystal (not_isUnit_ϖ hϖ)).IsHighestWeight b ↔
        ∃ j, b = Φ ⟨j, topHW hvt hR hinj hϖ (Λ j)⟩) ∧
      ∀ j, (hB.crystal (not_isUnit_ϖ hϖ)).wt (Φ ⟨j, topHW hvt hR hinj hϖ (Λ j)⟩) = (Λ j).1 := by
  classical
  obtain ⟨s, Λ, Ψ, hΨ, hBB⟩ := exists_equiv_of_isCategoryOInt hinj hϖ hϖv hk hfund hO hB
  have hc := not_isUnit_ϖ hϖ
  have hB₀ := fun j ↦ isCrystalBaseHW hvt hR hinj hϖ hϖv hk hfund (Λ j)
  let Φ := (IsCrystalBase.sigmaCrystalEquiv hc hB₀).trans
    ((IsCrystalBase.dfinsupp hc hB₀).crystalEquivOfEquiv hB hc Ψ hΨ hBB)
  refine ⟨s, Λ, Φ, fun b ↦ ?_, fun j ↦ ?_⟩
  · obtain ⟨⟨j, b₀⟩, rfl⟩ := Φ.toEquiv.surjective b
    rw [Crystal.Equiv.coe_toEquiv, ← Crystal.Equiv.coe_toStrictHom,
      Crystal.StrictHom.isHighestWeight_apply_iff, Crystal.isHighestWeight_sigma_iff]
    change (crystalHW hvt hR hinj hϖ hϖv hk hfund (Λ j)).IsHighestWeight b₀ ↔ _
    rw [isHighestWeight_crystalHW_iff hinj hϖ hϖv hk hfund]
    refine ⟨fun h ↦ ⟨j, by rw [h]; rfl⟩, fun ⟨j', h⟩ ↦ ?_⟩
    obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.mp (Φ.toEquiv.injective h)
    exact eq_of_heq h'
  · exact (Φ.toStrictHom.wt_apply _).trans (wt_topHW hinj hϖ hϖv hk hfund (Λ j))

section Normal

variable [Fintype I] {H : Type*} [AddCommGroup H] [Module ℝ H] {Cm : Matrix I I ℤ}
  {P : Matrix.Realization Cm ℝ H} (hCm : Cm.IsGeneralizedCartan)
  (ψ : R.crystalDatum.Hom (P.cartanDatum hCm)) [IsFormallyReal (A ⧸ Ideal.span {ϖ})]

/-- **The crystal of a crystal base in `𝒪_int` is normal.** For a module `M` in `𝒪_int` with a
crystal base `(L, B)` and a morphism of Cartan data `ψ` from the root datum to a realization over
`ℝ`, `ψ_* B` is normal (`Crystal.IsNormal`, relative to the path model): it is `⊔ⱼ ψ_* B(λⱼ)`
(`GrandLoop.exists_crystalEquiv_sigma_of_isCategoryOInt`) and each `ψ_* B(λⱼ)` is a path crystal
(`GrandLoop.isNormal_crystalHW`). This is the normality of crystals of integrable modules in
[Kas] §7.6, for modules in `𝒪_int`. -/
theorem isNormal_crystal_of_isCategoryOInt (hR : R.IsXRegular) (hO : IsCategoryOInt R v M)
    (hB : IsCrystalBase hL ϖ B) : ((hB.crystal (not_isUnit_ϖ hϖ)).mapDatum ψ).IsNormal := by
  obtain ⟨s, Λ, Φ, -⟩ :=
    exists_crystalEquiv_sigma_of_isCategoryOInt (hR := hR) hinj hϖ hϖv hk hfund hO hB
  have h := Crystal.IsNormal.sigma fun j : s ↦
    isNormal_crystalHW (hvt := hvt) (hR := hR) hCm ψ hinj hϖ hϖv hk hfund (Λ j)
  rw [← Crystal.sigma_mapDatum] at h
  exact h.of_equiv (Φ.mapDatum ψ)

/-- **The crystal of a crystal base in `𝒪_int` is normal**, with weights in the standard real
realization of the Cartan matrix (`LusztigCartanDatum.RootDatum.stdHom`). -/
theorem isNormal_crystal_of_isCategoryOInt' (hO : IsCategoryOInt R v M)
    (hB : IsCrystalBase hL ϖ B) :
    ((hB.crystal (not_isUnit_ϖ hϖ)).mapDatum (R.stdHom hR)).IsNormal :=
  isNormal_crystal_of_isCategoryOInt (hvt := hvt) hinj hϖ hϖv hk hfund _ _ hR hO hB

end Normal

end GrandLoop

end LieLean.QuantumGroup

/-! ### Kashiwara's setting `ℚ(v)` -/

namespace LieLean.QuantumGroup.GrandLoop

open Sl2.RankOne

variable {I : Type*} [Fintype I] [DecidableEq I] {D : LusztigCartanDatum I}
  {M : Type*} [AddCommGroup M] [Module (RatFunc ℚ) M]
  [Module (QuantumGroup D.extendedRootDatum vInf) M]
  [IsScalarTower (RatFunc ℚ) (QuantumGroup D.extendedRootDatum vInf) M]
  [Module LocalRing M] [IsScalarTower LocalRing (RatFunc ℚ) M]
  {hM : IsIntegrable D.extendedRootDatum vInf M} {L : Submodule LocalRing M}
  {hL : IsCrystalLattice (pow_ne_one_of_transcendental' transcendental_vInf) hM L}
  {B : Set (L ⧸ (Ideal.span {localX} • ⊤ : Submodule LocalRing L))}

/-- **The crystal of a crystal base in `𝒪_int` is normal**, in Kashiwara's setting: `k = ℚ(v)`,
`A` the local ring at `v = ∞`, `ϖ = v⁻¹`, for every Cartan datum with finite index set and the root
datum `LusztigCartanDatum.extendedRootDatum`, with no hypothesis left. -/
theorem isNormal_crystal_of_isCategoryOInt_ratFunc (hO : IsCategoryOInt D.extendedRootDatum vInf M)
    (hB : IsCrystalBase hL localX B) :
    ((hB.crystal (not_isUnit_ϖ localX_mem_maximalIdeal)).mapDatum
      (D.extendedRootDatum.stdHom D.isXRegular_extendedRootDatum)).IsNormal :=
  isNormal_crystal_of_isCategoryOInt' (hvt := transcendental_vInf)
    (hR := D.isXRegular_extendedRootDatum)
    injective_algebraMap_localRing localX_mem_maximalIdeal algebraMap_localX exists_pow_localX_mul
    D.exists_fundamental_extendedRootDatum hO hB

end LieLean.QuantumGroup.GrandLoop
