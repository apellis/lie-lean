/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.CrystalBasis.Integrable
import LieLean.Algebra.QuantumGroup.CrystalBasis.StringCounts
import LieLean.RepresentationTheory.Crystal.Normal

/-!
# Crystal bases of integrable `U`-modules

Let `M` be an integrable `U = U_q(𝔤)`-module ([Lus] 3.5.1), with `v` not a root of unity, and let
`A` be a commutative ring with `k` an `A`-algebra and `M` an `A`-module compatibly, and `c ∈ A`.
(Kashiwara's setting is `A = A₀ ⊆ F(q)`, the rational functions regular at `q = 0`, and `c = q`.)

* A *crystal lattice* (`QuantumGroup.IsCrystalLattice`, [HK] Def. 4.2.2) is a free `A`-submodule
  `L ⊆ M` spanning `M` over `k`, graded by the weight spaces and stable under all Kashiwara
  operators `ẽᵢ`, `f̃ᵢ`.
* A *crystal base* (`QuantumGroup.IsCrystalBase`, [HK] Def. 4.2.3) of `M` is a crystal lattice `L`
  with a basis `B` of the `A/cA`-module `L/cL` consisting of classes of weight vectors such that
  `ẽᵢ B, f̃ᵢ B ⊆ B ∪ {0}` and `f̃ᵢ b = b' ↔ ẽᵢ b' = b` for `b, b' ∈ B`.

For `c` not a unit, `B` carries the structure of an abstract crystal
(`QuantumGroup.IsCrystalBase.crystal`) over the Cartan datum
`LusztigCartanDatum.RootDatum.crystalDatum` of the root datum, with
`εᵢ(b) = max {a | ẽᵢᵃ b ≠ 0}` and `φᵢ(b) = εᵢ(b) + ⟨i, wt b⟩` ([HK] (4.9)), and this crystal is
seminormal (`QuantumGroup.IsCrystalBase.isSeminormal_crystal`): `φᵢ(b) = max {a | f̃ᵢᵃ b ≠ 0}`
([HK] Prop. 4.2.11, (4.10)).

## References

* [HK] J. Hong, S.-J. Kang, *Introduction to quantum groups and crystal bases*, GSM 42, §4.2.
* [Kas] M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §4.
-/

open Pointwise

/-- The Cartan datum of abstract crystals attached to a root datum: weights `X = Hom(Y, ℤ)`,
simple roots `αᵢ = i'` and simple coroots `Λ ↦ Λ(i)`. -/
def LusztigCartanDatum.RootDatum.crystalDatum {I Y : Type*} [AddCommGroup Y]
    {D : LusztigCartanDatum I} (R : D.RootDatum Y) : CartanDatum I (Y →+ ℤ) where
  root := R.root
  coroot i := AddMonoidHom.toIntLinearMap
    { toFun := fun Λ ↦ Λ (R.coroot i), map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  coroot_root_self i := by simp [R.root_coroot, D.cartanMatrix_self]

@[simp] lemma LusztigCartanDatum.RootDatum.crystalDatum_coroot {I Y : Type*} [AddCommGroup Y]
    {D : LusztigCartanDatum I} (R : D.RootDatum Y) (i : I) (Λ : Y →+ ℤ) :
    R.crystalDatum.coroot i Λ = Λ (R.coroot i) := rfl

@[simp] lemma LusztigCartanDatum.RootDatum.crystalDatum_root {I Y : Type*} [AddCommGroup Y]
    {D : LusztigCartanDatum I} (R : D.RootDatum Y) (i : I) :
    R.crystalDatum.root i = R.root i := rfl

namespace LieLean.QuantumGroup

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k}
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M]
  [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1) (hM : IsIntegrable R v M)
  {A : Type*} [CommRing A] [Algebra A k] [Module A M] [IsScalarTower A k M]

/-- The projection of `nodeSl2` onto its graded piece `n` is the projection onto the sum of the
weight spaces `M^Λ` with `⟨i, Λ⟩ = n`. -/
lemma nodeSl2_wtProj (i : I) (n : ℤ) :
    (nodeSl2 R v M hv hM i).wtProj n = weightSetProj hv hM {Λ | Λ (R.coroot i) = n} := by
  refine ext_weightSpace hM fun Λ m hm ↦ ?_
  rw [IntegrableSl2.wtProj_of_mem (V := nodeSl2 R v M hv hM i) (mem_nodeWt_of_mem hm),
    weightSetProj_of_mem hv hM _ hm]
  by_cases h : Λ (R.coroot i) = n <;> simp [h]

/-- A crystal lattice of an integrable `U`-module ([HK] Def. 4.2.2): a free `A`-submodule
spanning `M` over `k`, graded by the weight spaces, and stable under all `ẽᵢ`, `f̃ᵢ`. -/
structure IsCrystalLattice (L : Submodule A M) : Prop where
  span_eq_top : Submodule.span k (L : Set M) = ⊤
  free : Module.Free A L
  weightSetProj_mem : ∀ S, ∀ m ∈ L, weightSetProj hv hM S m ∈ L
  kashiwaraE_mem : ∀ i, ∀ m ∈ L, kashiwaraE R v M hv hM i m ∈ L
  kashiwaraF_mem : ∀ i, ∀ m ∈ L, kashiwaraF R v M hv hM i m ∈ L

variable {L : Submodule A M} {hv hM}

omit [Algebra A k] [IsScalarTower A k M] in
/-- A crystal lattice is Kashiwara-stable for every `nodeSl2`. -/
lemma IsCrystalLattice.isKashiwaraStable (hL : IsCrystalLattice hv hM L) (i : I) :
    (nodeSl2 R v M hv hM i).IsKashiwaraStable (pow_d_ne_zero i) (pow_d_ne_one hv i) L where
  wtProj_mem m hm n := by rw [nodeSl2_wtProj]; exact hL.weightSetProj_mem _ m hm
  eTilde_mem := hL.kashiwaraE_mem i
  fTilde_mem := hL.kashiwaraF_mem i

/-- `ẽᵢ` on `L / c L`. -/
noncomputable abbrev IsCrystalLattice.eQ (hL : IsCrystalLattice hv hM L) (c : A) (i : I) :=
  (nodeSl2 R v M hv hM i).eTildeQ (pow_d_ne_zero i) (pow_d_ne_one hv i) (hL.kashiwaraE_mem i) c

/-- `f̃ᵢ` on `L / c L`. -/
noncomputable abbrev IsCrystalLattice.fQ (hL : IsCrystalLattice hv hM L) (c : A) (i : I) :=
  (nodeSl2 R v M hv hM i).fTildeQ (pow_d_ne_zero i) (pow_d_ne_one hv i) (hL.kashiwaraF_mem i) c

/-- A crystal base of an integrable `U`-module ([HK] Def. 4.2.3): a crystal lattice `L` and a basis
`B` of the `A/cA`-module `L/cL` consisting of classes of weight vectors, such that
`ẽᵢ B, f̃ᵢ B ⊆ B ∪ {0}` and `f̃ᵢ b = b' ↔ ẽᵢ b' = b` for `b, b' ∈ B`. -/
structure IsCrystalBase (hL : IsCrystalLattice hv hM L) (c : A)
    (B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))) : Prop where
  linearIndependent : LinearIndependent (A ⧸ Ideal.span {c}) (Subtype.val : B → _)
  span_eq_top : Submodule.span (A ⧸ Ideal.span {c}) B = ⊤
  exists_weight : ∀ b ∈ B, ∃ Λ, ∃ x : L, (x : M) ∈ weightSpace R v M Λ ∧
    Submodule.Quotient.mk x = b
  eQ_mem : ∀ i, ∀ b ∈ B, hL.eQ c i b ∈ B ∨ hL.eQ c i b = 0
  fQ_mem : ∀ i, ∀ b ∈ B, hL.fQ c i b ∈ B ∨ hL.fQ c i b = 0
  fQ_eq_iff : ∀ i, ∀ b ∈ B, ∀ b' ∈ B, hL.fQ c i b = b' ↔ hL.eQ c i b' = b

namespace IsCrystalBase

variable {hL : IsCrystalLattice hv hM L} {c : A}
  {B : Set (L ⧸ (Ideal.span {c} • ⊤ : Submodule A L))}

lemma zero_notMem (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) : (0 : _) ∉ B := by
  have : Nontrivial (A ⧸ Ideal.span {c}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
  intro h0
  exact hB.linearIndependent.ne_zero ⟨0, h0⟩ rfl

/-- A weight of `b ∈ B`. -/
noncomputable def wt (hB : IsCrystalBase hL c B) (b : B) : Y →+ ℤ :=
  Classical.choose (hB.exists_weight b b.2)

lemma exists_mk_eq (hB : IsCrystalBase hL c B) (b : B) :
    ∃ x : L, (x : M) ∈ weightSpace R v M (hB.wt b) ∧ Submodule.Quotient.mk x = b.1 :=
  Classical.choose_spec (hB.exists_weight b b.2)

/-- The weight of a nonzero class of a weight vector is unique. -/
lemma wt_eq (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (b : B) {Λ : Y →+ ℤ} (x : L)
    (hx : (x : M) ∈ weightSpace R v M Λ) (hxb : Submodule.Quotient.mk x = b.1) :
    hB.wt b = Λ := by
  classical
  by_contra hne
  obtain ⟨y, hy, hyb⟩ := hB.exists_mk_eq b
  have hxy : (x : M) - y ∈ c • L := (IntegrableSl2.mk_eq_mk_iff c x y).1 (hxb.trans hyb.symm)
  have hP := LinearMap.map_mem_smul_of_mem (f := weightSetProj hv hM {Λ}) c
    (hL.weightSetProj_mem _) hxy
  rw [map_sub, weightSetProj_of_mem hv hM _ hx, weightSetProj_of_mem hv hM _ hy] at hP
  simp only [Set.mem_singleton_iff, ↓reduceIte, hne, sub_zero] at hP
  exact hB.zero_notMem hc (by rw [← (IntegrableSl2.mk_eq_zero_iff c x).2 hP, hxb]; exact b.2)

/-- The lengths of the `i`-strings through `b ∈ B` ([HK] Prop. 4.2.11 (3), (4.9)). -/
lemma exists_counts (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b : B) :
    ∃ k p : ℕ, (p : ℤ) = hB.wt b (R.coroot i) + 2 * k ∧ k ≤ p ∧
      (∀ a, (hL.eQ c i ^ a) b.1 = 0 ↔ k < a) ∧ (∀ a, (hL.fQ c i ^ a) b.1 = 0 ↔ p < k + a) := by
  obtain ⟨x, hx, hxb⟩ := hB.exists_mk_eq b
  have := (hL.isKashiwaraStable i).exists_string_counts c B (hB.zero_notMem hc) (hB.eQ_mem i)
    (hB.fQ_eq_iff i) x (mem_nodeWt_of_mem hx) (by rw [hxb]; exact b.2)
  rwa [hxb] at this

/-- `εᵢ(b) = max {a | ẽᵢᵃ b ≠ 0}`. -/
noncomputable def eps (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b : B) : ℕ :=
  Classical.choose (hB.exists_counts hc i b)

lemma eQ_pow_eq_zero_iff (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b : B) (a : ℕ) :
    (hL.eQ c i ^ a) b.1 = 0 ↔ hB.eps hc i b < a :=
  (Classical.choose_spec (Classical.choose_spec (hB.exists_counts hc i b))).2.2.1 a

lemma fQ_pow_eq_zero_iff (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b : B) (a : ℕ) :
    (hL.fQ c i ^ a) b.1 = 0 ↔ (hB.eps hc i b : ℤ) + hB.wt b (R.coroot i) < a := by
  obtain ⟨hp, -, -, hf⟩ := Classical.choose_spec (Classical.choose_spec (hB.exists_counts hc i b))
  rw [hf a]
  unfold eps
  omega

lemma eQ_mk_mem_weightSpace (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b b' : B)
    (h : hL.eQ c i b.1 = b'.1) : hB.wt b' = hB.wt b + R.root i := by
  obtain ⟨x, hx, hxb⟩ := hB.exists_mk_eq b
  refine hB.wt_eq hc b' ⟨_, hL.kashiwaraE_mem i x x.2⟩
    (kashiwaraE_mem_weightSpace hv hM i hx) ?_
  rw [← h, ← hxb]
  rfl

lemma eQ_mem_of_ne (hB : IsCrystalBase hL c B) (i : I) (b : B) (h : hL.eQ c i b.1 ≠ 0) :
    hL.eQ c i b.1 ∈ B :=
  (hB.eQ_mem i b b.2).resolve_right h

lemma fQ_mem_of_ne (hB : IsCrystalBase hL c B) (i : I) (b : B) (h : hL.fQ c i b.1 ≠ 0) :
    hL.fQ c i b.1 ∈ B :=
  (hB.fQ_mem i b b.2).resolve_right h

open scoped Classical in
/-- `ẽᵢ` on `B ∪ {0}`, with `0` modelled by `none`. -/
noncomputable def e (hB : IsCrystalBase hL c B) (i : I) (b : B) : Option B :=
  if h : hL.eQ c i b.1 = 0 then none else some ⟨_, hB.eQ_mem_of_ne i b h⟩

open scoped Classical in
/-- `f̃ᵢ` on `B ∪ {0}`, with `0` modelled by `none`. -/
noncomputable def f (hB : IsCrystalBase hL c B) (i : I) (b : B) : Option B :=
  if h : hL.fQ c i b.1 = 0 then none else some ⟨_, hB.fQ_mem_of_ne i b h⟩

lemma e_eq_some_iff (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b b' : B) :
    hB.e i b = some b' ↔ hL.eQ c i b.1 = b'.1 := by
  unfold e
  split_ifs with h
  · simp only [false_iff]
    intro h'
    exact hB.zero_notMem hc (h ▸ h' ▸ b'.2)
  · simp [Subtype.ext_iff]

lemma f_eq_some_iff (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b b' : B) :
    hB.f i b = some b' ↔ hL.fQ c i b.1 = b'.1 := by
  unfold f
  split_ifs with h
  · simp only [false_iff]
    intro h'
    exact hB.zero_notMem hc (h ▸ h' ▸ b'.2)
  · simp [Subtype.ext_iff]

/-- The crystal of a crystal base ([HK] §4.2, (4.9)–(4.10)): `B` with `wt`, `εᵢ`, `φᵢ` and the
Kashiwara operators. -/
noncomputable def crystal (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) :
    Crystal R.crystalDatum B where
  wt := hB.wt
  ε i b := ((hB.eps hc i b : ℤ) : WithBot ℤ)
  φ i b := (((hB.eps hc i b : ℤ) + hB.wt b (R.coroot i) : ℤ) : WithBot ℤ)
  e := hB.e
  f := hB.f
  φ_eq i b := by simp
  f_eq_some_iff i b b' := by
    rw [hB.f_eq_some_iff hc, hB.e_eq_some_iff hc]
    exact hB.fQ_eq_iff i b b.2 b' b'.2
  wt_e i b b' h := hB.eQ_mk_mem_weightSpace hc i b b' ((hB.e_eq_some_iff hc i b b').1 h)
  ε_e i b b' h := by
    have hb' := (hB.e_eq_some_iff hc i b b').1 h
    have key : ∀ a, hB.eps hc i b' < a ↔ hB.eps hc i b < a + 1 := fun a ↦ by
      rw [← hB.eQ_pow_eq_zero_iff hc, ← hB.eQ_pow_eq_zero_iff hc, pow_succ,
        Module.End.mul_apply, hb']
    have h1 := (key (hB.eps hc i b')).not.1 (lt_irrefl _)
    have h2 := (key (hB.eps hc i b' + 1)).1 (Nat.lt_succ_self _)
    have : hB.eps hc i b = hB.eps hc i b' + 1 := by omega
    rw [this]
    push_cast
    rfl
  e_eq_none_of_φ_eq_bot i b h := absurd h WithBot.coe_ne_bot

lemma crystal_wt (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (b : B) :
    (hB.crystal hc).wt b = hB.wt b := rfl

lemma crystal_e (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b : B) :
    (hB.crystal hc).e i b = hB.e i b := rfl

lemma crystal_f (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (b : B) :
    (hB.crystal hc).f i b = hB.f i b := rfl

lemma isSome_eIter_iff (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (n : ℕ) (b : B) :
    ((hB.crystal hc).eIter i n b).isSome ↔ (hL.eQ c i ^ n) b.1 ≠ 0 := by
  induction n generalizing b with
  | zero =>
    simp only [Crystal.eIter_zero, Option.isSome_some, pow_zero, Module.End.one_apply, true_iff]
    exact fun h ↦ hB.zero_notMem hc (h ▸ b.2)
  | succ n ih =>
    rw [Crystal.eIter_succ, pow_succ, Module.End.mul_apply, crystal_e]
    unfold e
    split_ifs with h
    · simp [h]
    · simp only [Option.bind_some]
      exact ih _

lemma isSome_fIter_iff (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) (i : I) (n : ℕ) (b : B) :
    ((hB.crystal hc).fIter i n b).isSome ↔ (hL.fQ c i ^ n) b.1 ≠ 0 := by
  induction n generalizing b with
  | zero =>
    simp only [Crystal.fIter_zero, Option.isSome_some, pow_zero, Module.End.one_apply, true_iff]
    exact fun h ↦ hB.zero_notMem hc (h ▸ b.2)
  | succ n ih =>
    rw [Crystal.fIter_succ, pow_succ, Module.End.mul_apply, crystal_f]
    unfold f
    split_ifs with h
    · simp [h]
    · simp only [Option.bind_some]
      exact ih _

/-- The crystal of a crystal base is seminormal: `εᵢ(b) = max {a | ẽᵢᵃ b ≠ 0}` and
`φᵢ(b) = max {a | f̃ᵢᵃ b ≠ 0}` ([HK] (4.9), Prop. 4.2.11). -/
theorem isSeminormal_crystal (hB : IsCrystalBase hL c B) (hc : ¬IsUnit c) :
    (hB.crystal hc).IsSeminormal := by
  intro i b n
  rw [hB.isSome_eIter_iff hc, hB.isSome_fIter_iff hc, Ne, Ne, hB.eQ_pow_eq_zero_iff hc,
    hB.fQ_pow_eq_zero_iff hc]
  change (¬_ ↔ ((n : ℤ) : WithBot ℤ) ≤ ((hB.eps hc i b : ℤ) : WithBot ℤ)) ∧
    (¬_ ↔ ((n : ℤ) : WithBot ℤ) ≤ (((hB.eps hc i b : ℤ) + hB.wt b (R.coroot i) : ℤ) : WithBot ℤ))
  rw [WithBot.coe_le_coe, WithBot.coe_le_coe]
  omega

end IsCrystalBase

end LieLean.QuantumGroup
