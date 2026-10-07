/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.BraidAction.OrthogonalGeneral
import LieLean.Algebra.QuantumGroup.BraidAction.CoupledSerreNegative

/-!
# Morphisms of root data, diagonal automorphisms, and Lusztig's `Tᵢ`

Let `D` be a Cartan datum. A morphism of root data `φ : R → R'` of type `D` is an additive map
`φ : Y → Y'` with `φ(i) = i` on simple coroots and `⟨φ μ, j'⟩ = ⟨μ, j'⟩` on simple roots
(`LusztigCartanDatum.RootDatum.Hom`). It induces an algebra homomorphism
`U(R) → U(R')`, `Eᵢ ↦ Eᵢ`, `Fᵢ ↦ Fᵢ`, `K_μ ↦ K_{φ μ}` (`QuantumGroup.mapHom`), which intertwines
any two endomorphisms with Lusztig's generator formulas at the same node
(`QuantumGroup.mapHom_comp_of_hasBraidGeneratorImages`). Every root datum receives a morphism from
a root datum whose simple coroots are linearly independent and can be paired with arbitrary
integers (`LusztigCartanDatum.RootDatum.freeCoroot`, `freeCorootHom`, `exists_le_freeCoroot`).

For `c : I → kˣ` the diagonal automorphism `D_c` scales `Eᵢ` by `cᵢ` and `Fᵢ` by `cᵢ⁻¹`
(`QuantumGroup.diagHom`). With `ζᵢ = -vᵢ` and the Chevalley involution `ω`, Lusztig's
automorphisms satisfy `ω Tᵢ ω D_ζ = D_ζ Tᵢ` (`QuantumGroup.chevalley_comp_comp_diagHom`): on
generators this is the identity `ω(Tᵢ(Fⱼ)) = (-vᵢ)^{-aᵢⱼ} Tᵢ(Eⱼ)` of the explicit formulas.
Consequently `ω T_w ω = D_ζ T_w D_ζ⁻¹` for every word `w`.

The arguments are our own.
-/

open LieLean Finset

noncomputable section

namespace LusztigCartanDatum.RootDatum

variable {I Y Y' : Type*} [AddCommGroup Y] [AddCommGroup Y'] {D : LusztigCartanDatum I}

/-- A morphism of root data of type `D`. -/
structure Hom (R : D.RootDatum Y) (R' : D.RootDatum Y') where
  /-- The map of coweight lattices. -/
  toHom : Y →+ Y'
  map_coroot : ∀ i, toHom (R.coroot i) = R'.coroot i
  root_map : ∀ j μ, R'.root j (toHom μ) = R.root j μ

/-- The root datum on `Y × ℤ^(I)` with simple coroots `(i, eᵢ)` and simple roots `(μ, f) ↦ ⟨μ, j'⟩`;
its simple coroots can be paired with arbitrary integers. -/
def freeCoroot (R : D.RootDatum Y) : D.RootDatum (Y × (I →₀ ℤ)) where
  coroot i := (R.coroot i, Finsupp.single i 1)
  root j := (R.root j).comp (AddMonoidHom.fst Y (I →₀ ℤ))
  root_coroot i j := by simp [R.root_coroot]

/-- The projection `freeCoroot R → R`. -/
def freeCorootHom (R : D.RootDatum Y) : R.freeCoroot.Hom R where
  toHom := AddMonoidHom.fst _ _
  map_coroot _ := rfl
  root_map _ _ := rfl

lemma exists_le_freeCoroot (R : D.RootDatum Y) (N : ℕ) :
    ∃ Λ : Y × (I →₀ ℤ) →+ ℤ, ∀ i, (N : ℤ) ≤ Λ (R.freeCoroot.coroot i) :=
  ⟨(N : ℤ) • (Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id ℤ).comp (AddMonoidHom.snd _ _),
    fun i ↦ by simp [freeCoroot]⟩

end LusztigCartanDatum.RootDatum

namespace LieLean.QuantumGroup

variable {k I Y Y' : Type*} [Field k] [AddCommGroup Y] [AddCommGroup Y'] [DecidableEq I]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {R' : D.RootDatum Y'} (v : k)

/-! ### The homomorphism induced by a morphism of root data -/

omit [DecidableEq I] in
lemma Hom.map_ktilde (φ : R.Hom R') (i : I) : φ.toHom (ktilde R i) = ktilde R' i := by
  simp [ktilde, map_nsmul, φ.map_coroot]

omit [DecidableEq I] in
lemma Hom.map_reflY (φ : R.Hom R') (i : I) (μ : Y) :
    φ.toHom (reflY R i μ) = reflY R' i (φ.toHom μ) := by
  simp [reflY_apply, map_sub, map_zsmul, φ.map_coroot, φ.root_map]

/-- The relations of `U(R)` hold for the generators of `U(R')` along `φ`. -/
theorem mapHom_relations (φ : R.Hom R') :
    Relations R v (E R' v) (F R' v) ((KHom R' v).comp φ.toHom.toMultiplicative) where
  K_mul_E μ i := by
    change K R' v (φ.toHom μ) * E R' v i = _
    rw [K_mul_E, φ.root_map]
    rfl
  K_mul_F μ i := by
    change K R' v (φ.toHom μ) * F R' v i = _
    rw [K_mul_F, φ.root_map]
    rfl
  E_mul_F i j := by
    rw [E_mul_F_sub]
    split_ifs
    · change _ = _ • (K R' v (φ.toHom (ktilde R i)) - K R' v (φ.toHom (-ktilde R i)))
      rw [map_neg, Hom.map_ktilde]
    · rfl
  serre_E _ _ h := serre_E R' v h
  serre_F _ _ h := serre_F R' v h

/-- The algebra homomorphism `U(R) → U(R')` induced by a morphism of root data. -/
def mapHom (φ : R.Hom R') : QuantumGroup R v →ₐ[k] QuantumGroup R' v :=
  lift (mapHom_relations v φ)

variable {v}

@[simp] lemma mapHom_E (φ : R.Hom R') (i : I) : mapHom v φ (E R v i) = E R' v i := lift_E _ i

@[simp] lemma mapHom_F (φ : R.Hom R') (i : I) : mapHom v φ (F R v i) = F R' v i := lift_F _ i

@[simp] lemma mapHom_K (φ : R.Hom R') (μ : Y) : mapHom v φ (K R v μ) = K R' v (φ.toHom μ) :=
  lift_K _ μ

lemma mapHom_surjective (φ : R.Hom R') (hφ : Function.Surjective φ.toHom) :
    Function.Surjective (mapHom v φ) := by
  have hrange : ∀ u : QuantumGroup R' v, u ∈ (mapHom v φ).range := by
    intro u
    refine induction_on R' v u (fun c ↦ (mapHom v φ).range.algebraMap_mem c)
      (fun i ↦ ⟨E R v i, mapHom_E φ i⟩) (fun i ↦ ⟨F R v i, mapHom_F φ i⟩) (fun μ ↦ ?_)
      (fun x y hx hy ↦ add_mem hx hy) (fun x y hx hy ↦ mul_mem hx hy)
    obtain ⟨μ, rfl⟩ := hφ μ
    exact ⟨K R v μ, mapHom_K φ μ⟩
  exact fun u ↦ hrange u

/-- `mapHom` intertwines endomorphisms with Lusztig's generator formulas at the same node. -/
theorem mapHom_comp_of_hasBraidGeneratorImages (φ : R.Hom R') {i : I}
    {T : QuantumGroup R v →ₐ[k] QuantumGroup R v} {T' : QuantumGroup R' v →ₐ[k] QuantumGroup R' v}
    (H : HasBraidGeneratorImages i T) (H' : HasBraidGeneratorImages i T') :
    (mapHom v φ).comp T = T'.comp (mapHom v φ) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · simp only [AlgHom.comp_apply, mapHom_E, H.map_E, H'.map_E]
    split_ifs
    · simp [braidEi, Kt, Hom.map_ktilde]
    · simp [braidEj, serreAux, map_sum, map_smul, map_mul, map_pow]
  · simp only [AlgHom.comp_apply, mapHom_F, H.map_F, H'.map_F]
    split_ifs
    · simp [braidFi, Hom.map_ktilde]
    · simp [braidFj, serreAux, map_sum, map_smul, map_mul, map_pow]
  · simp [H.map_K, H'.map_K, Hom.map_reflY]

/-! ### Diagonal automorphisms -/

variable (R v) in
/-- The relations of `U` hold for `cᵢ Eᵢ`, `cᵢ⁻¹ Fᵢ`, `K_μ`. -/
theorem diag_relations (c : I → kˣ) :
    Relations R v (fun i ↦ (c i : k) • E R v i) (fun i ↦ (c i : k)⁻¹ • F R v i)
      (KHom R v) where
  K_mul_E μ i := by
    change K R v μ * ((c i : k) • E R v i) = v ^ R.root i μ • (((c i : k) • E R v i) * K R v μ)
    rw [mul_smul_comm, K_mul_E, smul_mul_assoc, smul_comm]
  K_mul_F μ i := by
    change K R v μ * ((c i : k)⁻¹ • F R v i) =
      v ^ (-R.root i μ) • (((c i : k)⁻¹ • F R v i) * K R v μ)
    rw [mul_smul_comm, K_mul_F, smul_mul_assoc, smul_comm]
  E_mul_F i j := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm ((c j : k)⁻¹), ← smul_sub, E_mul_F_sub]
    split_ifs with h
    · subst h
      rw [mul_inv_cancel₀ (Units.ne_zero _), one_smul]
      rfl
    · rw [smul_zero]
  serre_E i j h := by rw [qSerre_smul_smul, serre_E R v h, smul_zero]
  serre_F i j h := by rw [qSerre_smul_smul, serre_F R v h, smul_zero]

variable (R v) in
/-- The diagonal automorphism `Eᵢ ↦ cᵢ Eᵢ`, `Fᵢ ↦ cᵢ⁻¹ Fᵢ`, `K_μ ↦ K_μ`. -/
def diagHom (c : I → kˣ) : QuantumGroup R v →ₐ[k] QuantumGroup R v := lift (diag_relations R v c)

@[simp] lemma diagHom_E (c : I → kˣ) (i : I) :
    diagHom R v c (E R v i) = (c i : k) • E R v i := lift_E _ i

@[simp] lemma diagHom_F (c : I → kˣ) (i : I) :
    diagHom R v c (F R v i) = (c i : k)⁻¹ • F R v i := lift_F _ i

@[simp] lemma diagHom_K (c : I → kˣ) (μ : Y) : diagHom R v c (K R v μ) = K R v μ := lift_K _ μ

lemma diagHom_comp_diagHom (c c' : I → kˣ) :
    (diagHom R v c).comp (diagHom R v c') = diagHom R v (c * c') := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · simp [smul_smul, mul_comm]
  · simp [smul_smul, mul_comm]
  · simp

lemma diagHom_one : diagHom R v 1 = AlgHom.id k (QuantumGroup R v) := by
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_) <;> simp

/-! ### The Chevalley involution and Lusztig's `Tᵢ` -/

omit [DecidableEq I] in
lemma serreAux_smul_smul' {B : Type*} [Ring B] [Algebra k B] (c x : k) (m : ℕ) (a b : B)
    (α β : k) : serreAux c x m (α • a) (β • b) = (α ^ m * β) • serreAux c x m a b := by
  simp only [serreAux, Finset.smul_sum, smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  simp only [mem_range] at hr
  congr 1
  have : α ^ m = α ^ (m - r) * α ^ r := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [this]
  ring

variable (D v) in
/-- `ζᵢ = -vᵢ`, the scalars relating `ω Tᵢ ω` and `Tᵢ`. -/
def chevalleyScalar [NeZero v] (i : I) : kˣ :=
  Units.mk0 (-(v ^ D.d i)) (neg_ne_zero.2 (pow_ne_zero _ (NeZero.ne v)))

/-- **`ω Tᵢ ω D_ζ = D_ζ Tᵢ`** for any endomorphism `Tᵢ` with Lusztig's generator formulas, where
`ω` is the Chevalley involution and `D_ζ` the diagonal automorphism with `ζⱼ = -vⱼ`. -/
theorem chevalley_comp_comp_diagHom [NeZero v] {i : I}
    {T : QuantumGroup R v →ₐ[k] QuantumGroup R v} (H : HasBraidGeneratorImages i T) :
    (chevalley R v).comp (T.comp ((chevalley R v).comp (diagHom R v (chevalleyScalar D v)))) =
      (diagHom R v (chevalleyScalar D v)).comp T := by
  have hv := NeZero.ne v
  have hq : v ^ D.d i ≠ 0 := pow_ne_zero _ hv
  refine hom_ext (fun l ↦ ?_) (fun l ↦ ?_) (fun μ ↦ ?_)
  · simp only [AlgHom.comp_apply, diagHom_E, map_smul, chevalley_E, H.map_F, H.map_E]
    by_cases hl : l = i
    · subst hl
      simp only [↓reduceIte, braidFi, braidEi, map_neg, map_mul, chevalley_K, chevalley_E,
        diagHom_F, diagHom_K, Kt, smul_neg, neg_inj, smul_mul_assoc]
      rw [show K R v (-(-ktilde R l)) * F R v l = (v ^ D.d l) ^ (-2 : ℤ) • (F R v l * Kt R v l) by
        rw [neg_neg, K_mul_F, root_ktilde, D.cartanMatrix_self]
        congr 1
        rw [← zpow_natCast, ← zpow_mul]
        ring_nf]
      rw [smul_smul]
      congr 1
      simp only [chevalleyScalar, Units.val_mk0]
      field_simp
    · simp only [hl, ↓reduceIte, braidFj, braidEj, map_smul, smul_smul]
      rw [show chevalley R v (serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i l) (F R v i)
          (F R v l)) = serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i l) (E R v i) (E R v l) by
        simp [serreAux, map_sum, map_smul, map_mul, map_pow],
        show diagHom R v (chevalleyScalar D v) (serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i l)
          (E R v i) (E R v l)) = serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i l)
            ((chevalleyScalar D v i : k) • E R v i) ((chevalleyScalar D v l : k) • E R v l) by
        simp [serreAux, map_sum, map_smul, map_mul, map_pow],
        serreAux_smul_smul', smul_smul]
      congr 1
      simp only [chevalleyScalar, Units.val_mk0]
      rw [neg_pow (v ^ D.d i)]
      ring
  · simp only [AlgHom.comp_apply, diagHom_F, map_smul, chevalley_F, H.map_F, H.map_E]
    by_cases hl : l = i
    · subst hl
      simp only [↓reduceIte, braidFi, braidEi, map_neg, map_mul, chevalley_K, chevalley_F,
        diagHom_E, diagHom_K, Kt, smul_neg, neg_inj, mul_smul_comm]
      rw [show K R v (-ktilde R l) * E R v l = (v ^ D.d l) ^ (-2 : ℤ) • (E R v l *
          K R v (-ktilde R l)) by
        rw [K_mul_E, map_neg, root_ktilde, D.cartanMatrix_self]
        congr 1
        rw [← zpow_natCast, ← zpow_mul]
        ring_nf]
      rw [smul_smul]
      congr 1
      simp only [chevalleyScalar, Units.val_mk0]
      field_simp
    · simp only [hl, ↓reduceIte, braidFj, braidEj, map_smul, smul_smul]
      rw [show chevalley R v (serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i l) (E R v i)
          (E R v l)) = serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i l) (F R v i) (F R v l) by
        simp [serreAux, map_sum, map_smul, map_mul, map_pow],
        show diagHom R v (chevalleyScalar D v) (serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i l)
          (F R v i) (F R v l)) = serreAux (v ^ D.d i) (v ^ D.d i)⁻¹ (negA D i l)
            ((chevalleyScalar D v i : k)⁻¹ • F R v i) ((chevalleyScalar D v l : k)⁻¹ • F R v l) by
        simp [serreAux, map_sum, map_smul, map_mul, map_pow],
        serreAux_smul_smul', smul_smul]
      congr 1
      simp only [chevalleyScalar, Units.val_mk0]
      rw [inv_pow, neg_pow (v ^ D.d i)]
      field_simp
  · simp [H.map_K, map_neg, reflY]

end LieLean.QuantumGroup
