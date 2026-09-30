/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.RepresentationTheory.Crystal.Path.LittelmannIsomorphism

/-!
# Levi restriction of the path crystal and normality of `B(λ)`

Let `e : κ → ι` be an injective map of index sets (a subdiagram `J = e(κ)`), `A_J` the
principal submatrix, and `Q` a realization of `A_J`. A linear map `r : 𝔥* → 𝔥_J*` with
`r(α_{e k}) = α_k^J` and `⟨r v, α_k^{J∨}⟩ = ⟨v, α_{e k}^∨⟩` (`LeviMap`) exists for every
realization `Q` (`exists_leviMap`). Composing paths with `r` intertwines the root operators
`e_{e k}, f_{e k}` with the Levi root operators `e_k, f_k` (`e_restrict`, `f_restrict`), and is
injective on the `J`-components (`restrict_injOn_jComponent`).

## Main results

* `jComponent_bijOn`: the `J`-component of a path (its closure under `e_j, f_j`, `j ∈ J`) is
  mapped bijectively onto the component of the restricted path in the Levi path crystal,
  compatibly with all `J`-words.
* `componentIso_straightLine_restrict`: if `π ∈ B(λ)` is `J`-highest (`e_j π = 0` for `j ∈ J`),
  the Levi component of the restricted path is isomorphic to the Levi crystal `B_J(μ)`,
  `μ = r(π(1))`, with `π_μ ↦ r ∘ π`. Hence every `J`-component of `B(λ)` through a
  `J`-highest path is isomorphic, as a `J`-crystal, to a highest-weight crystal `B_J(μ)`.
* `exists_jHighest`: every `J`-component of `B(λ)` contains a `J`-highest path.
* `LeviMap.exists_jHighest_componentIso`: the three combined, with `jComponent_eq_of_mem`
  (`J`-components are the classes of an equivalence relation).

Together: the restriction of `B(λ)` to any subdiagram `J` (of finite type or not) is a
disjoint union of highest-weight Levi path crystals `B_J(μ)`, the `J`-highest paths indexing
the components (Littelmann's restriction rule). For `J = {i}` every `i`-string of `B(λ)` is a
copy of the `sl₂` path crystal `B(n)`. This is normality of `B(λ)` relative to the path model;
the identification of `B_J(μ)` with the crystal base of the irreducible `U_q(𝔤_J)`-module
(needed for normality in Kashiwara's sense) is not formalized here.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*,
  Invent. Math. 116 (1994), 329–346, restriction rule (check).
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. (2) 142
  (1995), 499–525, Theorem 7.1 (the isomorphism theorem, applied to the Levi datum).
* M. Kashiwara, *Crystal bases of modified quantized enveloping algebra*, Duke Math. J. 73
  (1994), 383–413, §1.5 (normal crystals) (check).

The arguments are reconstructed: the Levi path crystal is the path crystal of an auxiliary
realization of `A_J`, reached by a linear restriction map, and Theorem 7.1 is applied there.
-/

open Set Module LittelmannPath

namespace Matrix.Realization.LSGeneralClass

variable {ι κ H H' : Type*} [Fintype ι] [Fintype κ] [AddCommGroup H] [Module ℝ H]
  [AddCommGroup H'] [Module ℝ H']
  {A : Matrix ι ι ℤ} {P : Realization A ℝ H} {hA : A.IsGeneralizedCartan}
  {e : κ → ι} {Q : Realization (A.submatrix e e) ℝ H'}
  {hA' : (A.submatrix e e).IsGeneralizedCartan}

variable (P Q e) in
/-- A restriction map from the weights of `P` to the weights of the Levi realization `Q`. -/
structure LeviMap where
  /-- The underlying linear map `𝔥* → 𝔥_J*`. -/
  toLinearMap : Dual ℝ H →ₗ[ℝ] Dual ℝ H'
  map_root : ∀ k, toLinearMap (P.root (e k)) = Q.root k
  apply_coroot : ∀ v k, toLinearMap v (Q.coroot k) = v (P.coroot (e k))

omit [Fintype ι] [Fintype κ] in
/-- A principal submatrix of a generalized Cartan matrix is a generalized Cartan matrix. -/
theorem isGeneralizedCartan_submatrix (hA : A.IsGeneralizedCartan) (he : Function.Injective e) :
    (A.submatrix e e).IsGeneralizedCartan where
  diag k := hA.diag (e k)
  offDiag_nonpos _ _ hkl := hA.offDiag_nonpos _ _ (he.ne hkl)
  zero_comm k l := hA.zero_comm (e k) (e l)

/-- Every realization of a principal submatrix admits a restriction map. -/
theorem exists_leviMap [FiniteDimensional ℝ H] (he : Function.Injective e)
    (Q : Realization (A.submatrix e e) ℝ H') : Nonempty (LeviMap P e Q) := by
  classical
  have hsurj : ∀ g : κ → ℝ, ∃ h : H, ∀ k, P.root (e k) h = g k := by
    intro g
    obtain ⟨h, hh⟩ := P.rootMap_surjective (Function.extend e g 0)
    refine ⟨h, fun k => ?_⟩
    have := congr_fun hh (e k)
    rwa [rootMap_apply, he.extend_apply] at this
  choose lift hlift using hsurj
  set s : Set H' := range Q.coroot
  have hs : LinearIndepOn ℝ id s := Q.linearIndependent_coroot.linearIndepOn_id
  let b := Basis.extend hs
  have hinj : Function.Injective Q.coroot := Q.linearIndependent_coroot.injective
  let val : H' → H := fun x =>
    if hx : x ∈ s then P.coroot (e hx.choose) else lift fun k => Q.root k x
  let φ : H' →ₗ[ℝ] H := b.constr ℝ fun y => val y
  have hsub : s ⊆ hs.extend (subset_univ s) := Basis.subset_extend hs
  have hφc : ∀ k, φ (Q.coroot k) = P.coroot (e k) := by
    intro k
    have hk : Q.coroot k ∈ s := ⟨k, rfl⟩
    have hb : b ⟨Q.coroot k, hsub hk⟩ = Q.coroot k := by simp [b]
    rw [← hb, b.constr_basis]
    change val (Q.coroot k) = _
    simp only [val, hk, ↓reduceDIte]
    rw [hinj hk.choose_spec]
  have hφr : ∀ k (h : H'), P.root (e k) (φ h) = Q.root k h := by
    intro k h
    have hlin : (P.root (e k)).comp φ = Q.root k := by
      refine b.ext fun y => ?_
      rw [LinearMap.comp_apply, b.constr_basis]
      have hb : (b y : H') = y := by simp [b]
      rw [hb]
      change P.root (e k) (val y) = _
      by_cases hy : (y : H') ∈ s
      · simp only [val, hy, ↓reduceDIte]
        have hc : Q.root k (y : H') = Q.root k (Q.coroot hy.choose) := by
          rw [hy.choose_spec]
        rw [hc, P.root_coroot, Q.root_coroot, submatrix_apply]
      · simp only [val, hy, ↓reduceDIte]
        exact hlift _ k
    exact LinearMap.congr_fun hlin h
  exact ⟨{ toLinearMap := φ.dualMap
           map_root := fun k => LinearMap.ext fun h => hφr k h
           apply_coroot := fun v k => by
             change v (φ (Q.coroot k)) = _
             rw [hφc] }⟩

namespace LeviMap

variable (L : LeviMap P e Q)

/-- The restriction map is injective on the span of the roots of `J`. -/
theorem eq_zero_of_mem_span {v : Dual ℝ H} (hv : v ∈ Submodule.span ℝ (range (P.root ∘ e)))
    (h : L.toLinearMap v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  have h' : ∑ k, c k • Q.root k = 0 := by
    rw [← h, map_sum]
    simp only [map_smul, Function.comp_apply, L.map_root]
  have hc := Fintype.linearIndependent_iff.mp Q.linearIndependent_root c h'
  simp [hc]

/-- Restriction preserves integrality. -/
theorem map_mem_integralWeights {v : Dual ℝ H} (hv : v ∈ P.integralWeights) :
    L.toLinearMap v ∈ Q.integralWeights := by
  intro k
  rw [L.apply_coroot]
  exact hv (e k)

/-- The restricted path `r ∘ π` in the Levi path crystal. -/
noncomputable def restrict (π : LittelmannPath (P.pathSpace hA)) :
    LittelmannPath (Q.pathSpace hA') where
  toFun t := L.toLinearMap (π t)
  wt := ⟨L.toLinearMap π.wt, L.map_mem_integralWeights π.wt.2⟩
  toFun_of_nonpos' t ht := by rw [π.apply_of_nonpos ht, map_zero]
  toFun_of_one_le' t ht := by rw [π.apply_of_one_le ht, pathSpace_embed, pathSpace_embed]
  continuous_coroot' k := by
    simp only [pathSpace_coroot, L.apply_coroot]
    exact π.continuous_pairing (e k)

theorem restrict_apply (π : LittelmannPath (P.pathSpace hA)) (t : ℝ) :
    L.restrict (hA' := hA') π t = L.toLinearMap (π t) := rfl

theorem pairing_restrict (π : LittelmannPath (P.pathSpace hA)) (k : κ) :
    (L.restrict (hA' := hA') π).pairing k = π.pairing (e k) := by
  funext t
  simp only [pairing, pathSpace_coroot, restrict_apply, L.apply_coroot]

theorem runningMin_restrict (π : LittelmannPath (P.pathSpace hA)) (k : κ) (t : ℝ) :
    (L.restrict (hA' := hA') π).runningMin k t = π.runningMin (e k) t := by
  simp only [runningMin, pairing_restrict]

theorem minPairing_restrict (π : LittelmannPath (P.pathSpace hA)) (k : κ) :
    (L.restrict (hA' := hA') π).minPairing k = π.minPairing (e k) :=
  L.runningMin_restrict π k 1

theorem eCoeff_restrict (π : LittelmannPath (P.pathSpace hA)) (k : κ) (t : ℝ) :
    (L.restrict (hA' := hA') π).eCoeff k t = π.eCoeff (e k) t := by
  simp only [eCoeff, runningMin_restrict, minPairing_restrict]

/-- Restriction intertwines `e_{e k}` with the Levi operator `e_k`. -/
theorem e_restrict (π : LittelmannPath (P.pathSpace hA)) (k : κ) :
    LittelmannPath.e k (L.restrict (hA' := hA') π) =
      (LittelmannPath.e (e k) π).map L.restrict := by
  by_cases hQ : π.minPairing (e k) ≤ -1
  · have hQ' : (L.restrict (hA' := hA') π).minPairing k ≤ -1 := by
      rwa [minPairing_restrict]
    rw [e_of_le hQ', e_of_le hQ, Option.map_some]
    congr 1
    apply LittelmannPath.ext
    intro t
    rw [eRaw_apply, restrict_apply, restrict_apply, eRaw_apply, map_sub, map_smul,
      eCoeff_restrict]
    congr 2
    exact (L.map_root k).symm
  · have hQ' : ¬(L.restrict (hA' := hA') π).minPairing k ≤ -1 := by
      rwa [minPairing_restrict]
    simp only [LittelmannPath.e, hQ, hQ', ↓reduceDIte, Option.map_none]

theorem restrict_rev (π : LittelmannPath (P.pathSpace hA)) :
    L.restrict (hA' := hA') π.rev = (L.restrict π).rev := by
  apply LittelmannPath.ext
  intro t
  rw [restrict_apply, rev_apply, rev_apply, restrict_apply, restrict_apply, map_sub]

/-- Restriction intertwines `f_{e k}` with the Levi operator `f_k`. -/
theorem f_restrict (π : LittelmannPath (P.pathSpace hA)) (k : κ) :
    LittelmannPath.f k (L.restrict (hA' := hA') π) =
      (LittelmannPath.f (e k) π).map L.restrict := by
  rw [LittelmannPath.f, LittelmannPath.f, ← restrict_rev, e_restrict, Option.map_map,
    Option.map_map]
  congr 1
  funext ρ
  exact (L.restrict_rev ρ).symm

/-- A `J`-word as a word on all of `ι`. -/
def liftWord (e : κ → ι) (u : List (κ ⊕ κ)) : List (ι ⊕ ι) := u.map (Sum.map e e)

/-- Restriction intertwines all `J`-words. -/
theorem rootWord_restrict (u : List (κ ⊕ κ)) (π : LittelmannPath (P.pathSpace hA)) :
    rootWord u (L.restrict (hA' := hA') π) =
      (rootWord (liftWord e u) π).map L.restrict := by
  induction u generalizing π with
  | nil => rfl
  | cons a u ih =>
    have hstep : rootStep a (L.restrict (hA' := hA') π) =
        (rootStep (Sum.map e e a) π).map L.restrict := by
      cases a with
      | inl k => exact L.e_restrict π k
      | inr k => exact L.f_restrict π k
    change (rootStep a (L.restrict π)).bind (rootWord u) =
      ((rootStep (Sum.map e e a) π).bind (rootWord (liftWord e u))).map L.restrict
    rw [hstep]
    cases rootStep (Sum.map e e a) π with
    | none => rfl
    | some ρ => exact ih ρ

end LeviMap

/-- The `J`-component of a path: its images under all `J`-words (words in `e_j, f_j`,
`j ∈ J = e(κ)`). -/
def jComponent (e : κ → ι) (π : LittelmannPath (P.pathSpace hA)) :
    Set (LittelmannPath (P.pathSpace hA)) :=
  {x | ∃ u : List (κ ⊕ κ), rootWord (LeviMap.liftWord e u) π = some x}

omit [Fintype κ] in
/-- A `J`-letter changes a path pointwise by an element of the span of the `J`-roots. -/
theorem rootStep_sub_mem_span {π y : LittelmannPath (P.pathSpace hA)} {a : κ ⊕ κ}
    (h : rootStep (Sum.map e e a) π = some y) (t : ℝ) :
    y t - π t ∈ Submodule.span ℝ (range (P.root ∘ e)) := by
  cases a with
  | inl k =>
    change LittelmannPath.e (e k) π = some y at h
    obtain ⟨hQ, rfl⟩ := e_eq_some_iff.mp h
    rw [eRaw_apply, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  | inr k =>
    change LittelmannPath.f (e k) π = some y at h
    have key : ∀ s ∈ Icc (0 : ℝ) 1,
        y s - π s ∈ Submodule.span ℝ (range (P.root ∘ e)) := by
      intro s hs
      rw [f_apply h hs, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
    rcases le_or_gt t 0 with ht | ht
    · rw [y.apply_of_nonpos ht, π.apply_of_nonpos ht, sub_zero]
      exact zero_mem _
    rcases le_or_gt t 1 with ht1 | ht1
    · exact key t ⟨ht.le, ht1⟩
    · rw [y.apply_of_one_le ht1.le, π.apply_of_one_le ht1.le, ← y.apply_one, ← π.apply_one]
      exact key 1 ⟨zero_le_one, le_rfl⟩

omit [Fintype κ] in
/-- Every path of the `J`-component of `π` differs from `π` pointwise by an element of the span
of the `J`-roots. -/
theorem sub_mem_span_of_mem_jComponent {π x : LittelmannPath (P.pathSpace hA)}
    (hx : x ∈ jComponent e π) (t : ℝ) :
    x t - π t ∈ Submodule.span ℝ (range (P.root ∘ e)) := by
  obtain ⟨u, hu⟩ := hx
  induction u generalizing π with
  | nil =>
    cases hu
    rw [sub_self]
    exact zero_mem _
  | cons a u ih =>
    obtain ⟨ρ, ha, hl⟩ := Option.bind_eq_some_iff.mp hu
    rw [← sub_add_sub_cancel _ (ρ t)]
    exact add_mem (ih hl) (rootStep_sub_mem_span ha t)

namespace LeviMap

variable (L : LeviMap P e Q)

/-- Restriction is injective on every `J`-component. -/
theorem restrict_injOn_jComponent (π : LittelmannPath (P.pathSpace hA)) :
    InjOn (L.restrict (hA' := hA')) (jComponent e π) := by
  intro x hx y hy hxy
  apply LittelmannPath.ext
  intro t
  have hmem : x t - y t ∈ Submodule.span ℝ (range (P.root ∘ e)) := by
    rw [← sub_sub_sub_cancel_right _ _ (π t)]
    exact sub_mem (sub_mem_span_of_mem_jComponent hx t) (sub_mem_span_of_mem_jComponent hy t)
  have hr : L.toLinearMap (x t - y t) = 0 := by
    have := congrArg (fun ρ : LittelmannPath (Q.pathSpace hA') => ρ t) hxy
    simp only [restrict_apply] at this
    rw [map_sub, this, sub_self]
  exact sub_eq_zero.mp (L.eq_zero_of_mem_span hmem hr)

/-- **Levi branching of the path crystal**: restriction maps the `J`-component of `π`
bijectively onto the component of `r ∘ π` in the Levi path crystal (and intertwines all
`J`-words, `rootWord_restrict`). -/
theorem jComponent_bijOn (π : LittelmannPath (P.pathSpace hA)) :
    BijOn (L.restrict (hA' := hA')) (jComponent e π) (L.restrict π).component := by
  refine ⟨fun x hx => ?_, L.restrict_injOn_jComponent π, fun y hy => ?_⟩
  · obtain ⟨u, hu⟩ := hx
    refine (mem_component_iff_rootWord _ _).mpr ⟨u, ?_⟩
    rw [L.rootWord_restrict, hu, Option.map_some]
  · obtain ⟨u, hu⟩ := (mem_component_iff_rootWord _ _).mp hy
    rw [L.rootWord_restrict] at hu
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hu
    exact ⟨x, ⟨u, hx⟩, rfl⟩

end LeviMap

/-- A common denominator for the vertices of a presentation: `N π(a_j)` is integral for all
break points `a_j`. -/
theorem Presentation.exists_denominator (σ : Presentation P hA) :
    ∃ N : ℕ, 0 < N ∧ ∀ j, (N : ℝ) • σ.path (σ.a j) ∈ P.integralWeights := by
  obtain ⟨N, hN, hNa⟩ := exists_common_denominator σ.a
  refine ⟨N, hN, fun j => ?_⟩
  have ha1 : (σ.a (Fin.last (σ.n + 1)) : ℝ) = 1 := by rw [σ.one]; simp
  induction j using Fin.lastCases with
  | last =>
    rw [ha1, σ.path.apply_one, pathSpace_embed]
    exact natCast_smul_mem_integralWeights σ.path.wt.2 N
  | cast k =>
    have hc := σ.congruence k (σ.a k.castSucc) ⟨le_rfl, by
      exact_mod_cast σ.mono.monotone Fin.castSucc_lt_succ.le⟩
    have hr := LSAChainBridge.rootLattice_le_integralWeights hc
    obtain ⟨z, hz⟩ := hNa k.castSucc
    have hsplit : (N : ℝ) • σ.path (σ.a k.castSucc) =
        (N : ℝ) • (σ.path (σ.a k.castSucc) - (σ.a k.castSucc : ℝ) • (σ.x k : Dual ℝ H)) +
          (z : ℝ) • (σ.x k : Dual ℝ H) := by
      rw [← hz, smul_sub, smul_smul]
      abel
    rw [hsplit]
    exact add_mem (natCast_smul_mem_integralWeights hr N)
      (intCast_smul_mem_integralWeights (σ.x k).2 z)

/-- **Normality of `B(λ)` along a subdiagram**: if `π ∈ B(λ)` is `J`-highest (`e_j π = 0` for all
`j ∈ J`), the Levi component of the restricted path `r ∘ π` is isomorphic to the highest-weight
Levi path crystal `B_J(μ)`, `μ = r(π(1))`, with `π_μ ↦ r ∘ π`. Together with `jComponent_bijOn`,
the `J`-component of `π` in `B(λ)` is a copy of `B_J(μ)`. This is Littelmann's restriction rule
([Lit94] (check); [Lit95] Theorem 7.1 applied to the Levi datum); reconstructed. -/
theorem LeviMap.componentIso_straightLine_restrict [FiniteDimensional ℝ H']
    (L : LeviMap P e Q) {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ)
    {π : LittelmannPath (P.pathSpace hA)}
    (hπ : π ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component)
    (hJ : ∀ k, LittelmannPath.e (e k) π = none) :
    ComponentIso (straightLine (Q.pathSpace hA') (L.restrict (hA' := hA') π).wt)
      (L.restrict π) := by
  obtain ⟨σ, rfl⟩ := exists_presentation_of_mem_component _ hπ
  obtain ⟨N, hN, hNint⟩ := σ.exists_denominator
  have hI := Matrix.Realization.isIntegral_of_mem_pathCrystal hA hΛ ⟨σ.path, hπ⟩
  have hmin : ∀ k, (0 : ℝ) ≤ σ.path.minPairing (e k) := by
    intro k
    have hm : -1 < σ.path.minPairing (e k) := e_eq_none_iff.mp (hJ k)
    obtain ⟨z, hz⟩ := hI (e k)
    rw [hz] at hm ⊢
    have : (-1 : ℤ) < z := by exact_mod_cast hm
    exact_mod_cast (show (0 : ℤ) ≤ z by omega)
  have ha0 : (σ.a 0 : ℝ) = 0 := by rw [σ.zero]; simp
  have ha1 : (σ.a (Fin.last (σ.n + 1)) : ℝ) = 1 := by rw [σ.one]; simp
  have hamono : StrictMono fun j => (σ.a j : ℝ) := fun i j hij => by
    change (σ.a i : ℝ) < σ.a j
    exact_mod_cast σ.mono hij
  have hanonneg : ∀ j, 0 ≤ (σ.a j : ℝ) := fun j => by
    rw [← ha0]; exact hamono.monotone (Fin.zero_le j)
  have hale1 : ∀ j, (σ.a j : ℝ) ≤ 1 := fun j => by
    rw [← ha1]; exact hamono.monotone (Fin.le_last j)
  refine componentIso_straightLine_of_rationalPieces (L.restrict σ.path) hN σ.n
    (fun j => (σ.a j : ℝ)) hamono ha0 ha1 ?_ ?_ ?_
  · intro j t ht
    have hk1 : (σ.a j.castSucc : ℝ) < σ.a j.succ := hamono Fin.castSucc_lt_succ
    simp only [L.restrict_apply]
    rw [σ.piece j t ht, σ.piece j _ ⟨le_rfl, hk1.le⟩, σ.piece j _ ⟨hk1.le, le_rfl⟩]
    have hne : (σ.a j.succ : ℝ) - σ.a j.castSucc ≠ 0 := by linarith
    have hcoef : (t - (σ.a j.castSucc : ℝ)) / ((σ.a j.succ : ℝ) - σ.a j.castSucc) *
        ((σ.a j.succ : ℝ) - σ.a j.castSucc) = t - σ.a j.castSucc := by
      field_simp
    simp only [map_add, map_smul, sub_self, zero_smul, add_zero, add_sub_cancel_left,
      smul_smul, hcoef]
  · intro j
    rw [L.restrict_apply, ← map_smul]
    exact L.map_mem_integralWeights (hNint j)
  · intro j k
    rw [L.restrict_apply, L.apply_coroot]
    have h := σ.path.minPairing_le (i := e k) ⟨hanonneg j, hale1 j⟩
    simp only [pairing, pathSpace_coroot] at h
    exact (hmin k).trans h

omit [Fintype κ] in
/-- Every `J`-component of `B(λ)` contains a `J`-highest path, reached by `J`-raising
operators. -/
theorem exists_jHighest {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ)
    {x : LittelmannPath (P.pathSpace hA)}
    (hx : x ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ∃ y ∈ jComponent e x, (∀ k, LittelmannPath.e (e k) y = none) ∧
      y ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component := by
  classical
  set π₀ := straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩ with hπ₀
  have hwt : ∀ z ∈ π₀.component, ∃ k : ι → ℤ, 0 ≤ k ∧ (z.wt : Dual ℝ H) = Λ - P.rootOf k :=
    fun z hz => exists_wt_eq_sub_rootOf_pathCrystal (hA := hA) hΛ ⟨z, hz⟩
  -- Raising by `e_j` adds `α_j` to the weight, so lowers the height of `Λ - wt` by one.
  have hraise : ∀ z ∈ π₀.component, ∀ k : ι → ℤ, (z.wt : Dual ℝ H) = Λ - P.rootOf k →
      ∀ j z', LittelmannPath.e (e j) z = some z' →
        z' ∈ π₀.component ∧ ∃ k' : ι → ℤ, 0 ≤ k' ∧ (z'.wt : Dual ℝ H) = Λ - P.rootOf k' ∧
          k = k' + Pi.single (e j) 1 := by
    intro z hz k hkw j z' hz'
    have hz'B : z' ∈ π₀.component := π₀.isStable_component.e_mem (e j) z z' hz hz'
    obtain ⟨k', hk', hkw'⟩ := hwt z' hz'B
    refine ⟨hz'B, k', hk', hkw', ?_⟩
    have hw := wt_of_e_eq_some hz'
    have hw' : (z'.wt : Dual ℝ H) = z.wt + P.root (e j) := by
      rw [hw]; rfl
    apply P.rootOf_injective
    rw [map_add, rootOf_single]
    rw [hkw, hkw'] at hw'
    calc P.rootOf k = Λ - (Λ - P.rootOf k + P.root (e j)) + P.root (e j) := by abel
      _ = P.rootOf k' + P.root (e j) := by rw [← hw']; abel
  suffices h : ∀ n : ℕ, ∀ z ∈ π₀.component, ∀ k : ι → ℤ, 0 ≤ k →
      (z.wt : Dual ℝ H) = Λ - P.rootOf k → ∑ i, k i = n →
      ∃ y ∈ jComponent e z, (∀ k, LittelmannPath.e (e k) y = none) ∧ y ∈ π₀.component by
    obtain ⟨k, hk, hkw⟩ := hwt x hx
    have hsum : 0 ≤ ∑ i, k i := Finset.sum_nonneg fun i _ => hk i
    exact h (∑ i, k i).toNat x hx k hk hkw (Int.toNat_of_nonneg hsum).symm
  intro n
  induction n with
  | zero =>
    intro z hz k hk hkw hsum
    refine ⟨z, ⟨[], rfl⟩, fun j => ?_, hz⟩
    by_contra hne
    obtain ⟨z', hz'⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨-, k', hk', -, hkk⟩ := hraise z hz k hkw j z' hz'
    have := congrArg (fun f : ι → ℤ => ∑ i, f i) hkk
    have hk'sum : 0 ≤ ∑ i, k' i := Finset.sum_nonneg fun i _ => hk' i
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single'] at this
    simp at this
    omega
  | succ n ih =>
    intro z hz k hk hkw hsum
    by_cases hall : ∀ j, LittelmannPath.e (e j) z = none
    · exact ⟨z, ⟨[], rfl⟩, hall, hz⟩
    push Not at hall
    obtain ⟨j, hj⟩ := hall
    obtain ⟨z', hz'⟩ := Option.ne_none_iff_exists'.mp hj
    obtain ⟨hz'B, k', hk', hkw', hkk⟩ := hraise z hz k hkw j z' hz'
    have hsum' : ∑ i, k' i = n := by
      have := congrArg (fun f : ι → ℤ => ∑ i, f i) hkk
      simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single'] at this
      simp at this
      omega
    obtain ⟨y, ⟨u, hu⟩, hye, hyB⟩ := ih z' hz'B k' hk' hkw' hsum'
    refine ⟨y, ⟨.inl j :: u, ?_⟩, hye, hyB⟩
    change (LittelmannPath.e (e j) z).bind (rootWord (LeviMap.liftWord e u)) = some y
    rw [hz', Option.bind_some]
    exact hu

omit [Fintype ι] [Fintype κ] in
/-- Lifting commutes with inverting words. -/
theorem invWord_liftWord (u : List (κ ⊕ κ)) :
    invWord (LeviMap.liftWord e u) = LeviMap.liftWord e (invWord u) := by
  simp only [invWord, LeviMap.liftWord, List.map_reverse, List.map_map]
  congr 2
  funext a
  cases a <;> rfl

omit [Fintype κ] in
/-- Being in the same `J`-component is symmetric. -/
theorem mem_jComponent_comm {x y : LittelmannPath (P.pathSpace hA)} :
    y ∈ jComponent e x ↔ x ∈ jComponent e y := by
  suffices h : ∀ x y : LittelmannPath (P.pathSpace hA), y ∈ jComponent e x → x ∈ jComponent e y
    from ⟨h x y, h y x⟩
  rintro x y ⟨u, hu⟩
  refine ⟨invWord u, ?_⟩
  rw [← invWord_liftWord]
  exact (rootWord_invWord_eq_some_iff _).mp hu

omit [Fintype κ] in
/-- `J`-components are equal or disjoint: they are the classes of an equivalence relation. -/
theorem jComponent_eq_of_mem {x y : LittelmannPath (P.pathSpace hA)}
    (h : y ∈ jComponent e x) : jComponent e y = jComponent e x := by
  have trans : ∀ a b c : LittelmannPath (P.pathSpace hA),
      b ∈ jComponent e a → c ∈ jComponent e b → c ∈ jComponent e a := by
    rintro a b c ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u ++ v, ?_⟩
    rw [LeviMap.liftWord, List.map_append, rootWord_append_eq_bind]
    rw [LeviMap.liftWord] at hu hv
    rw [hu, Option.bind_some, hv]
  ext z
  exact ⟨fun hz => trans _ _ _ h hz,
    fun hz => trans _ _ _ (mem_jComponent_comm.mp h) hz⟩

/-- **The restriction of `B(λ)` to a subdiagram is a disjoint union of Levi highest-weight
crystals** (normality of `B(λ)` along `J`; Littelmann's restriction rule, [Lit94] (check),
[Lit95] Theorem 7.1 for the Levi datum; reconstructed): every `J`-component of `B(λ)` equals the
`J`-component of a `J`-highest path `y ∈ B(λ)`, restriction maps it bijectively onto the Levi
component of `r ∘ y`, and that Levi component is isomorphic to `B_J(μ)`, `μ = r(y(1))`,
with `π_μ ↦ r ∘ y`. -/
theorem LeviMap.exists_jHighest_componentIso [FiniteDimensional ℝ H']
    (L : LeviMap P e Q) {Λ : Dual ℝ H} (hΛ : P.IsDominantIntegral Λ)
    {x : LittelmannPath (P.pathSpace hA)}
    (hx : x ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component) :
    ∃ y ∈ (straightLine (P.pathSpace hA) ⟨Λ, hΛ.mem_integralWeights⟩).component,
      (∀ k, LittelmannPath.e (e k) y = none) ∧ jComponent e x = jComponent e y ∧
      BijOn (L.restrict (hA' := hA')) (jComponent e y) (L.restrict y).component ∧
      ComponentIso (straightLine (Q.pathSpace hA') (L.restrict (hA' := hA') y).wt)
        (L.restrict y) := by
  obtain ⟨y, hyx, hye, hyB⟩ := exists_jHighest (e := e) hΛ hx
  exact ⟨y, hyB, hye, (jComponent_eq_of_mem hyx).symm, L.jComponent_bijOn y,
    L.componentIso_straightLine_restrict hΛ hyB hye⟩

end Matrix.Realization.LSGeneralClass
