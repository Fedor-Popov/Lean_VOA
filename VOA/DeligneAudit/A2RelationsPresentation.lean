/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2RelationsSingular
import VOA.Filtered.LiGradedModeLeibniz
import VOA.Filtered.LiC2Bridge
import VOA.Filtered.LiGeneratorWords

/-!
# The explicit A₂ presentation: `I₂ⁿˢ` lies in the `C₂` kernel of `L_{-3/2}(sl₃)`

Write `φ : ℂ[X₀,…,X₇] → gr^Li L_{-3/2}(sl₃)` for the current-coordinate map
`X a ↦ [generator a (-1) 𝟙]` into Li degree zero (the map of `CurrentC2Presentation`).

1. `aeval_relationPoly_two`: `φ (relationPoly 2) = 0`.  The state representing
   `2 · relationPoly 2` differs from the image of `singVec` by `3 e₁₂(-2)𝟙 ∈ C₂`, and `singVec`
   vanishes in the simple quotient (`simpleProjection_singVec`).
2. `aeval_adPoly`: the zero mode `{[g_b], ·}` of a current is a derivation of the Li graded
   algebra (`liAssociatedGradedMode_leibniz`) that matches the coadjoint derivation `adPoly b`
   of the polynomial ring on the generators.  Hence `ker φ` is `ad`-stable.
3. Seven explicit polynomial identities `adPoly f (relationPoly a) = ± relationPoly a'` reach
   every relation from the highest one; so `I2ns_le_ker`.
4. `explicitPresentation : CurrentC2Presentation .A2 W` with `ideal := I2ns`, and its
   `CurrentJetSurjectivity` (the existing spanning proof does not look at the ideal).
-/

namespace VOA.DeligneAudit.A2

open VOA.AffineSl3 VOA.DeligneHigherRankConditionalCapstone MvPolynomial

noncomputable section

/-! ## Transport of modes to the simple quotient -/

theorem gen_eq_proj (a : Fin 8) :
    gen a = simpleProjection (-3 / 2) level_add_three_ne_zero
      (J (-3 / 2) a (-1) (vacuumA (-3 / 2))) := rfl

/-- Modes of the simple currents are the projections of the universal current modes. -/
theorem smul_gen_proj (a : Fin 8) (m : ℤ) (x : Vacuum (-3 / 2)) :
    W.smul (gen a) m (simpleProjection (-3 / 2) level_add_three_ne_zero x) =
      simpleProjection (-3 / 2) level_add_three_ne_zero (J (-3 / 2) a m x) := by
  change (simpleVOA (-3 / 2) level_add_three_ne_zero).smul
    (simpleProjection (-3 / 2) level_add_three_ne_zero (currentState (-3 / 2) (generator a))) m
    (simpleProjection (-3 / 2) level_add_three_ne_zero x) = _
  rw [simpleProjection_product, smulU_currentState]

theorem vacuum_eq_proj :
    W.vacuum = simpleProjection (-3 / 2) level_add_three_ne_zero (vacuumA (-3 / 2)) := rfl

/-! ## Representatives of polynomial values (any VOA, any eight weight-one states) -/

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W' : VertexOperatorAlgebra V)
  (g : Fin 8 → V) (hg : ∀ i, g i ∈ W'.grading (1 : ℤ))

/-- The current-coordinate map into Li degree zero. -/
abbrev clsG : MvPolynomial (Fin 8) ℂ →ₐ[ℂ] liAssociatedGraded W' :=
  aeval fun i => liDegreeZeroClass W' 1 ⟨g i, hg i⟩

/-- `x` is a weight-`N` representative of the value of `p`. -/
def Rep (p : MvPolynomial (Fin 8) ℂ) (N : ℕ) (x : V) : Prop :=
  ∃ hx : x ∈ W'.grading (N : ℤ), clsG W' g hg p = liDegreeZeroClass W' N ⟨x, hx⟩

theorem rep_X (i : Fin 8) : Rep W' g hg (X i) 1 (g i) := ⟨hg i, by simp⟩

variable {W' g hg}

theorem rep_add {p q : MvPolynomial (Fin 8) ℂ} {N : ℕ} {x y : V} (hp : Rep W' g hg p N x)
    (hq : Rep W' g hg q N y) : Rep W' g hg (p + q) N (x + y) := by
  obtain ⟨hx, hpx⟩ := hp
  obtain ⟨hy, hqy⟩ := hq
  refine ⟨Submodule.add_mem _ hx hy, ?_⟩
  rw [map_add, hpx, hqy]
  simp only [liDegreeZeroClass_eq_liHomogeneousClass]
  rw [← liHomogeneousClass_add]
  rfl

theorem rep_smul {p : MvPolynomial (Fin 8) ℂ} {N : ℕ} {x : V} (hp : Rep W' g hg p N x) (c : ℂ) :
    Rep W' g hg (c • p) N (c • x) := by
  obtain ⟨hx, hpx⟩ := hp
  refine ⟨Submodule.smul_mem _ c hx, ?_⟩
  rw [map_smul, hpx]
  simp only [liDegreeZeroClass_eq_liHomogeneousClass]
  rw [← liHomogeneousClass_smul]
  rfl

theorem rep_mul {p q : MvPolynomial (Fin 8) ℂ} {N M : ℕ} {x y : V} (hp : Rep W' g hg p N x)
    (hq : Rep W' g hg q M y) : Rep W' g hg (p * q) (N + M) (W'.smul x (-1) y) := by
  obtain ⟨hx, hpx⟩ := hp
  obtain ⟨hy, hqy⟩ := hq
  have hgr : W'.smul x (-1) y ∈ W'.grading ((N + M : ℕ) : ℤ) := by
    simpa using W'.smul_mem_grading hx hy (-1)
  refine ⟨hgr, ?_⟩
  rw [map_mul, hpx, hqy, liDegreeZeroClass_eq_liHomogeneousClass,
    liDegreeZeroClass_eq_liHomogeneousClass, liHomogeneousClass_mul]
  rfl

theorem rep_zero (N : ℕ) : Rep W' g hg 0 N 0 :=
  ⟨Submodule.zero_mem _, by
    rw [map_zero]
    exact (liDegreeZeroClass_eq_zero_of_mem_O₂ W' N ⟨0, Submodule.zero_mem _⟩
      (Submodule.zero_mem _)).symm⟩

theorem rep_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin 8) ℂ) {N : ℕ}
    (x : ι → V) (h : ∀ i, Rep W' g hg (p i) N (x i)) :
    Rep W' g hg (∑ i ∈ s, p i) N (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rep_zero N
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact rep_add (h a) ih

theorem clsG_eq_zero_of_rep {p : MvPolynomial (Fin 8) ℂ} {N : ℕ} {x : V}
    (hp : Rep W' g hg p N x) (hx : x ∈ O₂ W') : clsG W' g hg p = 0 := by
  obtain ⟨hxN, hpx⟩ := hp
  rw [hpx]
  exact liDegreeZeroClass_eq_zero_of_mem_O₂ W' N ⟨x, hxN⟩ hx

/-! ### Zero modes of the currents act by the coadjoint derivation -/

/-- The derivation of the polynomial ring on the generators induced by a structure table `T`:
`X i ↦ ∑ c, T b i c • X c`. -/
def adPolyT (T : Fin 8 → Fin 8 → Fin 8 → ℂ) (b : Fin 8) :
    Derivation ℂ (MvPolynomial (Fin 8) ℂ) (MvPolynomial (Fin 8) ℂ) :=
  mkDerivation ℂ fun i => ∑ c, T b i c • X c

variable (W' g hg) in
/-- The Li zero mode of a current. -/
abbrev zeroModeG (b : Fin 8) : liAssociatedGraded W' →ₗ[ℂ] liAssociatedGraded W' :=
  liAssociatedGradedMode W' 0 (liDegreeZeroClass W' 1 ⟨g b, hg b⟩)

theorem zeroModeG_one (b : Fin 8) : zeroModeG W' g hg b 1 = 0 := by
  have h := liAssociatedGradedMode_leibniz W' 0 (liDegreeZeroClass W' 1 ⟨g b, hg b⟩) 1 1
  simp only [mul_one, one_mul] at h
  change zeroModeG W' g hg b 1 = zeroModeG W' g hg b 1 + zeroModeG W' g hg b 1 at h
  linear_combination -h

/-- **The Li zero mode of a current matches the coadjoint derivation**, provided it does on the
generators. -/
theorem clsG_adPolyT (T : Fin 8 → Fin 8 → Fin 8 → ℂ)
    (hT : ∀ b i, ∃ h : W'.smul (g b) 0 (g i) ∈ W'.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W' 1 ⟨W'.smul (g b) 0 (g i), h⟩ = clsG W' g hg (∑ c, T b i c • X c))
    (b : Fin 8) (p : MvPolynomial (Fin 8) ℂ) :
    clsG W' g hg (adPolyT T b p) = zeroModeG W' g hg b (clsG W' g hg p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one, map_smul, zeroModeG_one, smul_zero]
  | add p q hp hq => rw [map_add, map_add, hp, map_add, map_add, hq]
  | mul_X p i hp =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, map_mul]
      have hX : clsG W' g hg (adPolyT T b (X i)) =
          zeroModeG W' g hg b (clsG W' g hg (X i)) := by
        obtain ⟨h, hh⟩ := hT b i
        rw [adPolyT, mkDerivation_X, ← hh, zeroModeG, clsG, aeval_X,
          liDegreeZeroClass_mode_zero W' 1 1 (by omega)]
        rfl
      rw [hX, zeroModeG, liAssociatedGradedMode_leibniz]
      ring

/-- Hence the kernel of the current-coordinate map is stable under the coadjoint derivations. -/
theorem clsG_adPolyT_eq_zero (T : Fin 8 → Fin 8 → Fin 8 → ℂ)
    (hT : ∀ b i, ∃ h : W'.smul (g b) 0 (g i) ∈ W'.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W' 1 ⟨W'.smul (g b) 0 (g i), h⟩ = clsG W' g hg (∑ c, T b i c • X c))
    (b : Fin 8) {p : MvPolynomial (Fin 8) ℂ} (hp : clsG W' g hg p = 0) :
    clsG W' g hg (adPolyT T b p) = 0 := by
  rw [clsG_adPolyT T hT, hp, map_zero]

end Generic

/-! ## The A₂ instance -/

/-- The coadjoint derivation of `sl₃` on the polynomial ring on `generator`. -/
abbrev adPoly (b : Fin 8) := adPolyT bracketTable b

theorem adPoly_X (b i : Fin 8) : adPoly b (X i) = ∑ c, bracketTable b i c • X c := by
  rw [adPoly, adPolyT, mkDerivation_X]

theorem adPoly_two_mul (b : Fin 8) (p : MvPolynomial (Fin 8) ℂ) :
    adPoly b (2 * p) = 2 * adPoly b p := by
  have : (2 : MvPolynomial (Fin 8) ℂ) * p = (2 : ℂ) • p := by
    rw [MvPolynomial.smul_eq_C_mul, map_ofNat]
  rw [this, Derivation.map_smul, MvPolynomial.smul_eq_C_mul, map_ofNat]

theorem adPoly_three_mul (b : Fin 8) (p : MvPolynomial (Fin 8) ℂ) :
    adPoly b (3 * p) = 3 * adPoly b p := by
  have : (3 : MvPolynomial (Fin 8) ℂ) * p = (3 : ℂ) • p := by
    rw [MvPolynomial.smul_eq_C_mul, map_ofNat]
  rw [this, Derivation.map_smul, MvPolynomial.smul_eq_C_mul, map_ofNat]

theorem adPoly_q (b i j : Fin 8) :
    adPoly b (q i j) = X i * (∑ c, bracketTable b j c • X c) +
      X j * (∑ c, bracketTable b i c • X c) := by
  rw [q, Derivation.leibniz, adPoly_X, adPoly_X, smul_eq_mul, smul_eq_mul]

/-- Expand `adPoly` on an explicit relation and compare by `ring`. -/
macro "adPoly_compute" : tactic => `(tactic| (
  set_option linter.unusedSimpArgs false in
  simp only [relationPoly, Fin.isValue, Matrix.cons_val, map_add, map_sub, map_neg,
    adPoly_two_mul, adPoly_three_mul, adPoly_q, Fin.sum_univ_eight, bracketTable]
  simp
  set_option linter.unusedSimpArgs false in
  simp only [MvPolynomial.smul_eq_C_mul, map_neg, map_ofNat, map_one]
  ring))

theorem adPoly_f1_R2 : adPoly 3 (relationPoly 2) = relationPoly 1 := by adPoly_compute

theorem adPoly_f2_R2 : adPoly 4 (relationPoly 2) = -relationPoly 0 := by adPoly_compute

theorem adPoly_f1_R0 : adPoly 3 (relationPoly 0) = -relationPoly 6 := by adPoly_compute

theorem adPoly_f2_R1 : adPoly 4 (relationPoly 1) = -relationPoly 7 := by adPoly_compute

theorem adPoly_f1_R7 : adPoly 3 (relationPoly 7) = -relationPoly 3 := by adPoly_compute

theorem adPoly_f2_R6 : adPoly 4 (relationPoly 6) = -relationPoly 4 := by adPoly_compute

theorem adPoly_f1_R4 : adPoly 3 (relationPoly 4) = -relationPoly 5 := by adPoly_compute

/-! ### Propagation from the highest relation (any VOA with `sl₃` current brackets) -/

section Propagate

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W' : VertexOperatorAlgebra V}
  {g : Fin 8 → V} {hg : ∀ i, g i ∈ W'.grading (1 : ℤ)}

theorem clsG_relationPoly_of_two
    (hT : ∀ b i, ∃ h : W'.smul (g b) 0 (g i) ∈ W'.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W' 1 ⟨W'.smul (g b) 0 (g i), h⟩ =
        clsG W' g hg (∑ c, bracketTable b i c • X c))
    (h2 : clsG W' g hg (relationPoly 2) = 0) (a : Fin 8) :
    clsG W' g hg (relationPoly a) = 0 := by
  have ad : ∀ (b : Fin 8) (p : MvPolynomial (Fin 8) ℂ), clsG W' g hg p = 0 →
      clsG W' g hg (adPoly b p) = 0 := fun b p hp => clsG_adPolyT_eq_zero bracketTable hT b hp
  have neg : ∀ p : MvPolynomial (Fin 8) ℂ, clsG W' g hg (-p) = 0 → clsG W' g hg p = 0 :=
    fun p h => by rwa [map_neg, neg_eq_zero] at h
  have h1 : clsG W' g hg (relationPoly 1) = 0 := by
    have := ad 3 _ h2; rwa [adPoly_f1_R2] at this
  have h0 : clsG W' g hg (relationPoly 0) = 0 := by
    have := ad 4 _ h2; rw [adPoly_f2_R2] at this; exact neg _ this
  have h6 : clsG W' g hg (relationPoly 6) = 0 := by
    have := ad 3 _ h0; rw [adPoly_f1_R0] at this; exact neg _ this
  have h7 : clsG W' g hg (relationPoly 7) = 0 := by
    have := ad 4 _ h1; rw [adPoly_f2_R1] at this; exact neg _ this
  have h3 : clsG W' g hg (relationPoly 3) = 0 := by
    have := ad 3 _ h7; rw [adPoly_f1_R7] at this; exact neg _ this
  have h4 : clsG W' g hg (relationPoly 4) = 0 := by
    have := ad 4 _ h6; rw [adPoly_f2_R6] at this; exact neg _ this
  have h5 : clsG W' g hg (relationPoly 5) = 0 := by
    have := ad 3 _ h4; rw [adPoly_f1_R4] at this; exact neg _ this
  fin_cases a
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

theorem I2ns_le_ker_of_two
    (hT : ∀ b i, ∃ h : W'.smul (g b) 0 (g i) ∈ W'.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W' 1 ⟨W'.smul (g b) 0 (g i), h⟩ =
        clsG W' g hg (∑ c, bracketTable b i c • X c))
    (h2 : clsG W' g hg (relationPoly 2) = 0) :
    I2ns ≤ RingHom.ker (clsG W' g hg).toRingHom := by
  rw [I2ns, Ideal.span_le]
  rintro _ ⟨a, rfl⟩
  exact clsG_relationPoly_of_two hT h2 a

end Propagate

/-! ### The current brackets in the simple quotient -/

/-- `g_b(0) g_i = [g_b, g_i]` in `L_{-3/2}(sl₃)`. -/
theorem smul_gen_zero (b i : Fin 8) :
    W.smul (gen b) 0 (gen i) = ∑ c, bracketTable b i c • gen c := by
  rw [gen_eq_proj i, smul_gen_proj, J_J_comm (-3 / 2) b i le_rfl (by norm_num),
    J_vac_nonneg _ le_rfl, map_zero, zero_add, if_neg (by norm_num), add_zero, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul]
  rfl

-- Heartbeats raised for the `GradedVertexOperatorAlgebra` layer:
-- the extra parent projection deepens `whnf`/`isDefEq` on this concrete VOA.
set_option maxHeartbeats 400000 in
theorem hT_A2 (b i : Fin 8) :
    ∃ h : W.smul (gen b) 0 (gen i) ∈ W.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W 1 ⟨W.smul (gen b) 0 (gen i), h⟩ =
        clsG W gen gen_weight_one (∑ c, bracketTable b i c • X c) := by
  obtain ⟨hx, hEq⟩ := rep_sum (W' := W) (g := gen) (hg := gen_weight_one) Finset.univ
    (fun c => bracketTable b i c • X c) (N := 1) (fun c => bracketTable b i c • gen c)
    (fun c => rep_smul (rep_X W gen gen_weight_one c) _)
  have hv := smul_gen_zero b i
  refine ⟨hv ▸ hx, ?_⟩
  rw [hEq]
  exact congrArg (liDegreeZeroClass W 1) (Subtype.ext hv)

/-! ### The highest relation vanishes -/

theorem smul_gen_gen (a b : Fin 8) :
    W.smul (gen a) (-1) (gen b) = simpleProjection (-3 / 2) level_add_three_ne_zero
      (J (-3 / 2) a (-1) (J (-3 / 2) b (-1) (vacuumA (-3 / 2)))) := by
  rw [gen_eq_proj b, smul_gen_proj]

/-- The state representing `2 · relationPoly 2` is `-3 e₁₂(-2)𝟙`, because `singVec` dies. -/
theorem two_combo_eq :
    (2 : ℂ) • W.smul (gen 6) (-1) (gen 2) + (-2 : ℂ) • W.smul (gen 7) (-1) (gen 2)
      + (6 : ℂ) • W.smul (gen 1) (-1) (gen 0) = (-3 : ℂ) • W.smul (gen 2) (-2) W.vacuum := by
  have e : (2 : ℂ) • J (-3 / 2) 6 (-1) (J (-3 / 2) 2 (-1) (vacuumA (-3 / 2))) +
      (-2 : ℂ) • J (-3 / 2) 7 (-1) (J (-3 / 2) 2 (-1) (vacuumA (-3 / 2))) +
      (6 : ℂ) • J (-3 / 2) 1 (-1) (J (-3 / 2) 0 (-1) (vacuumA (-3 / 2))) =
      singVec + (-3 : ℂ) • J (-3 / 2) 2 (-2) (vacuumA (-3 / 2)) := by
    unfold singVec; module
  have e' := congrArg (simpleProjection (-3 / 2) level_add_three_ne_zero) e
  simp only [map_add, map_smul, simpleProjection_singVec, zero_add] at e'
  rw [smul_gen_gen, smul_gen_gen, smul_gen_gen, vacuum_eq_proj, smul_gen_proj]
  exact e'

theorem two_combo_mem_O₂ :
    (2 : ℂ) • W.smul (gen 6) (-1) (gen 2) + (-2 : ℂ) • W.smul (gen 7) (-1) (gen 2)
      + (6 : ℂ) • W.smul (gen 1) (-1) (gen 0) ∈ O₂ W := by
  rw [two_combo_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨gen 2, W.vacuum, rfl⟩)

theorem two_combo_poly :
    (2 : ℂ) • (X 6 * X 2) + (-2 : ℂ) • (X 7 * X 2) + (6 : ℂ) • (X 1 * X 0) =
      (2 : ℂ) • relationPoly 2 := by
  rw [relationPoly_two]
  simp only [MvPolynomial.smul_eq_C_mul, map_neg, map_ofNat]
  ring

/-- Generic form: a weight-two state in `C₂` representing `2 · relationPoly 2`. -/
theorem clsG_relationPoly_two_of {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W' : VertexOperatorAlgebra V} {g : Fin 8 → V} {hg : ∀ i, g i ∈ W'.grading (1 : ℤ)}
    (hO : (2 : ℂ) • W'.smul (g 6) (-1) (g 2) + (-2 : ℂ) • W'.smul (g 7) (-1) (g 2)
      + (6 : ℂ) • W'.smul (g 1) (-1) (g 0) ∈ O₂ W') :
    clsG W' g hg (relationPoly 2) = 0 := by
  have r := fun a b => rep_mul (rep_X W' g hg a) (rep_X W' g hg b)
  have hP := rep_add (rep_add (rep_smul (r 6 2) 2) (rep_smul (r 7 2) (-2))) (rep_smul (r 1 0) 6)
  have h2 := clsG_eq_zero_of_rep hP hO
  rw [two_combo_poly, map_smul] at h2
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **The highest-weight relation lies in the kernel.** -/
theorem clsG_relationPoly_two : clsG W gen gen_weight_one (relationPoly 2) = 0 :=
  clsG_relationPoly_two_of two_combo_mem_O₂

/-! ### All relations, the ideal, and the presentation -/

/-- **Every relation lies in the kernel of the current-coordinate map of `L_{-3/2}(sl₃)`.** -/
theorem clsG_relationPoly (a : Fin 8) : clsG W gen gen_weight_one (relationPoly a) = 0 :=
  clsG_relationPoly_of_two hT_A2 clsG_relationPoly_two a

/-- **`I₂ⁿˢ` is contained in the `C₂` kernel of `L_{-3/2}(sl₃)`.** -/
theorem I2ns_le_ker : I2ns ≤ RingHom.ker
    (MvPolynomial.aeval fun i =>
      liDegreeZeroClass W 1 ⟨gen i, gen_weight_one i⟩).toRingHom :=
  I2ns_le_ker_of_two hT_A2 clsG_relationPoly_two

/-- **The explicit A₂ presentation**: currents `generator a (-1) 𝟙` of `L_{-3/2}(sl₃)`, ideal
`I₂ⁿˢ` generated by the eight quadrics `relationPoly` (the adjoint copy `V(θ) ⊂ Sym² sl₃`). -/
def explicitPresentation : CurrentC2Presentation .A2 W where
  gen := gen
  gen_weight_one := gen_weight_one
  ideal := I2ns
  relations := I2ns_le_ker

theorem explicitPresentation_ideal : explicitPresentation.ideal = I2ns := rfl

/-- **`CurrentJetSurjectivity` for the explicit presentation** (the current-word spanning proof
is independent of the ideal). -/
theorem explicitCurrentJetSurjectivity : CurrentJetSurjectivity .A2 W explicitPresentation :=
  currentJetSurjectivity_of_genWordSpan explicitPresentation genWordsSpan

/-- **A₂ Deligne case with the explicit ideal `I₂ⁿˢ`**, conditional on the two remaining
packages.  By the capstone it also yields `ker = I₂ⁿˢ`. -/
theorem explicit_classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .A2 W explicitPresentation Carrier)
    (hchar : OrdinaryCarrierCharacter W Carrier) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  caseClassicallyFree_of_explicit_inputs .A2 W explicitPresentation Carrier
    explicitCurrentJetSurjectivity hgeom hchar

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.clsG_adPolyT
#print axioms VOA.DeligneAudit.A2.clsG_relationPoly_two
#print axioms VOA.DeligneAudit.A2.I2ns_le_ker
#print axioms VOA.DeligneAudit.A2.explicitPresentation
#print axioms VOA.DeligneAudit.A2.explicitCurrentJetSurjectivity
#print axioms VOA.DeligneAudit.A2.explicit_classicallyFree_of_two_inputs
end AxiomAudit
