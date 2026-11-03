/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SingularQuad
import VOA.Filtered.LiGradedModeLeibniz
import VOA.Filtered.LiC2Bridge
import VOA.Filtered.LiGeneratorWords

/-!
# Current presentations of `L_k(𝔤)` in Li degree zero (general `𝔤`)

The general-`𝔤`, `Fin n`-indexed version of REL's A₂ argument (`DeligneAudit/A2RelationsPresentation`):

* Generic (any VOA, any `n` weight-one states): `clsG`, `Rep` and its closure lemmas, and `clsG_adPolyT`: the
  Li zero mode of a current matches the coadjoint derivation `adPolyT T b` once it does on generators.
* For Lie data `D` indexed by `Fin n` and `L_k(𝔤) = simpleVOA D k hk`, with currents `genS i = [J^i_{-1}|0⟩]`:
  `smul_genS_zero` (`g_b(0) g_i = Σ f(b,i,c) g_c`), hence **`clsG_adPoly_eq_zero`**: the kernel of the
  current-coordinate map is stable under `adPolyT (structureConstant D) b`; and **`clsG_quad_eq_zero`**: a
  quadratic polynomial whose state `Σ cᵢ J^{aᵢ}_{-1}J^{bᵢ}_{-1}|0⟩` lies in the maximal ideal is in the kernel.
-/

namespace VOA.AffineGeneral

open MvPolynomial VOA.AffineGeneral.LieData

noncomputable section

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W' : VertexOperatorAlgebra V)
  (g : Fin n → V) (hg : ∀ i, g i ∈ W'.grading (1 : ℤ))

/-- The current-coordinate map into Li degree zero. -/
abbrev clsG : MvPolynomial (Fin n) ℂ →ₐ[ℂ] liAssociatedGraded W' :=
  aeval fun i => liDegreeZeroClass W' 1 ⟨g i, hg i⟩

/-- `x` is a weight-`N` representative of the value of `p`. -/
def Rep (p : MvPolynomial (Fin n) ℂ) (N : ℕ) (x : V) : Prop :=
  ∃ hx : x ∈ W'.grading (N : ℤ), clsG W' g hg p = liDegreeZeroClass W' N ⟨x, hx⟩

theorem rep_X (i : Fin n) : Rep W' g hg (X i) 1 (g i) := ⟨hg i, by simp⟩

variable {W' g hg}

theorem rep_add {p q : MvPolynomial (Fin n) ℂ} {N : ℕ} {x y : V} (hp : Rep W' g hg p N x)
    (hq : Rep W' g hg q N y) : Rep W' g hg (p + q) N (x + y) := by
  obtain ⟨hx, hpx⟩ := hp
  obtain ⟨hy, hqy⟩ := hq
  refine ⟨Submodule.add_mem _ hx hy, ?_⟩
  rw [map_add, hpx, hqy]
  simp only [liDegreeZeroClass_eq_liHomogeneousClass]
  rw [← liHomogeneousClass_add]
  rfl

theorem rep_smul {p : MvPolynomial (Fin n) ℂ} {N : ℕ} {x : V} (hp : Rep W' g hg p N x) (c : ℂ) :
    Rep W' g hg (c • p) N (c • x) := by
  obtain ⟨hx, hpx⟩ := hp
  refine ⟨Submodule.smul_mem _ c hx, ?_⟩
  rw [map_smul, hpx]
  simp only [liDegreeZeroClass_eq_liHomogeneousClass]
  rw [← liHomogeneousClass_smul]
  rfl

theorem rep_mul {p q : MvPolynomial (Fin n) ℂ} {N M : ℕ} {x y : V} (hp : Rep W' g hg p N x)
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

theorem rep_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℂ) {N : ℕ}
    (x : ι → V) (h : ∀ i, Rep W' g hg (p i) N (x i)) :
    Rep W' g hg (∑ i ∈ s, p i) N (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rep_zero N
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact rep_add (h a) ih

theorem clsG_eq_zero_of_rep {p : MvPolynomial (Fin n) ℂ} {N : ℕ} {x : V}
    (hp : Rep W' g hg p N x) (hx : x ∈ O₂ W') : clsG W' g hg p = 0 := by
  obtain ⟨hxN, hpx⟩ := hp
  rw [hpx]
  exact liDegreeZeroClass_eq_zero_of_mem_O₂ W' N ⟨x, hxN⟩ hx

/-! ### Zero modes of the currents act by the coadjoint derivation -/

/-- The derivation of the polynomial ring on the generators induced by a structure table `T`:
`X i ↦ ∑ c, T b i c • X c`. -/
def adPolyT (T : Fin n → Fin n → Fin n → ℂ) (b : Fin n) :
    Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ) :=
  mkDerivation ℂ fun i => ∑ c, T b i c • X c

variable (W' g hg) in
/-- The Li zero mode of a current. -/
abbrev zeroModeG (b : Fin n) : liAssociatedGraded W' →ₗ[ℂ] liAssociatedGraded W' :=
  liAssociatedGradedMode W' 0 (liDegreeZeroClass W' 1 ⟨g b, hg b⟩)

theorem zeroModeG_one (b : Fin n) : zeroModeG W' g hg b 1 = 0 := by
  have h := liAssociatedGradedMode_leibniz W' 0 (liDegreeZeroClass W' 1 ⟨g b, hg b⟩) 1 1
  simp only [mul_one, one_mul] at h
  change zeroModeG W' g hg b 1 = zeroModeG W' g hg b 1 + zeroModeG W' g hg b 1 at h
  linear_combination -h

/-- **The Li zero mode of a current matches the coadjoint derivation**, provided it does on the
generators. -/
theorem clsG_adPolyT (T : Fin n → Fin n → Fin n → ℂ)
    (hT : ∀ b i, ∃ h : W'.smul (g b) 0 (g i) ∈ W'.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W' 1 ⟨W'.smul (g b) 0 (g i), h⟩ = clsG W' g hg (∑ c, T b i c • X c))
    (b : Fin n) (p : MvPolynomial (Fin n) ℂ) :
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
theorem clsG_adPolyT_eq_zero (T : Fin n → Fin n → Fin n → ℂ)
    (hT : ∀ b i, ∃ h : W'.smul (g b) 0 (g i) ∈ W'.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W' 1 ⟨W'.smul (g b) 0 (g i), h⟩ = clsG W' g hg (∑ c, T b i c • X c))
    (b : Fin n) {p : MvPolynomial (Fin n) ℂ} (hp : clsG W' g hg p = 0) :
    clsG W' g hg (adPolyT T b p) = 0 := by
  rw [clsG_adPolyT T hT, hp, map_zero]

end Generic

/-! ## The simple affine VOA -/

section Affine

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {n : ℕ} (D : LieData κ (Fin n)) (k : ℂ) (hk : k + D.h ≠ 0)

/-- The currents of `L_k(𝔤)`. -/
def genS (i : Fin n) : Vacuum D k ⧸ maxIdeal D k hk :=
  simpleProjection D k hk (J D k i (-1) (vacuumA D k))

theorem genS_weight_one (i : Fin n) : genS D k hk i ∈ (simpleVOA D k hk).grading (1 : ℤ) :=
  simpleCurrentState_mem D k hk i

theorem smul_genS_proj (a : Fin n) (m : ℤ) (x : Vacuum D k) :
    (simpleVOA D k hk).smul (genS D k hk a) m (simpleProjection D k hk x) =
      simpleProjection D k hk (J D k a m x) := by
  change (simpleVOA D k hk).smul (simpleProjection D k hk (currentState D k (D.generator a))) m
    (simpleProjection D k hk x) = _
  exact (SimpleQuot.maxQuotientVOA_mkQ_smul (affineVOA D k hk) _ m x).trans
    (congrArg _ (smul_currentState D k hk a m x))

theorem genS_eq (i : Fin n) : genS D k hk i = simpleProjection D k hk (J D k i (-1) (vacuumA D k)) := rfl

theorem smul_genS_zero (b i : Fin n) :
    (simpleVOA D k hk).smul (genS D k hk b) 0 (genS D k hk i) =
      ∑ c, structureConstant D b i c • genS D k hk c := by
  rw [genS_eq D k hk i, smul_genS_proj, J_zero_st1, map_sum]
  simp only [map_smul]
  rfl

theorem hT_aff (b i : Fin n) :
    ∃ h : (simpleVOA D k hk).smul (genS D k hk b) 0 (genS D k hk i) ∈
        (simpleVOA D k hk).grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass (simpleVOA D k hk) 1 ⟨_, h⟩ =
        clsG (simpleVOA D k hk) (genS D k hk) (genS_weight_one D k hk)
          (∑ c, structureConstant D b i c • X c) := by
  obtain ⟨hx, hEq⟩ := rep_sum (W' := simpleVOA D k hk) (g := genS D k hk) (hg := genS_weight_one D k hk)
    Finset.univ (fun c => structureConstant D b i c • X c) (N := 1)
    (fun c => structureConstant D b i c • genS D k hk c)
    (fun c => rep_smul (rep_X (simpleVOA D k hk) (genS D k hk) (genS_weight_one D k hk) c) _)
  have hv := smul_genS_zero D k hk b i
  refine ⟨hv ▸ hx, ?_⟩
  rw [hEq]
  exact congrArg (liDegreeZeroClass (simpleVOA D k hk) 1) (Subtype.ext hv)

/-- **The kernel of the current-coordinate map of `L_k(𝔤)` is `ad`-stable.** -/
theorem clsG_adPoly_eq_zero (b : Fin n) {p : MvPolynomial (Fin n) ℂ}
    (hp : clsG (simpleVOA D k hk) (genS D k hk) (genS_weight_one D k hk) p = 0) :
    clsG (simpleVOA D k hk) (genS D k hk) (genS_weight_one D k hk)
      (adPolyT (structureConstant D) b p) = 0 :=
  clsG_adPolyT_eq_zero (structureConstant D) (hT_aff D k hk) b hp

/-- The polynomial of a quadratic state. -/
def quadPoly (terms : List (ℂ × Fin n × Fin n)) : MvPolynomial (Fin n) ℂ :=
  (terms.map fun t => t.1 • (X t.2.1 * X t.2.2)).sum

theorem rep_quad (terms : List (ℂ × Fin n × Fin n)) :
    Rep (simpleVOA D k hk) (genS D k hk) (genS_weight_one D k hk) (quadPoly terms) (1 + 1)
      (simpleProjection D k hk (quadState D k terms)) := by
  induction terms with
  | nil =>
    simp only [quadPoly, quadState, List.map_nil, List.sum_nil, map_zero]
    exact rep_zero _
  | cons t terms ih =>
    simp only [quadPoly, quadState, List.map_cons, List.sum_cons, map_add, map_smul] at ih ⊢
    refine rep_add (rep_smul ?_ _) ih
    have r := rep_mul (rep_X (simpleVOA D k hk) (genS D k hk) (genS_weight_one D k hk) t.2.1)
      (rep_X (simpleVOA D k hk) (genS D k hk) (genS_weight_one D k hk) t.2.2)
    rwa [genS_eq D k hk t.2.2, smul_genS_proj] at r

/-- **A quadratic state in the maximal ideal gives a relation in Li degree zero.** -/
theorem clsG_quad_eq_zero (terms : List (ℂ × Fin n × Fin n)) (h : quadState D k terms ∈ maxIdeal D k hk) :
    clsG (simpleVOA D k hk) (genS D k hk) (genS_weight_one D k hk) (quadPoly terms) = 0 := by
  have h0 : simpleProjection D k hk (quadState D k terms) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr h
  have r := rep_quad D k hk terms
  rw [h0] at r
  exact clsG_eq_zero_of_rep r (Submodule.zero_mem _)

end Affine

end

end VOA.AffineGeneral
