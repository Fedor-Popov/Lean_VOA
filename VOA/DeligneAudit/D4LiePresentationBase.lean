/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4LieSingular
import VOA.DeligneAudit.A2RelationsPresentation

/-!
# Toward the explicit `D₄` presentation: polynomial values and the coadjoint derivation

* §1 (any VOA, any finite family of weight-one states): the `Rep`/`clsG`/`adPolyT` toolkit of
  `A2RelationsPresentation`, generalized from `Fin 8` to any finite index type: the zero mode of a
  current acts on the current-coordinate image by the coadjoint derivation, so the kernel is
  stable under it (`clsG_adPolyT_eq_zero'`).
* §2: the derivation on a quadric given by a coefficient list (`adPolyT_entryMatrix`).
* §3 (`L_{-2}(𝔰𝔬₈)`, cert basis): the current brackets in the simple quotient (`hT4`) and the
  three highest relations `P0, P1, P2` in the kernel (`clsG_rel_hw`), from the singular vectors.
-/

namespace VOA.DeligneAudit.D4Lie

open VOA VOA.AffineGeneral VOA.AffineGeneral.LieData VOA.DeligneHigherRankConditionalCapstone
  MvPolynomial VOA.QuadraticJetCoefficientPairing

noncomputable section

/-! ## §1  Representatives of polynomial values (any VOA) -/

section Generic

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W' : VertexOperatorAlgebra V)
  (g : σ → V) (hg : ∀ i, g i ∈ W'.grading (1 : ℤ))

/-- The current-coordinate map into Li degree zero. -/
abbrev clsG' : MvPolynomial σ ℂ →ₐ[ℂ] liAssociatedGraded W' :=
  aeval fun i => liDegreeZeroClass W' 1 ⟨g i, hg i⟩

/-- `x` is a weight-`N` representative of the value of `p`. -/
def Rep' (p : MvPolynomial σ ℂ) (N : ℕ) (x : V) : Prop :=
  ∃ hx : x ∈ W'.grading (N : ℤ), clsG' W' g hg p = liDegreeZeroClass W' N ⟨x, hx⟩

theorem rep_X' (i : σ) : Rep' W' g hg (X i) 1 (g i) := ⟨hg i, by simp⟩

variable {W' g hg}

theorem rep_add' {p q : MvPolynomial σ ℂ} {N : ℕ} {x y : V} (hp : Rep' W' g hg p N x)
    (hq : Rep' W' g hg q N y) : Rep' W' g hg (p + q) N (x + y) := by
  obtain ⟨hx, hpx⟩ := hp
  obtain ⟨hy, hqy⟩ := hq
  refine ⟨Submodule.add_mem _ hx hy, ?_⟩
  rw [map_add, hpx, hqy]
  simp only [liDegreeZeroClass_eq_liHomogeneousClass]
  rw [← liHomogeneousClass_add]
  rfl

theorem rep_smul' {p : MvPolynomial σ ℂ} {N : ℕ} {x : V} (hp : Rep' W' g hg p N x) (c : ℂ) :
    Rep' W' g hg (c • p) N (c • x) := by
  obtain ⟨hx, hpx⟩ := hp
  refine ⟨Submodule.smul_mem _ c hx, ?_⟩
  rw [map_smul, hpx]
  simp only [liDegreeZeroClass_eq_liHomogeneousClass]
  rw [← liHomogeneousClass_smul]
  rfl

theorem rep_mul' {p q : MvPolynomial σ ℂ} {N M : ℕ} {x y : V} (hp : Rep' W' g hg p N x)
    (hq : Rep' W' g hg q M y) : Rep' W' g hg (p * q) (N + M) (W'.smul x (-1) y) := by
  obtain ⟨hx, hpx⟩ := hp
  obtain ⟨hy, hqy⟩ := hq
  have hgr : W'.smul x (-1) y ∈ W'.grading ((N + M : ℕ) : ℤ) := by
    simpa using W'.smul_mem_grading hx hy (-1)
  refine ⟨hgr, ?_⟩
  rw [map_mul, hpx, hqy, liDegreeZeroClass_eq_liHomogeneousClass,
    liDegreeZeroClass_eq_liHomogeneousClass, liHomogeneousClass_mul]
  rfl

theorem rep_zero' (N : ℕ) : Rep' W' g hg 0 N 0 :=
  ⟨Submodule.zero_mem _, by
    rw [map_zero]
    exact (liDegreeZeroClass_eq_zero_of_mem_O₂ W' N ⟨0, Submodule.zero_mem _⟩
      (Submodule.zero_mem _)).symm⟩

theorem rep_sum' {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℂ) {N : ℕ}
    (x : ι → V) (h : ∀ i, Rep' W' g hg (p i) N (x i)) :
    Rep' W' g hg (∑ i ∈ s, p i) N (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rep_zero' N
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact rep_add' (h a) ih

theorem clsG_eq_zero_of_rep' {p : MvPolynomial σ ℂ} {N : ℕ} {x : V}
    (hp : Rep' W' g hg p N x) (hx : x ∈ O₂ W') : clsG' W' g hg p = 0 := by
  obtain ⟨hxN, hpx⟩ := hp
  rw [hpx]
  exact liDegreeZeroClass_eq_zero_of_mem_O₂ W' N ⟨x, hxN⟩ hx

/-- The derivation `X i ↦ ∑ c, T b i c • X c`. -/
def adPolyT' (T : σ → σ → σ → ℂ) (b : σ) :
    Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  mkDerivation ℂ fun i => ∑ c, T b i c • X c

variable (W' g hg) in
/-- The Li zero mode of a current. -/
abbrev zeroModeG' (b : σ) : liAssociatedGraded W' →ₗ[ℂ] liAssociatedGraded W' :=
  liAssociatedGradedMode W' 0 (liDegreeZeroClass W' 1 ⟨g b, hg b⟩)

theorem zeroModeG_one' (b : σ) : zeroModeG' W' g hg b 1 = 0 := by
  have h := liAssociatedGradedMode_leibniz W' 0 (liDegreeZeroClass W' 1 ⟨g b, hg b⟩) 1 1
  simp only [mul_one, one_mul] at h
  change zeroModeG' W' g hg b 1 = zeroModeG' W' g hg b 1 + zeroModeG' W' g hg b 1 at h
  linear_combination -h

/-- The Li zero mode of a current matches the coadjoint derivation. -/
theorem clsG_adPolyT' (T : σ → σ → σ → ℂ)
    (hT : ∀ b i, ∃ h : W'.smul (g b) 0 (g i) ∈ W'.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W' 1 ⟨W'.smul (g b) 0 (g i), h⟩ = clsG' W' g hg (∑ c, T b i c • X c))
    (b : σ) (p : MvPolynomial σ ℂ) :
    clsG' W' g hg (adPolyT' T b p) = zeroModeG' W' g hg b (clsG' W' g hg p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one, map_smul, zeroModeG_one', smul_zero]
  | add p q hp hq => rw [map_add, map_add, hp, map_add, map_add, hq]
  | mul_X p i hp =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, map_mul]
      have hX : clsG' W' g hg (adPolyT' T b (X i)) =
          zeroModeG' W' g hg b (clsG' W' g hg (X i)) := by
        obtain ⟨h, hh⟩ := hT b i
        rw [adPolyT', mkDerivation_X, ← hh, zeroModeG', clsG', aeval_X,
          liDegreeZeroClass_mode_zero W' 1 1 (by omega)]
        rfl
      rw [hX, zeroModeG', liAssociatedGradedMode_leibniz]
      ring

/-- **The kernel of the current-coordinate map is stable under the coadjoint derivations.** -/
theorem clsG_adPolyT_eq_zero' (T : σ → σ → σ → ℂ)
    (hT : ∀ b i, ∃ h : W'.smul (g b) 0 (g i) ∈ W'.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W' 1 ⟨W'.smul (g b) 0 (g i), h⟩ = clsG' W' g hg (∑ c, T b i c • X c))
    (b : σ) {p : MvPolynomial σ ℂ} (hp : clsG' W' g hg p = 0) :
    clsG' W' g hg (adPolyT' T b p) = 0 := by
  rw [clsG_adPolyT' T hT, hp, map_zero]

end Generic

/-! ## §2  The derivation on a quadric given by a coefficient list -/

section Quadric

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- `adPolyT'` on a variable. -/
theorem adPolyT'_X (T : σ → σ → σ → ℂ) (b i : σ) : adPolyT' T b (X i) = ∑ c, T b i c • X c := by
  rw [adPolyT', mkDerivation_X]

theorem adPolyT'_entryMatrix (T : σ → σ → σ → ℂ) (b : σ) (L : List (σ × σ × ℂ)) :
    adPolyT' T b (quadraticRelation (A2.entryMatrix L)) =
      (L.map fun t => t.2.2 • (X t.1 * adPolyT' T b (X t.2.1) +
        X t.2.1 * adPolyT' T b (X t.1))).sum := by
  rw [A2.quadraticRelation_entryMatrix]
  induction L with
  | nil => simp
  | cons t L ih =>
      rw [List.map_cons, List.sum_cons, map_add, ih, List.map_cons, List.sum_cons,
        Derivation.map_smul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]

end Quadric

/-! ## §3  `L_{-2}(𝔰𝔬₈)` in the cert basis -/

/-- `L_{-2}(𝔰𝔬₈)`. -/
abbrev W4 := simpleVOA d4CertData (-2) hk4

/-- The current generators. -/
abbrev gen4 (a : Fin 28) : Vacuum d4CertData (-2) ⧸ maxIdeal d4CertData (-2) hk4 :=
  simpleCurrentState d4CertData (-2) hk4 (d4CertData.generator a)

theorem gen4_weight_one (a : Fin 28) : gen4 a ∈ W4.grading (1 : ℤ) :=
  simpleCurrentState_mem d4CertData (-2) hk4 a

/-- The current-coordinate map of `L_{-2}(𝔰𝔬₈)`. -/
abbrev cls4 : MvPolynomial (Fin 28) ℂ →ₐ[ℂ] liAssociatedGraded W4 := clsG' W4 gen4 gen4_weight_one

theorem gen4_eq_proj (a : Fin 28) :
    gen4 a = simpleProjection d4CertData (-2) hk4
      (J d4CertData (-2) a (-1) (vacuumA d4CertData (-2))) := rfl

theorem smul_gen4_proj (a : Fin 28) (m : ℤ) (x : Vacuum d4CertData (-2)) :
    W4.smul (gen4 a) m (simpleProjection d4CertData (-2) hk4 x) =
      simpleProjection d4CertData (-2) hk4 (J d4CertData (-2) a m x) := by
  have h := SimpleQuot.maxQuotientVOA_mkQ_smul (affineVOA d4CertData (-2) hk4)
    (J d4CertData (-2) a (-1) (vacuumA d4CertData (-2))) m x
  rw [smulJ] at h
  exact h

/-- `g_b(0) g_i = [g_b, g_i]` in `L_{-2}(𝔰𝔬₈)`. -/
theorem smul_gen4_zero (b i : Fin 28) :
    W4.smul (gen4 b) 0 (gen4 i) = ∑ c, d4CertData.structureConstant b i c • gen4 c := by
  rw [gen4_eq_proj i, smul_gen4_proj, J_J_comm, J_vac_nonneg _ _ b le_rfl, map_zero, zero_add,
    if_neg (by norm_num), add_zero, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, zero_add, gen4_eq_proj c]

set_option maxHeartbeats 1000000 in -- `obtain` on the `Rep'` existential is slow here
theorem hT4 (b i : Fin 28) :
    ∃ h : W4.smul (gen4 b) 0 (gen4 i) ∈ W4.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W4 1 ⟨W4.smul (gen4 b) 0 (gen4 i), h⟩ =
        cls4 (∑ c, d4CertData.structureConstant b i c • X c) := by
  obtain ⟨hx, hEq⟩ := rep_sum' (W' := W4) (g := gen4) (hg := gen4_weight_one) Finset.univ
    (fun c => d4CertData.structureConstant b i c • X c) (N := 1)
    (fun c => d4CertData.structureConstant b i c • gen4 c)
    (fun c => rep_smul' (rep_X' W4 gen4 gen4_weight_one c) _)
  have hv := smul_gen4_zero b i
  refine ⟨by rw [hv]; exact hx, ?_⟩
  rw [hEq]
  exact congrArg (liDegreeZeroClass W4 1) (Subtype.ext hv)

/-- The coadjoint derivation of `𝔰𝔬₈` on the cert coordinates. -/
abbrev ad4 (b : Fin 28) := adPolyT' d4CertData.structureConstant b

theorem cls4_ad (b : Fin 28) {p : MvPolynomial (Fin 28) ℂ} (hp : cls4 p = 0) :
    cls4 (ad4 b p) = 0 :=
  clsG_adPolyT_eq_zero' _ hT4 b hp

/-- The sparse form of the derivation on a variable. -/
theorem ad4_X (b i : Fin 28) :
    ad4 b (X i) = ((sL b i).map fun t => (t.2 : ℂ) • X t.1).sum := by
  rw [ad4, adPolyT'_X]
  simp only [structureConstant_eq, sZ]
  induction sL b i with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, add_smul, Finset.sum_add_distrib, ih,
        apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]

/-- The relation polynomials of `DeligneCarrierD4`. -/
def Q (r : Fin 105) : MvPolynomial (Fin 28) ℂ := quadraticRelation (DeligneCarrier.D4.rel r)

theorem ad4_Q (b : Fin 28) (r : Fin 105) :
    ad4 b (Q r) = ((DeligneCarrier.D4.relTable r).map fun t => t.2.2 • (X t.1 * ad4 b (X t.2.1) +
      X t.2.1 * ad4 b (X t.1))).sum :=
  adPolyT'_entryMatrix _ b _

/-! ### The highest relations -/

theorem smul_gen4_gen4 (a b : Fin 28) :
    W4.smul (gen4 a) (-1) (gen4 b) = simpleProjection d4CertData (-2) hk4 (w2 a b) := by
  rw [gen4_eq_proj b, smul_gen4_proj]
  rfl

/-- The state `∑ cz • g_a(-1) g_b` is the image of a singular vector, hence zero. -/
theorem hw_state_zero (r : Fin 3) :
    ∑ i, (cz r i : ℂ) • W4.smul (gen4 (ta r i)) (-1) (gen4 (tb r i)) = 0 := by
  simp only [smul_gen4_gen4, ← map_smul, ← map_sum]
  exact simpleProjection_sv r

theorem cls4_hw_poly (r : Fin 3) : cls4 (∑ i, (cz r i : ℂ) • (X (ta r i) * X (tb r i))) = 0 := by
  have hP := rep_sum' (W' := W4) (g := gen4) (hg := gen4_weight_one) Finset.univ
    (fun i => (cz r i : ℂ) • (X (ta r i) * X (tb r i))) (N := 2)
    (fun i => (cz r i : ℂ) • W4.smul (gen4 (ta r i)) (-1) (gen4 (tb r i)))
    (fun i => rep_smul' (rep_mul' (rep_X' W4 gen4 gen4_weight_one _)
      (rep_X' W4 gen4 gen4_weight_one _)) _)
  rw [hw_state_zero] at hP
  exact clsG_eq_zero_of_rep' hP (Submodule.zero_mem _)

theorem Q_hw0 : Q 0 = ∑ i, (cz 0 i : ℂ) • (X (ta 0 i) * X (tb 0 i)) := by
  rw [Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp [DeligneCarrier.D4.relTable, Fin.sum_univ_three, ta, tb, cz]
  abel

theorem Q_hw1 : Q 1 = ∑ i, (cz 1 i : ℂ) • (X (ta 1 i) * X (tb 1 i)) := by
  rw [Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp [DeligneCarrier.D4.relTable, Fin.sum_univ_three, ta, tb, cz]
  abel

theorem Q_hw2 : Q 2 = ∑ i, (cz 2 i : ℂ) • (X (ta 2 i) * X (tb 2 i)) := by
  rw [Q, DeligneCarrier.D4.rel, A2.quadraticRelation_entryMatrix]
  simp [DeligneCarrier.D4.relTable, Fin.sum_univ_three, ta, tb, cz]
  abel

/-- **The three highest relations lie in the kernel.** -/
theorem cls4_of_eq {p q : MvPolynomial (Fin 28) ℂ} (h : p = q) (hq : cls4 q = 0) : cls4 p = 0 :=
  (congrArg cls4 h).trans hq

theorem cls4_Q0 : cls4 (Q 0) = 0 := cls4_of_eq Q_hw0 (cls4_hw_poly 0)
theorem cls4_Q1 : cls4 (Q 1) = 0 := cls4_of_eq Q_hw1 (cls4_hw_poly 1)
theorem cls4_Q2 : cls4 (Q 2) = 0 := cls4_of_eq Q_hw2 (cls4_hw_poly 2)

theorem eq_zero_of_smul {M : Type*} [AddCommGroup M] [Module ℂ M] {c : ℂ} (hc : c ≠ 0) {x : M}
    (h : c • x = 0) : x = 0 := by
  rw [← one_smul ℂ x, ← inv_mul_cancel₀ hc, mul_smul, h, smul_zero]

/-- **One propagation step**: `ad_b P_r = c P_s` with `c ≠ 0` moves `P_r ∈ ker` to `P_s ∈ ker`. -/
theorem cls4_step {b : Fin 28} {r s : Fin 105} {c : ℂ} (hc : c ≠ 0) (h : ad4 b (Q r) = c • Q s)
    (hr : cls4 (Q r) = 0) : cls4 (Q s) = 0 := by
  have h1 : cls4 (c • Q s) = 0 := (congrArg cls4 h).symm.trans (cls4_ad b hr)
  rw [map_smul] at h1
  exact eq_zero_of_smul hc h1

/-- The step with a cleared denominator: `q • ad_b P_r = p • P_s`, `p ≠ 0`. -/
theorem cls4_stepq {b : Fin 28} {r s : Fin 105} {p q : ℂ} (hp : p ≠ 0)
    (h : q • ad4 b (Q r) = p • Q s) (hr : cls4 (Q r) = 0) : cls4 (Q s) = 0 := by
  have h0 : cls4 (q • ad4 b (Q r)) = 0 :=
    (map_smul cls4 q _).trans ((congrArg (q • ·) (cls4_ad b hr)).trans (smul_zero q))
  have h1 : cls4 (p • Q s) = 0 := (congrArg cls4 h).symm.trans h0
  exact eq_zero_of_smul hp ((map_smul cls4 p (Q s)).symm.trans h1)

end

end VOA.DeligneAudit.D4Lie

section AxiomAudit
open VOA.DeligneAudit.D4Lie
#print axioms clsG_adPolyT_eq_zero'
#print axioms cls4_ad
#print axioms cls4_Q0
#print axioms cls4_step
end AxiomAudit
