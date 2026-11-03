/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieSingular
import VOA.DeligneAudit.F4Sector
import VOA.DeligneAudit.F4LieStepsA
import VOA.DeligneAudit.F4LieStepsB
import VOA.DeligneAudit.F4LieStepsC
import VOA.DeligneAudit.F4LieStepsD
import VOA.DeligneAudit.E6SectorSparse
import VOA.AffineGeneral.LiPresentation
import VOA.AffineGeneral.DeligneInstance
import VOA.DeligneAudit.A2CarrierUpperBound
import VOA.DeligneAudit.A2CurrentJetSurjectivity

/-!
# The explicit `F₄` presentation: `I₂ⁿˢ` lies in the `C₂` kernel of `L_{-5/2}(𝔣₄)`

`f4W = simpleVOA f4CertData (-5/2)` (currents in the `f4T` basis), `clF4` its
current-coordinate map into Li degree zero. The E₆ method (`E6Presentation`):

1. `clF4_rel_zero`: the highest relation `P₀ = -X₈² + 4X₁₉X₃₀ + 4X₂₁X₃₄ + 4X₂₅X₄₂` is in the
   kernel: its state is the weight-two singular vector `f4sv` (`f4sv_mem_maxIdeal`).
2. `clF4_step`: the kernel is stable under the coadjoint derivations (`clsG_adPoly_eq_zero`); each
   BFS step `P_k = ad(g) P_j` is a kernel-checked sparse identity
   (`F4LieSteps`, checked in `F4LieStepsA..D`).
3. `clF4_rel`: all 324 relations, by strong induction along `f4Steps`.
4. **`I2ns_le_ker`**, **`explicitPresentation`** (`ideal := F4data.I`),
   **`explicitCurrentJetSurjectivity`**, **`geometricCarrierEmbedding`** (via
   `geometricCarrierEmbedding_of_quadraticIdeal`).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.F4Lie

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse
  VOA.DeligneAudit.E6SectorSparse VOA.AffineGeneral VOA.AffineGeneral.SCLie
  VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.CarrierEmbedding
  VOA.DeligneAudit.DeligneSector.F4

noncomputable section

/-- The current-coordinate map of `L_{-5/2}(𝔣₄)` into Li degree zero. -/
abbrev clF4 := clsG f4W (genS f4CertData (-5/2) f4_level_ne)
  (genS_weight_one f4CertData (-5/2) f4_level_ne)

theorem scF_eq : scF f4T 52 = f4CertData.structureConstant := by
  funext x y c
  rw [f4CertData_sc]
  rfl

theorem adPoly_quadP (x : Fin 52) (l : List (ℕ × ℕ × ℤ)) (hl : qInRange 52 l = true) :
    adPolyT f4CertData.structureConstant x (quadP 52 l) = quadP 52 (adS f4T x l) := by
  rw [← scF_eq]
  exact adDer_quadP f4_bound x l hl

/-! ## The highest relation -/

theorem relQ_zero :
    relQ 0 = [(8, 8, -1), (19, 30, 4), (21, 34, 4), (25, 42, 4)] := by decide +kernel

theorem quadP_relQ_zero : quadP 52 (relQ 0) = quadPoly (termsZC f4svTerms) := by
  rw [relQ_zero]
  simp [quadP, quadPoly, termsZC, f4svTerms, Xn, MvPolynomial.smul_eq_C_mul, map_ofNat]

theorem clF4_rel_zero : clF4 (quadP 52 (relQ 0)) = 0 := by
  rw [quadP_relQ_zero]
  exact clsG_quad_eq_zero f4CertData (-5/2) f4_level_ne _ f4sv_mem_maxIdeal

/-! ## Propagation -/

theorem f4Steps_ok : f4Steps.all stepOK = true := by
  simp only [f4Steps, List.all_append, f4StepsA_ok, f4StepsB_ok, f4StepsC_ok, f4StepsD_ok,
    Bool.and_self]

theorem relQ_qInRange (j : ℕ) (hj : j < 324) : qInRange 52 (relQ j) = true := by
  have h := relZ_range (k := j) (by omega)
  simp only [relZ, hj, if_true] at h
  simp only [qInRange, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact h

theorem clF4_step (st : ℕ × ℕ × ℕ) (h : stepOK st = true) (hj : clF4 (quadP 52 (relQ st.2.1)) = 0) :
    clF4 (quadP 52 (relQ st.2.2)) = 0 := by
  obtain ⟨g, j, k⟩ := st
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hg, hjk⟩, hk⟩, hz⟩ := h
  have h0 := quadP_eq_zero_of_quadZero (n := 52) (by norm_num) _ hz
  rw [quadP_append', quadP_scaleQ] at h0
  have heq : quadP 52 (relQ k) = quadP 52 (adS f4T g (relQ j)) := by
    push_cast at h0
    linear_combination -h0
  have had := clsG_adPoly_eq_zero f4CertData (-5/2) f4_level_ne ⟨g, hg⟩ hj
  rw [adPoly_quadP ⟨g, hg⟩ _ (relQ_qInRange j (by omega))] at had
  rw [heq]
  exact had

theorem clF4_rel_lt : ∀ k, k < 324 → clF4 (quadP 52 (relQ k)) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact clF4_rel_zero
    · have hmem : k ∈ f4Steps.map (·.2.2) := by
        rw [f4Steps_targets, List.mem_range']; exact ⟨k - 1, by omega, by omega⟩
      obtain ⟨st, hst, hst2⟩ := List.mem_map.mp hmem
      have hok := List.all_eq_true.mp f4Steps_ok st hst
      have hlt : st.2.1 < st.2.2 := by
        simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1.1.2
      rw [← hst2]
      exact clF4_step st hok (ih _ (by omega) (by omega))

theorem clF4_rel (r : Fin 324) : clF4 (quadraticRelation (F4data.rel r)) = 0 := by
  have e1 : quadraticRelation (F4data.rel r) = quadP 52 (relQ r) := by
    rw [quadP_eq]; exact rel_poly r
  exact (congrArg clF4 e1).trans (clF4_rel_lt r r.2)

/-! ## The ideal and the presentation -/

/-- **`I₂ⁿˢ` is contained in the `C₂` kernel of `L_{-5/2}(𝔣₄)`.** -/
theorem I2ns_le_ker : F4data.I ≤ RingHom.ker
    (MvPolynomial.aeval fun i =>
      liDegreeZeroClass f4W 1 ⟨genS f4CertData (-5/2) f4_level_ne i,
        genS_weight_one f4CertData (-5/2) f4_level_ne i⟩).toRingHom := by
  intro p hp
  have hle : quadraticIdeal F4data.rel ≤ RingHom.ker clF4.toRingHom := by
    rw [quadraticIdeal, Ideal.span_le]
    rintro _ ⟨r, rfl⟩
    exact clF4_rel r
  exact hle hp

/-- **The explicit `F₄` presentation**: currents `J^a_{-1}|0⟩` of `L_{-5/2}(𝔣₄)`, ideal `I₂ⁿˢ`. -/
def explicitPresentation : CurrentC2Presentation .F4 f4W where
  gen := genS f4CertData (-5/2) f4_level_ne
  gen_weight_one := genS_weight_one f4CertData (-5/2) f4_level_ne
  ideal := F4data.I
  relations := I2ns_le_ker

theorem explicitPresentation_ideal : explicitPresentation.ideal = quadraticIdeal F4data.rel := rfl

/-- **The geometric carrier embedding** for the explicit `F₄` presentation. -/
def geometricCarrierEmbedding :
    GeometricCarrierEmbedding .F4 f4W explicitPresentation (Carrier F4data.rel) :=
  geometricCarrierEmbedding_of_quadraticIdeal explicitPresentation F4data.rel rfl

/-- **`CurrentJetSurjectivity` for the explicit `F₄` presentation.** -/
theorem explicitCurrentJetSurjectivity : CurrentJetSurjectivity .F4 f4W explicitPresentation :=
  DeligneAudit.currentJetSurjectivity_of_genWordSpan explicitPresentation
    (VOA.AffineGeneral.Deligne.genWordsSpan .F4 f4CertData (-5/2) f4_level_ne)

end

end VOA.DeligneAudit.F4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.F4Lie.clF4_rel_zero
#print axioms VOA.DeligneAudit.F4Lie.I2ns_le_ker
#print axioms VOA.DeligneAudit.F4Lie.geometricCarrierEmbedding
#print axioms VOA.DeligneAudit.F4Lie.explicitCurrentJetSurjectivity
end AxiomAudit
