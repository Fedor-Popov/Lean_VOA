/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2LieSingular
import VOA.DeligneAudit.G2Sector
import VOA.DeligneAudit.G2LieSteps
import VOA.DeligneAudit.E6SectorSparse
import VOA.AffineGeneral.LiPresentation
import VOA.AffineGeneral.DeligneInstance
import VOA.DeligneAudit.A2CarrierUpperBound
import VOA.DeligneAudit.A2CurrentJetSurjectivity

/-!
# The explicit `G₂` presentation: `I₂ⁿˢ` lies in the `C₂` kernel of `L_{-5/3}(𝔤₂)`

`g2W = simpleVOA g2CertData (-5/3)` (currents in the `g2T` basis), `clG2` its
current-coordinate map into Li degree zero. The E₆ method (`E6Presentation`):

1. `clG2_rel_zero`: the highest relation `P₀ = -X₂² + 3X₅X₉ + 3X₆X₁₀` is in the kernel: its
   state is the weight-two singular vector `g2sv` (`g2sv_mem_maxIdeal`).
2. `clG2_step`: the kernel is stable under the coadjoint derivations (`clsG_adPoly_eq_zero`); each
   BFS step `P_k = ad(g) P_j` is a kernel-checked sparse identity (`G2LieSteps`).
3. `clG2_rel`: all 27 relations, by strong induction along `g2Steps`.
4. **`I2ns_le_ker`**, **`explicitPresentation`** (`ideal := G2data.I`),
   **`explicitCurrentJetSurjectivity`**, **`geometricCarrierEmbedding`** (via
   `geometricCarrierEmbedding_of_quadraticIdeal`).
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.G2Lie

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse
  VOA.DeligneAudit.E6SectorSparse VOA.AffineGeneral VOA.AffineGeneral.SCLie
  VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.CarrierEmbedding
  VOA.DeligneAudit.DeligneSector.G2

noncomputable section

/-- The current-coordinate map of `L_{-5/3}(𝔤₂)` into Li degree zero. -/
abbrev clG2 := clsG g2W (genS g2CertData (-5/3) g2_level_ne)
  (genS_weight_one g2CertData (-5/3) g2_level_ne)

theorem scF_eq : scF g2T 14 = g2CertData.structureConstant := by
  funext x y c
  rw [g2CertData_sc]
  rfl

theorem adPoly_quadP (x : Fin 14) (l : List (ℕ × ℕ × ℤ)) (hl : qInRange 14 l = true) :
    adPolyT g2CertData.structureConstant x (quadP 14 l) = quadP 14 (adS g2T x l) := by
  rw [← scF_eq]
  exact adDer_quadP g2_bound x l hl

/-! ## The highest relation -/

theorem relQ_zero : relQ 0 = [(2, 2, -1), (5, 9, 3), (6, 10, 3)] := by decide +kernel

theorem quadP_relQ_zero : quadP 14 (relQ 0) = quadPoly (termsZC g2svTerms) := by
  rw [relQ_zero]
  simp [quadP, quadPoly, termsZC, g2svTerms, Xn, MvPolynomial.smul_eq_C_mul, map_ofNat]

theorem clG2_rel_zero : clG2 (quadP 14 (relQ 0)) = 0 := by
  rw [quadP_relQ_zero]
  exact clsG_quad_eq_zero g2CertData (-5/3) g2_level_ne _ g2sv_mem_maxIdeal

/-! ## Propagation -/

theorem relQ_qInRange (j : ℕ) (hj : j < 27) : qInRange 14 (relQ j) = true := by
  have h := relZ_range (k := j) (by omega)
  simp only [relZ, hj, if_true] at h
  simp only [qInRange, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact h

theorem clG2_step (st : ℕ × ℕ × ℕ) (h : stepOK st = true) (hj : clG2 (quadP 14 (relQ st.2.1)) = 0) :
    clG2 (quadP 14 (relQ st.2.2)) = 0 := by
  obtain ⟨g, j, k⟩ := st
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hg, hjk⟩, hk⟩, hz⟩ := h
  have h0 := quadP_eq_zero_of_quadZero (n := 14) (by norm_num) _ hz
  rw [quadP_append', quadP_scaleQ] at h0
  have heq : quadP 14 (relQ k) = quadP 14 (adS g2T g (relQ j)) := by
    push_cast at h0
    linear_combination -h0
  have had := clsG_adPoly_eq_zero g2CertData (-5/3) g2_level_ne ⟨g, hg⟩ hj
  rw [adPoly_quadP ⟨g, hg⟩ _ (relQ_qInRange j (by omega))] at had
  rw [heq]
  exact had

theorem clG2_rel_lt : ∀ k, k < 27 → clG2 (quadP 14 (relQ k)) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact clG2_rel_zero
    · have hmem : k ∈ g2Steps.map (·.2.2) := by
        rw [g2Steps_targets, List.mem_range']; exact ⟨k - 1, by omega, by omega⟩
      obtain ⟨st, hst, hst2⟩ := List.mem_map.mp hmem
      have hok := List.all_eq_true.mp g2Steps_ok st hst
      have hlt : st.2.1 < st.2.2 := by
        simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1.1.2
      rw [← hst2]
      exact clG2_step st hok (ih _ (by omega) (by omega))

theorem clG2_rel (r : Fin 27) : clG2 (quadraticRelation (G2data.rel r)) = 0 := by
  have e1 : quadraticRelation (G2data.rel r) = quadP 14 (relQ r) := by
    rw [quadP_eq]; exact rel_poly r
  exact (congrArg clG2 e1).trans (clG2_rel_lt r r.2)

/-! ## The ideal and the presentation -/

/-- **`I₂ⁿˢ` is contained in the `C₂` kernel of `L_{-5/3}(𝔤₂)`.** -/
theorem I2ns_le_ker : G2data.I ≤ RingHom.ker
    (MvPolynomial.aeval fun i =>
      liDegreeZeroClass g2W 1 ⟨genS g2CertData (-5/3) g2_level_ne i,
        genS_weight_one g2CertData (-5/3) g2_level_ne i⟩).toRingHom := by
  intro p hp
  have hle : quadraticIdeal G2data.rel ≤ RingHom.ker clG2.toRingHom := by
    rw [quadraticIdeal, Ideal.span_le]
    rintro _ ⟨r, rfl⟩
    exact clG2_rel r
  exact hle hp

/-- **The explicit `G₂` presentation**: currents `J^a_{-1}|0⟩` of `L_{-5/3}(𝔤₂)`, ideal `I₂ⁿˢ`. -/
def explicitPresentation : CurrentC2Presentation .G2 g2W where
  gen := genS g2CertData (-5/3) g2_level_ne
  gen_weight_one := genS_weight_one g2CertData (-5/3) g2_level_ne
  ideal := G2data.I
  relations := I2ns_le_ker

theorem explicitPresentation_ideal : explicitPresentation.ideal = quadraticIdeal G2data.rel := rfl

/-- **The geometric carrier embedding** for the explicit `G₂` presentation. -/
def geometricCarrierEmbedding :
    GeometricCarrierEmbedding .G2 g2W explicitPresentation (Carrier G2data.rel) :=
  geometricCarrierEmbedding_of_quadraticIdeal explicitPresentation G2data.rel rfl

/-- **`CurrentJetSurjectivity` for the explicit `G₂` presentation.** -/
theorem explicitCurrentJetSurjectivity : CurrentJetSurjectivity .G2 g2W explicitPresentation :=
  DeligneAudit.currentJetSurjectivity_of_genWordSpan explicitPresentation
    (VOA.AffineGeneral.Deligne.genWordsSpan .G2 g2CertData (-5/3) g2_level_ne)

end

end VOA.DeligneAudit.G2Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Lie.clG2_rel_zero
#print axioms VOA.DeligneAudit.G2Lie.I2ns_le_ker
#print axioms VOA.DeligneAudit.G2Lie.geometricCarrierEmbedding
#print axioms VOA.DeligneAudit.G2Lie.explicitCurrentJetSurjectivity
end AxiomAudit
