/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneVacuumRelationE8
import VOA.DeligneAudit.D4LiePresentationBase
import VOA.DeligneAudit.A2CarrierUpperBound
import VOA.DeligneAudit.A2CurrentJetSurjectivity

/-!
# The explicit `E₈` presentation of `L_{-6}(𝔢₈)`

`W8 = simpleVOA e8CertData (-6)` (cert basis of the lattice `e8Lie`), mirroring
`E7LiePresentation`.  The ingredients are those of the vacuum relation (`DeligneVacuumRelationE8`):

* `cls8_rel0`: relation `0` of `E8CarrierTables` is the symbol of the singular vector `sv`;
* `cls8_step`: the BFS step `ad x_f (P_p) = g · P_s` (`stepOK`, kernel-checked in
  `E8VacuumStepCheck*`) and `ad`-stability of the `C₂` kernel (`D4Lie.clsG_adPolyT_eq_zero'`);
* **`cls8_relQ`**: all 3875 relations of `I₂ⁿˢ = V(ω₁)` vanish in the `C₂` algebra;
* `I2ns_le_ker8`, **`explicitPresentation8 : CurrentC2Presentation .E8 W8`** (ideal `E8data.I`),
  `explicitCurrentJetSurjectivity8`, `explicitGeometricCarrierEmbedding8`,
  **`explicit8_classicallyFree_of_char`**, `explicit8_classicallyFree_of_upperBound`.
-/

namespace VOA.DeligneAudit.E8Lie

open VOA VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone MvPolynomial
  VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.CarrierEmbedding VOA.DeligneAudit.E7Sparse
  VOA.DeligneAudit.DeligneCarrier.E8 VOA.DeligneAudit.VacuumRelation

noncomputable section

/-! ## `L_{-6}(𝔢₈)` and its currents -/

/-- The current generators. -/
abbrev gen8 (a : Fin 248) : Vacuum e8CertData (-6) ⧸ maxIdeal e8CertData (-6) hk8 :=
  simpleCurrentState e8CertData (-6) hk8 (e8CertData.generator a)

theorem gen8_weight_one (a : Fin 248) : gen8 a ∈ W8.grading (1 : ℤ) :=
  simpleCurrentState_mem e8CertData (-6) hk8 a

/-- The current-coordinate map of `L_{-6}(𝔢₈)`. -/
abbrev cls8 : MvPolynomial (Fin 248) ℂ →ₐ[ℂ] liAssociatedGraded W8 :=
  D4Lie.clsG' W8 gen8 gen8_weight_one

theorem gen8_eq_proj (a : Fin 248) :
    gen8 a = simpleProjection e8CertData (-6) hk8
      (J e8CertData (-6) a (-1) (vacuumA e8CertData (-6))) := rfl

theorem smul_gen8_proj (a : Fin 248) (m : ℤ) (x : Vacuum e8CertData (-6)) :
    W8.smul (gen8 a) m (simpleProjection e8CertData (-6) hk8 x) =
      simpleProjection e8CertData (-6) hk8 (J e8CertData (-6) a m x) := by
  have h := SimpleQuot.maxQuotientVOA_mkQ_smul (affineVOA e8CertData (-6) hk8)
    (J e8CertData (-6) a (-1) (vacuumA e8CertData (-6))) m x
  rw [D4Lie.smulJ] at h
  exact h

theorem smul_gen8_zero (b i : Fin 248) :
    W8.smul (gen8 b) 0 (gen8 i) = ∑ c, e8CertData.structureConstant b i c • gen8 c := by
  rw [gen8_eq_proj i, smul_gen8_proj, D4Lie.J_J_comm, D4Lie.J_vac_nonneg _ _ b le_rfl, map_zero,
    zero_add, if_neg (by norm_num), add_zero, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, zero_add, gen8_eq_proj c]

set_option maxHeartbeats 1000000 in -- `obtain` on the `Rep'` existential is slow here
theorem hT8 (b i : Fin 248) :
    ∃ h : W8.smul (gen8 b) 0 (gen8 i) ∈ W8.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W8 1 ⟨W8.smul (gen8 b) 0 (gen8 i), h⟩ =
        cls8 (∑ c, e8CertData.structureConstant b i c • X c) := by
  obtain ⟨hx, hEq⟩ := D4Lie.rep_sum' (W' := W8) (g := gen8) (hg := gen8_weight_one) Finset.univ
    (fun c => e8CertData.structureConstant b i c • X c) (N := 1)
    (fun c => e8CertData.structureConstant b i c • gen8 c)
    (fun c => D4Lie.rep_smul' (D4Lie.rep_X' W8 gen8 gen8_weight_one c) _)
  have hv := smul_gen8_zero b i
  refine ⟨by rw [hv]; exact hx, ?_⟩
  rw [hEq]
  exact congrArg (liDegreeZeroClass W8 1) (Subtype.ext hv)

theorem cls8_ad (b : Fin 248) {p : MvPolynomial (Fin 248) ℂ} (hp : cls8 p = 0) :
    cls8 (adG e8CertData.structureConstant b p) = 0 :=
  D4Lie.clsG_adPolyT_eq_zero' _ hT8 b hp

/-! ## The chain over the 3875 relations -/

/-- The checked BFS step as a polynomial identity. -/
theorem step_identity (s : ℕ) (hs : s < 3875) (h : stepOK s = true) :
    ∃ (f : Fin 248), (stepOf s).1 < s ∧ (stepOf s).2.2 ≠ 0 ∧
      adG e8CertData.structureConstant f (quadP 248 (relQ (stepOf s).1)) =
        MvPolynomial.C ((stepOf s).2.2 : ℂ) * quadP 248 (relQ s) := by
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlt, hf⟩, hg⟩, hc⟩ := h
  have hz := quadP_eq_zero_of_check _ hc
  rw [stepList, quadP_append', quadP_map_scale,
    quadP_dQuad ⟨(stepOf s).2.1, hf⟩ _ (relQ_inRange _ (by omega))] at hz
  refine ⟨⟨(stepOf s).2.1, hf⟩, hlt, hg, ?_⟩
  rw [map_intCast]
  linear_combination hz

set_option maxHeartbeats 4000000 in
/-- One step of the chain in the `C₂` algebra. -/
theorem cls8_step (s : ℕ) (hs : s < 3875) (h : stepOK s = true)
    (hj : cls8 (quadP 248 (relQ (stepOf s).1)) = 0) : cls8 (quadP 248 (relQ s)) = 0 := by
  obtain ⟨f, _, hg, hq⟩ := step_identity s hs h
  have h1 : cls8 (MvPolynomial.C ((stepOf s).2.2 : ℂ) * quadP 248 (relQ s)) = 0 :=
    (congrArg cls8 hq).symm.trans (cls8_ad f hj)
  have hp' : ((stepOf s).2.2 : ℂ) ≠ 0 := by exact_mod_cast hg
  have e : quadP 248 (relQ s) = MvPolynomial.C ((stepOf s).2.2 : ℂ)⁻¹ *
      (MvPolynomial.C ((stepOf s).2.2 : ℂ) * quadP 248 (relQ s)) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hp', map_one, one_mul]
  calc cls8 (quadP 248 (relQ s))
      = cls8 (MvPolynomial.C ((stepOf s).2.2 : ℂ)⁻¹ *
          (MvPolynomial.C ((stepOf s).2.2 : ℂ) * quadP 248 (relQ s))) := congrArg cls8 e
    _ = cls8 (MvPolynomial.C ((stepOf s).2.2 : ℂ)⁻¹) *
          cls8 (MvPolynomial.C ((stepOf s).2.2 : ℂ) * quadP 248 (relQ s)) := map_mul _ _ _
    _ = 0 := (congrArg (cls8 (MvPolynomial.C ((stepOf s).2.2 : ℂ)⁻¹) * ·) h1).trans (mul_zero _)

/-! ### Relation `0` from the singular vector -/

theorem smul_gen8_gen8 (a b : Fin 248) :
    W8.smul (gen8 a) (-1) (gen8 b) = simpleProjection e8CertData (-6) hk8 (w2 a b) := by
  rw [gen8_eq_proj b, smul_gen8_proj]
  rfl

theorem hw8_state_zero :
    ∑ i, (cz i : ℂ) • W8.smul (gen8 (ta i)) (-1) (gen8 (tb i)) = 0 := by
  simp only [smul_gen8_gen8, ← map_smul, ← map_sum]
  exact simpleProjection_sv

theorem cls8_hw_poly : cls8 (∑ i, (cz i : ℂ) • (X (ta i) * X (tb i))) = 0 := by
  have hP := D4Lie.rep_sum' (W' := W8) (g := gen8) (hg := gen8_weight_one) Finset.univ
    (fun i => (cz i : ℂ) • (X (ta i) * X (tb i))) (N := 2)
    (fun i => (cz i : ℂ) • W8.smul (gen8 (ta i)) (-1) (gen8 (tb i)))
    (fun i => D4Lie.rep_smul' (D4Lie.rep_mul' (D4Lie.rep_X' W8 gen8 gen8_weight_one _)
      (D4Lie.rep_X' W8 gen8 gen8_weight_one _)) _)
  rw [hw8_state_zero] at hP
  exact D4Lie.clsG_eq_zero_of_rep' hP (Submodule.zero_mem _)

theorem quadP_relQ0 : quadP 248 (relQ 0) = ∑ i, (cz i : ℂ) • (X (ta i) * X (tb i)) := by
  rw [relQ_zero]
  simp only [quadP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fin.sum_univ_seven,
    ta, tb, cz, Xn]
  simp [MvPolynomial.smul_eq_C_mul]
  ring_nf

theorem cls8_rel0 : cls8 (quadP 248 (relQ 0)) = 0 :=
  (congrArg cls8 quadP_relQ0).trans cls8_hw_poly

/-- **All 3875 relations of `I₂ⁿˢ` vanish in the `C₂` algebra of `L_{-6}(𝔢₈)`.** -/
theorem cls8_relQ (k : ℕ) (hk : k < 3875) : cls8 (quadP 248 (relQ k)) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      by_cases h0 : k = 0
      · subst h0; exact cls8_rel0
      · have hs := stepOK_all k (Nat.pos_of_ne_zero h0) hk
        have hj : (stepOf k).1 < k := by
          simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hs
          exact hs.1.1.1
        exact cls8_step k hk hs (ih _ hj (by omega))

/-- **`I₂ⁿˢ ⊆ ker`** on `L_{-6}(𝔢₈)`. -/
theorem I2ns_le_ker8 : E8data.I ≤ RingHom.ker
    (MvPolynomial.aeval fun i => liDegreeZeroClass W8 1 ⟨gen8 i, gen8_weight_one i⟩).toRingHom := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨r, rfl⟩
  refine RingHom.mem_ker.mpr ?_
  exact (congrArg cls8 (quadraticRelation_rel r)).trans (cls8_relQ r.val r.isLt)

/-- **The explicit `E₈` presentation**: the 248 cert currents of `L_{-6}(𝔢₈)`, ideal `I₂ⁿˢ`. -/
def explicitPresentation8 : CurrentC2Presentation .E8 W8 where
  gen := gen8
  gen_weight_one := gen8_weight_one
  ideal := E8data.I
  relations := I2ns_le_ker8

theorem explicitPresentation8_ideal : explicitPresentation8.ideal = quadraticIdeal rel := rfl

/-- `CurrentJetSurjectivity` (current-word spanning; independent of the ideal). -/
theorem explicitCurrentJetSurjectivity8 :
    CurrentJetSurjectivity .E8 W8 explicitPresentation8 :=
  DeligneAudit.currentJetSurjectivity_of_genWordSpan explicitPresentation8
    (Deligne.genWordsSpan .E8 e8CertData (-6) hk8)

/-- The geometric carrier embedding, with the literal carrier of the `E₈` relations. -/
def explicitGeometricCarrierEmbedding8 :
    GeometricCarrierEmbedding .E8 W8 explicitPresentation8 (Carrier rel) :=
  geometricCarrierEmbedding_of_quadraticIdeal explicitPresentation8 rel rfl

/-- **The `E₈` Deligne case on `L_{-6}(𝔢₈)` with the explicit ideal `I₂ⁿˢ`**, conditional only on
the character input for the literal carrier.  It also yields `ker = I₂ⁿˢ`. -/
theorem explicit8_classicallyFree_of_char
    (hchar : OrdinaryCarrierCharacter W8 (Carrier rel)) :
    CaseClassicallyFree .E8 W8 explicitPresentation8 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W8 1 ⟨explicitPresentation8.gen i,
          explicitPresentation8.gen_weight_one i⟩).toRingHom = explicitPresentation8.ideal :=
  caseClassicallyFree_of_explicit_inputs .E8 W8 explicitPresentation8 _
    explicitCurrentJetSurjectivity8 explicitGeometricCarrierEmbedding8 hchar

/-- The same from the carrier upper bound. -/
theorem explicit8_classicallyFree_of_upperBound
    (hbound : QuadraticCarrierUpperBound rel W8) :
    CaseClassicallyFree .E8 W8 explicitPresentation8 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W8 1 ⟨explicitPresentation8.gen i,
          explicitPresentation8.gen_weight_one i⟩).toRingHom = explicitPresentation8.ideal :=
  caseClassicallyFree_of_quadraticCarrierUpperBound explicitPresentation8 rel rfl
    explicitCurrentJetSurjectivity8 hbound

end

end VOA.DeligneAudit.E8Lie

section AxiomAudit
open VOA.DeligneAudit.E8Lie
#print axioms cls8_relQ
#print axioms I2ns_le_ker8
#print axioms explicitCurrentJetSurjectivity8
#print axioms explicit8_classicallyFree_of_char
#print axioms explicit8_classicallyFree_of_upperBound
end AxiomAudit
