/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieSingular
import VOA.DeligneAudit.D4LiePresentationBase
import VOA.DeligneAudit.E7CarrierData
import VOA.DeligneAudit.E7LieStepsA
import VOA.DeligneAudit.E7LieStepsB
import VOA.DeligneAudit.E7LieStepsC
import VOA.DeligneAudit.E7LieStepsD
import VOA.DeligneAudit.E7LieStepsE
import VOA.DeligneAudit.E7LieStepsF
import VOA.DeligneAudit.E7LieStepsG
import VOA.DeligneAudit.E7LieStepsH
import VOA.DeligneAudit.A2CarrierUpperBound
import VOA.DeligneAudit.A2CurrentJetSurjectivity

/-!
# The explicit `E₇` presentation of `L_{-4}(𝔢₇)`

`W7 = simpleVOA e7CertData (-4)` (cert basis of the lattice `e7Lie`).

* `cls7_rel0`: relation `0` of `E7CarrierTables` (the symbol of the singular vector) is in the kernel.
* `ad7_quadP`: the coadjoint derivation on sparse quadrics is `adQ` (`E7LieStepDefs`); with the
  chunked checks `steps_ok0..7` (`ad_b P_j = p P_k`, `j < k`) and the `ad`-stability of the kernel,
  **`cls7_relQ`**: all 1539 relations of `I₂ⁿˢ = 1539` vanish in the `C₂` algebra.
* `I2ns_le_ker7`, **`explicitPresentation7 : CurrentC2Presentation .E7 W7`** (ideal `E7data.I`),
  `explicitCurrentJetSurjectivity7`, `explicitGeometricCarrierEmbedding7`,
  **`explicit7_classicallyFree_of_char`**, `explicit7_classicallyFree_of_upperBound`.
-/

namespace VOA.DeligneAudit.E7Lie

open VOA VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone MvPolynomial
  VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.CarrierEmbedding VOA.DeligneAudit.E7Sparse

noncomputable section

/-! ## `L_{-4}(𝔢₇)` and its currents -/

/-- `L_{-4}(𝔢₇)`. -/
abbrev W7 := simpleVOA e7CertData (-4) hk7

/-- The current generators. -/
abbrev gen7 (a : Fin 133) : Vacuum e7CertData (-4) ⧸ maxIdeal e7CertData (-4) hk7 :=
  simpleCurrentState e7CertData (-4) hk7 (e7CertData.generator a)

theorem gen7_weight_one (a : Fin 133) : gen7 a ∈ W7.grading (1 : ℤ) :=
  simpleCurrentState_mem e7CertData (-4) hk7 a

/-- The current-coordinate map of `L_{-4}(𝔢₇)`. -/
abbrev cls7 : MvPolynomial (Fin 133) ℂ →ₐ[ℂ] liAssociatedGraded W7 :=
  D4Lie.clsG' W7 gen7 gen7_weight_one

theorem gen7_eq_proj (a : Fin 133) :
    gen7 a = simpleProjection e7CertData (-4) hk7
      (J e7CertData (-4) a (-1) (vacuumA e7CertData (-4))) := rfl

theorem smul_gen7_proj (a : Fin 133) (m : ℤ) (x : Vacuum e7CertData (-4)) :
    W7.smul (gen7 a) m (simpleProjection e7CertData (-4) hk7 x) =
      simpleProjection e7CertData (-4) hk7 (J e7CertData (-4) a m x) := by
  have h := SimpleQuot.maxQuotientVOA_mkQ_smul (affineVOA e7CertData (-4) hk7)
    (J e7CertData (-4) a (-1) (vacuumA e7CertData (-4))) m x
  rw [D4Lie.smulJ] at h
  exact h

theorem smul_gen7_zero (b i : Fin 133) :
    W7.smul (gen7 b) 0 (gen7 i) = ∑ c, e7CertData.structureConstant b i c • gen7 c := by
  rw [gen7_eq_proj i, smul_gen7_proj, D4Lie.J_J_comm, D4Lie.J_vac_nonneg _ _ b le_rfl, map_zero,
    zero_add, if_neg (by norm_num), add_zero, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, zero_add, gen7_eq_proj c]

set_option maxHeartbeats 1000000 in -- `obtain` on the `Rep'` existential is slow here
theorem hT7 (b i : Fin 133) :
    ∃ h : W7.smul (gen7 b) 0 (gen7 i) ∈ W7.grading ((1 : ℕ) : ℤ),
      liDegreeZeroClass W7 1 ⟨W7.smul (gen7 b) 0 (gen7 i), h⟩ =
        cls7 (∑ c, e7CertData.structureConstant b i c • X c) := by
  obtain ⟨hx, hEq⟩ := D4Lie.rep_sum' (W' := W7) (g := gen7) (hg := gen7_weight_one) Finset.univ
    (fun c => e7CertData.structureConstant b i c • X c) (N := 1)
    (fun c => e7CertData.structureConstant b i c • gen7 c)
    (fun c => D4Lie.rep_smul' (D4Lie.rep_X' W7 gen7 gen7_weight_one c) _)
  have hv := smul_gen7_zero b i
  refine ⟨by rw [hv]; exact hx, ?_⟩
  rw [hEq]
  exact congrArg (liDegreeZeroClass W7 1) (Subtype.ext hv)

/-- The coadjoint derivation of `𝔢₇` on the cert coordinates. -/
abbrev ad7 (b : Fin 133) := D4Lie.adPolyT' e7CertData.structureConstant b

theorem cls7_ad (b : Fin 133) {p : MvPolynomial (Fin 133) ℂ} (hp : cls7 p = 0) :
    cls7 (ad7 b p) = 0 :=
  D4Lie.clsG_adPolyT_eq_zero' _ hT7 b hp

/-! ## The derivation on sparse quadrics -/

/-- `∑ c · X_i` of a sparse list. -/
def linP (L : List (ℕ × ℤ)) : MvPolynomial (Fin 133) ℂ :=
  (L.map fun s => (s.2 : MvPolynomial (Fin 133) ℂ) * Xn 133 s.1).sum

theorem ad7_X (b i : Fin 133) : ad7 b (X i) = ((sL b i).map fun t => (t.2 : ℂ) • X t.1).sum := by
  rw [ad7, D4Lie.adPolyT'_X]
  simp only [structureConstant_eq, sZ]
  induction sL b i with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, add_smul, Finset.sum_add_distrib, ih,
        apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]

theorem Xn_val (c : Fin 133) : Xn 133 c.val = X c := by
  rw [Xn, dif_pos c.isLt]

theorem ad7_Xn (b : Fin 133) (i : ℕ) : ad7 b (Xn 133 i) = linP (sLn b i) := by
  by_cases hi : i < 133
  · have hX : Xn 133 i = X ⟨i, hi⟩ := by rw [Xn, dif_pos hi]
    rw [hX, ad7_X, sLn, dif_pos hi, linP, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, Xn_val, smul_eq_C_mul]
    simp
  · rw [Xn, dif_neg hi, map_zero, sLn, dif_neg hi]
    rfl

theorem quadP_mapL (L : List (ℕ × ℤ)) (j : ℕ) (c : ℤ) :
    quadP 133 (L.map fun s => (s.1, j, c * s.2)) =
      (c : MvPolynomial (Fin 133) ℂ) * (linP L * Xn 133 j) := by
  induction L with
  | nil => simp [quadP, linP]
  | cons s L ih =>
      rw [List.map_cons, quadP_cons, ih]
      simp only [linP, List.map_cons, List.sum_cons]
      push_cast
      ring

theorem quadP_mapR (L : List (ℕ × ℤ)) (i : ℕ) (c : ℤ) :
    quadP 133 (L.map fun s => (i, s.1, c * s.2)) =
      (c : MvPolynomial (Fin 133) ℂ) * (Xn 133 i * linP L) := by
  induction L with
  | nil => simp [quadP, linP]
  | cons s L ih =>
      rw [List.map_cons, quadP_cons, ih]
      simp only [linP, List.map_cons, List.sum_cons]
      push_cast
      ring

theorem ad7_intCast_mul (b : Fin 133) (c : ℤ) (p : MvPolynomial (Fin 133) ℂ) :
    ad7 b ((c : MvPolynomial (Fin 133) ℂ) * p) = (c : MvPolynomial (Fin 133) ℂ) * ad7 b p := by
  have h : (c : MvPolynomial (Fin 133) ℂ) * p = (c : ℂ) • p := by
    rw [smul_eq_C_mul]; simp
  rw [h, Derivation.map_smul, smul_eq_C_mul]
  simp

/-- **The derivation on a sparse quadric.** -/
theorem ad7_quadP (b : Fin 133) (l : List (ℕ × ℕ × ℤ)) :
    ad7 b (quadP 133 l) = quadP 133 (adQ b l) := by
  induction l with
  | nil => simp [quadP, adQ]
  | cons t l ih =>
      rw [quadP_cons, map_add, ih]
      simp only [adQ, List.flatMap_cons, quadP_append, quadP_mapL, quadP_mapR]
      rw [ad7_intCast_mul, Derivation.leibniz, ad7_Xn, ad7_Xn, smul_eq_mul, smul_eq_mul]
      ring

/-! ## The chain over the 1539 relations -/

theorem stepOK_of_all {lo n k : ℕ} (h : (List.range' lo n).all stepOK = true) (hlo : lo ≤ k)
    (hhi : k < lo + n) : stepOK k = true :=
  List.all_eq_true.mp h k (List.mem_range'_1.mpr ⟨hlo, hhi⟩)

theorem stepOK_all (k : ℕ) (h1 : 1 ≤ k) (h2 : k < 1539) : stepOK k = true := by
  have go : ∀ (lo n : ℕ), (List.range' lo n).all stepOK = true → lo ≤ k → k < lo + n →
      stepOK k = true := fun lo n h hlo hhi => stepOK_of_all h hlo hhi
  by_cases c0 : k < 194; · exact go 1 193 steps_ok0 h1 (by omega)
  by_cases c1 : k < 387; · exact go 194 193 steps_ok1 (by omega) (by omega)
  by_cases c2 : k < 580; · exact go 387 193 steps_ok2 (by omega) (by omega)
  by_cases c3 : k < 773; · exact go 580 193 steps_ok3 (by omega) (by omega)
  by_cases c4 : k < 966; · exact go 773 193 steps_ok4 (by omega) (by omega)
  by_cases c5 : k < 1159; · exact go 966 193 steps_ok5 (by omega) (by omega)
  by_cases c6 : k < 1352; · exact go 1159 193 steps_ok6 (by omega) (by omega)
  exact go 1352 187 steps_ok7 (by omega) (by omega)

/-- One step of the chain. -/
theorem cls7_step (k : ℕ) (hk : stepOK k = true)
    (hj : cls7 (quadP 133 (DeligneCarrier.E7.relQ (recipe k).1)) = 0) :
    cls7 (quadP 133 (DeligneCarrier.E7.relQ k)) = 0 := by
  unfold stepOK at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨_, hb⟩, hp⟩, hz⟩ := hk
  have h0 := quadP_eq_zero_of_quadZero (n := 133) _ hz
  rw [quadP_append, quadP_scaleQ, ← ad7_quadP] at h0
  have hq : ad7 ⟨(recipe k).2.1 % 133, Nat.mod_lt _ (by decide)⟩
      (quadP 133 (DeligneCarrier.E7.relQ (recipe k).1)) =
      MvPolynomial.C ((recipe k).2.2 : ℂ) * quadP 133 (DeligneCarrier.E7.relQ k) := by
    rw [Int.cast_neg, neg_mul, add_neg_eq_zero] at h0
    rw [h0]
    simp
  have h1 : cls7 (MvPolynomial.C ((recipe k).2.2 : ℂ) * quadP 133 (DeligneCarrier.E7.relQ k)) = 0 :=
    (congrArg cls7 hq).symm.trans (cls7_ad _ hj)
  have hp' : ((recipe k).2.2 : ℂ) ≠ 0 := by exact_mod_cast hp
  have e : quadP 133 (DeligneCarrier.E7.relQ k) = MvPolynomial.C ((recipe k).2.2 : ℂ)⁻¹ *
      (MvPolynomial.C ((recipe k).2.2 : ℂ) * quadP 133 (DeligneCarrier.E7.relQ k)) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hp', map_one, one_mul]
  calc cls7 (quadP 133 (DeligneCarrier.E7.relQ k))
      = cls7 (MvPolynomial.C ((recipe k).2.2 : ℂ)⁻¹ *
          (MvPolynomial.C ((recipe k).2.2 : ℂ) * quadP 133 (DeligneCarrier.E7.relQ k))) := congrArg cls7 e
    _ = cls7 (MvPolynomial.C ((recipe k).2.2 : ℂ)⁻¹) *
          cls7 (MvPolynomial.C ((recipe k).2.2 : ℂ) * quadP 133 (DeligneCarrier.E7.relQ k)) := map_mul _ _ _
    _ = 0 := (congrArg (cls7 (MvPolynomial.C ((recipe k).2.2 : ℂ)⁻¹) * ·) h1).trans (mul_zero _)

/-! ### Relation `0` from the singular vector -/

theorem relQ0 : DeligneCarrier.E7.relQ 0 =
    [(52, 69, -1), (56, 68, -1), (59, 67, -1), (62, 66, 1), (64, 65, -1)] := by
  decide +kernel

theorem smul_gen7_gen7 (a b : Fin 133) :
    W7.smul (gen7 a) (-1) (gen7 b) = simpleProjection e7CertData (-4) hk7 (w2 a b) := by
  rw [gen7_eq_proj b, smul_gen7_proj]
  rfl

theorem hw7_state_zero :
    ∑ i, (cz i : ℂ) • W7.smul (gen7 (ta i)) (-1) (gen7 (tb i)) = 0 := by
  simp only [smul_gen7_gen7, ← map_smul, ← map_sum]
  exact simpleProjection_sv

theorem cls7_hw_poly : cls7 (∑ i, (cz i : ℂ) • (X (ta i) * X (tb i))) = 0 := by
  have hP := D4Lie.rep_sum' (W' := W7) (g := gen7) (hg := gen7_weight_one) Finset.univ
    (fun i => (cz i : ℂ) • (X (ta i) * X (tb i))) (N := 2)
    (fun i => (cz i : ℂ) • W7.smul (gen7 (ta i)) (-1) (gen7 (tb i)))
    (fun i => D4Lie.rep_smul' (D4Lie.rep_mul' (D4Lie.rep_X' W7 gen7 gen7_weight_one _)
      (D4Lie.rep_X' W7 gen7 gen7_weight_one _)) _)
  rw [hw7_state_zero] at hP
  exact D4Lie.clsG_eq_zero_of_rep' hP (Submodule.zero_mem _)

theorem quadP_relQ0 :
    quadP 133 (DeligneCarrier.E7.relQ 0) = ∑ i, (cz i : ℂ) • (X (ta i) * X (tb i)) := by
  rw [relQ0]
  simp only [quadP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fin.sum_univ_five,
    ta, tb, cz]
  have e : ∀ i : ℕ, (hi : i < 133) → Xn 133 i = X ⟨i, hi⟩ := fun i hi => by rw [Xn, dif_pos hi]
  rw [e 52 (by decide), e 69 (by decide), e 56 (by decide), e 68 (by decide), e 59 (by decide),
    e 67 (by decide), e 62 (by decide), e 66 (by decide), e 64 (by decide), e 65 (by decide)]
  simp only [smul_eq_C_mul]
  simp
  ring

theorem cls7_rel0 : cls7 (quadP 133 (DeligneCarrier.E7.relQ 0)) = 0 :=
  (congrArg cls7 quadP_relQ0).trans cls7_hw_poly

/-- **All 1539 relations of `I₂ⁿˢ` vanish in the `C₂` algebra of `L_{-4}(𝔢₇)`.** -/
theorem cls7_relQ (k : ℕ) (hk : k < 1539) : cls7 (quadP 133 (DeligneCarrier.E7.relQ k)) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      by_cases h0 : k = 0
      · subst h0; exact cls7_rel0
      · have hs := stepOK_all k (Nat.pos_of_ne_zero h0) hk
        have hj : (recipe k).1 < k := by
          unfold stepOK at hs
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
          exact hs.1.1.1
        exact cls7_step k hs (ih _ hj (by omega))

/-- **`I₂ⁿˢ ⊆ ker`** on `L_{-4}(𝔢₇)`. -/
theorem I2ns_le_ker7 : DeligneCarrier.E7.E7data.I ≤ RingHom.ker
    (MvPolynomial.aeval fun i => liDegreeZeroClass W7 1 ⟨gen7 i, gen7_weight_one i⟩).toRingHom := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨r, rfl⟩
  refine RingHom.mem_ker.mpr ?_
  exact (congrArg cls7 (DeligneCarrier.E7.quadraticRelation_rel r)).trans
    (cls7_relQ r.val r.isLt)

/-- **The explicit `E₇` presentation**: the 133 cert currents of `L_{-4}(𝔢₇)`, ideal `I₂ⁿˢ`. -/
def explicitPresentation7 : CurrentC2Presentation .E7 W7 where
  gen := gen7
  gen_weight_one := gen7_weight_one
  ideal := DeligneCarrier.E7.E7data.I
  relations := I2ns_le_ker7

theorem explicitPresentation7_ideal :
    explicitPresentation7.ideal = quadraticIdeal DeligneCarrier.E7.rel := rfl

/-- `CurrentJetSurjectivity` (current-word spanning; independent of the ideal). -/
theorem explicitCurrentJetSurjectivity7 :
    CurrentJetSurjectivity .E7 W7 explicitPresentation7 :=
  DeligneAudit.currentJetSurjectivity_of_genWordSpan explicitPresentation7
    (Deligne.genWordsSpan .E7 e7CertData (-4) hk7)

/-- The geometric carrier embedding, with the literal carrier of the `E₇` relations. -/
def explicitGeometricCarrierEmbedding7 :
    GeometricCarrierEmbedding .E7 W7 explicitPresentation7 (Carrier DeligneCarrier.E7.rel) :=
  geometricCarrierEmbedding_of_quadraticIdeal explicitPresentation7 DeligneCarrier.E7.rel rfl

/-- **The `E₇` Deligne case on `L_{-4}(𝔢₇)` with the explicit ideal `I₂ⁿˢ`**, conditional only on
the character input for the literal carrier.  It also yields `ker = I₂ⁿˢ`. -/
theorem explicit7_classicallyFree_of_char
    (hchar : OrdinaryCarrierCharacter W7 (Carrier DeligneCarrier.E7.rel)) :
    CaseClassicallyFree .E7 W7 explicitPresentation7 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W7 1 ⟨explicitPresentation7.gen i,
          explicitPresentation7.gen_weight_one i⟩).toRingHom = explicitPresentation7.ideal :=
  caseClassicallyFree_of_explicit_inputs .E7 W7 explicitPresentation7 _
    explicitCurrentJetSurjectivity7 explicitGeometricCarrierEmbedding7 hchar

/-- The same from the carrier upper bound. -/
theorem explicit7_classicallyFree_of_upperBound
    (hbound : QuadraticCarrierUpperBound DeligneCarrier.E7.rel W7) :
    CaseClassicallyFree .E7 W7 explicitPresentation7 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W7 1 ⟨explicitPresentation7.gen i,
          explicitPresentation7.gen_weight_one i⟩).toRingHom = explicitPresentation7.ideal :=
  caseClassicallyFree_of_quadraticCarrierUpperBound explicitPresentation7 DeligneCarrier.E7.rel rfl
    explicitCurrentJetSurjectivity7 hbound

end

end VOA.DeligneAudit.E7Lie

section AxiomAudit
open VOA.DeligneAudit.E7Lie
#print axioms ad7_quadP
#print axioms cls7_relQ
#print axioms I2ns_le_ker7
#print axioms explicitCurrentJetSurjectivity7
#print axioms explicit7_classicallyFree_of_char
#print axioms explicit7_classicallyFree_of_upperBound
end AxiomAudit
