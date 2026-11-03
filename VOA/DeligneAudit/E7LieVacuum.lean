/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieZhu
import VOA.DeligneAudit.DeligneVacuumRelationAffine

/-!
# `E₇`: the relation symbols, the vacuum quartic relation and the target bound

Following the `D₄` proof (`DeligneVacuumRelationD4`), for `W7 = L_{-4}(𝔢₇)` in the cert basis:

* relation `0` (the highest one): `sym_singular` from the singular vector (`simpleProjection_sv`) and two
  integer shadow checks (`hw7_bracket_shadowZ`, `hw7_form_shadowZ`);
* relations `k ≥ 1`: the kernel-checked propagation identities (`stepOK k`: `ad_b P_j = p P_k`) through
  the `sym_step`, by strong induction (`sym7_relQ`);
* **`e7_hrel`**: `sym (quadraticRelation (E7data.rel r)) = 0` for all 1539 relations;
* **`e7_targetLowerBound : TargetLowerBoundQ W7 (mldeCoeff 18)`**, unconditional (via
  `e7_targetLowerBound_of_rel`, i.e. `targetLowerBound_of_carrierData`).
-/

namespace VOA.DeligneAudit.E7Lie

open MvPolynomial VOA VOA.AffineGeneral VOA.DeligneAudit.VacuumRelation
  VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E7Sparse

noncomputable section

/-- The square-bracket current data of `L_{-4}(𝔢₇)`. -/
abbrev E7 : SqCurrentData W7 (Fin 133) := affineCurrentData e7CertData (-4) hk7

theorem hw7_bracket_shadowZ : ∀ e : Fin 133, ∑ i, cz i * sZ (ta i) (tb i) e = 0 := by
  decide +kernel

theorem hw7_form_shadowZ : ∑ i, cz i * Gz (ta i) (tb i) = 0 := by decide +kernel

theorem sym7_hw : E7.sym (∑ i, (cz i : ℂ) • (X (ta i) * X (tb i))) = 0 := by
  refine sym_singular e7CertData (-4) hk7 (fun i => (cz i : ℂ)) ta tb ?_ ?_ ?_
  · have h := simpleProjection_sv
    rw [sv] at h
    simpa [w2] using h
  · intro e
    have h := hw7_bracket_shadowZ e
    simp only [structureConstant_eq]
    exact_mod_cast h
  · have h := hw7_form_shadowZ
    simp only [formTable_eq]
    exact_mod_cast h

theorem sym7_rel0 : E7.sym (quadP 133 (DeligneCarrier.E7.relQ 0)) = 0 :=
  (congrArg E7.sym quadP_relQ0).trans sym7_hw

/-- The polynomial identity of step `k`. -/
theorem step7_identity (k : ℕ) (hk : stepOK k = true) :
    (1 : ℂ) • adG e7CertData.structureConstant ⟨(recipe k).2.1 % 133, Nat.mod_lt _ (by decide)⟩
      (quadP 133 (DeligneCarrier.E7.relQ (recipe k).1)) =
      ((recipe k).2.2 : ℂ) • quadP 133 (DeligneCarrier.E7.relQ k) := by
  unfold stepOK at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨_, hz⟩ := hk
  have h0 := quadP_eq_zero_of_quadZero (n := 133) _ hz
  rw [quadP_append, quadP_scaleQ, ← ad7_quadP] at h0
  rw [one_smul, smul_eq_C_mul]
  rw [Int.cast_neg, neg_mul, add_neg_eq_zero] at h0
  change ad7 _ _ = _
  rw [h0]
  simp

theorem stepOK_p (k : ℕ) (hk : stepOK k = true) : ((recipe k).2.2 : ℂ) ≠ 0 := by
  unfold stepOK at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact_mod_cast hk.1.2

theorem stepOK_j (k : ℕ) (hk : stepOK k = true) : (recipe k).1 < k := by
  unfold stepOK at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact hk.1.1.1

/-- **All 1539 relation symbols vanish.** -/
theorem sym7_relQ (k : ℕ) (hk : k < 1539) : E7.sym (quadP 133 (DeligneCarrier.E7.relQ k)) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      by_cases h0 : k = 0
      · subst h0; exact sym7_rel0
      · have hs := stepOK_all k (Nat.pos_of_ne_zero h0) hk
        exact sym_step e7CertData (-4) hk7 (stepOK_p k hs) (step7_identity k hs)
          (ih _ (stepOK_j k hs) (by have := stepOK_j k hs; omega))

/-- **The relation symbols of `E7data`**, the `hrel` for `E₇`. -/
theorem e7_hrel (r' : Fin 1539) :
    (affineCurrentData (ι := Fin DeligneCarrier.E7.E7data.n) e7CertData (-4) hk7).sym
      (quadraticRelation (DeligneCarrier.E7.E7data.rel r')) = 0 :=
  (congrArg E7.sym (DeligneCarrier.E7.quadraticRelation_rel r')).trans (sym7_relQ r'.val r'.isLt)

/-- **The `E₇` target lower bound** `dim (L_{-4}(𝔢₇))_N ≥ mldeCoeff 18 N`, unconditional. -/
theorem e7_targetLowerBound : DeligneCharacter.TargetLowerBoundQ W7 (DeligneCharacter.mldeCoeff 18) :=
  e7_targetLowerBound_of_rel (e7_hrel)

end

end VOA.DeligneAudit.E7Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.E7Lie.sym7_relQ
#print axioms VOA.DeligneAudit.E7Lie.e7_targetLowerBound
end AxiomAudit
