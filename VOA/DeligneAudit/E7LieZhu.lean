/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LiePresentation
import VOA.DeligneAudit.E7LieCasimirChecks
import VOA.DeligneAudit.DeligneVacuumRelationCarrier

/-!
# The inputs of the `targetLowerBound_of_carrierData` for `E₇`

`VacuumRelation.targetLowerBound_of_carrierData CD D k hk h hc c₀ hcas hrel` with

* `CD = DeligneCarrier.E7.E7data`, `D = e7CertData` (index `Fin 133 = Fin E7data.n`), `k = -4`,
  `hk = hk7`, `h = 18`;
* `hc = e7_hc`: `133·(-4)/(-4+18) = -2(18+1)`;
* `c₀ = 1/2`, `hcas = e7_casimir_match`: the Sugawara quadric `Σ κ⁻¹ᵢⱼ XᵢXⱼ` is `½ Q` (the cert
  Casimir of `E7data`);
* `hrel : ∀ r, (affineCurrentData e7CertData (-4) hk7).sym (quadraticRelation (E7data.rel r)) = 0`
  — the relation side (from the singular vector `simpleProjection_sv` and the propagation chain).
-/

namespace VOA.DeligneAudit.E7Lie

open VOA VOA.AffineGeneral MvPolynomial VOA.QuadraticJetCoefficientPairing

noncomputable section

theorem e7_hc : ((DeligneCarrier.E7.E7data.n : ℕ) : ℂ) * (-4) / (-4 + e7CertData.h) =
    -2 * (((18 : ℕ) : ℂ) + 1) := by
  rw [e7CertData_h]
  show ((133 : ℕ) : ℂ) * (-4) / (-4 + 18) = _
  norm_num

theorem dualx_eq_sum (a : Fin 133) : dualx a = ∑ c, ((Gi2 a c : ℂ) / 2) • xs c := by
  unfold dualx Gi2
  induction Gi2L a with
  | nil => simp
  | cons t l ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.cast_add, add_div, add_smul,
        Finset.sum_add_distrib, apply_ite (fun z : ℤ => (z : ℂ)), Int.cast_zero, zero_div,
        ite_div, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem kappaInv_eq (a b : Fin 133) : e7CertData.kappaInv a b = (Gi2 a b : ℂ) / 2 := by
  rw [LieData.kappaInv, LieData.coordinates, LieData.dualGenerator, e7CertData_dual,
    e7CertData_basis, dualx_eq_sum, repr_sum]

theorem quadP_flatMap {α : Type*} (L : List α) (g : α → List (ℕ × ℕ × ℤ)) :
    E7Sparse.quadP 133 (L.flatMap g) = (L.map fun a => E7Sparse.quadP 133 (g a)).sum := by
  induction L with
  | nil => simp [E7Sparse.quadP]
  | cons a L ih => rw [List.flatMap_cons, E7Sparse.quadP_append, ih, List.map_cons, List.sum_cons]

theorem row_eq (i : Fin 133) :
    ∑ j, MvPolynomial.C ((Gi2 i j : ℂ) / 2) * (X i * X j) =
      MvPolynomial.C (1 / 2 : ℂ) * E7Sparse.quadP 133 ((Gi2L i).map fun t => (i.val, t.1.val, t.2)) := by
  unfold Gi2
  induction Gi2L i with
  | nil => simp [E7Sparse.quadP]
  | cons t l ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, add_div, map_add, add_mul,
        Finset.sum_add_distrib, ih, E7Sparse.quadP_cons, Xn_val]
      have h1 : ∑ j, MvPolynomial.C ((((if t.1 = j then t.2 else 0 : ℤ)) : ℂ) / 2) * (X i * X j) =
          MvPolynomial.C ((t.2 : ℂ) / 2) * (X i * X t.1) := by
        rw [Finset.sum_eq_single t.1]
        · simp
        · intro j _ hj; rw [if_neg (Ne.symm hj)]; simp
        · simp
      rw [h1]
      have hC : MvPolynomial.C ((t.2 : ℂ) / 2) =
          MvPolynomial.C (1 / 2 : ℂ) * (t.2 : MvPolynomial (Fin 133) ℂ) := by
        rw [← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 133) ℂ) t.2, ← map_mul]
        congr 1
        ring
      rw [hC]
      ring

theorem casimir_match' :
    (∑ i, ∑ j, MvPolynomial.C (e7CertData.kappaInv i j) * (X i * X j)) =
      MvPolynomial.C (1 / 2 : ℂ) * quadraticRelation DeligneCarrier.E7.cas := by
  simp only [kappaInv_eq, row_eq]
  rw [← Finset.mul_sum, DeligneCarrier.E7.quadraticRelation_cas]
  refine congrArg (MvPolynomial.C (1 / 2 : ℂ) * ·) ?_
  have h0 := E7Sparse.quadP_eq_zero_of_quadZero (n := 133) _ giList_eq_qQ
  rw [E7Sparse.quadP_append, E7Sparse.quadP_scaleQ] at h0
  have hg : E7Sparse.quadP 133 giList = E7Sparse.quadP 133 DeligneCarrier.E7.qQ := by
    push_cast at h0
    linear_combination h0
  rw [← hg, giList, quadP_flatMap, ← List.sum_ofFn, List.ofFn_eq_map]

/-- **The Casimir match** for `targetLowerBound_of_carrierData`: `casPoly = ½ · Q`. -/
theorem e7_casimir_match :
    (VacuumRelation.affineCurrentData (ι := Fin DeligneCarrier.E7.E7data.n) e7CertData (-4)
      hk7).casPoly = MvPolynomial.C (1 / 2 : ℂ) * DeligneCarrier.E7.E7data.Q :=
  casimir_match'

/-- **The target bound for `E₇`**, from the relation symbols `hrel`. -/
theorem e7_targetLowerBound_of_rel
    (hrel : ∀ r, (VacuumRelation.affineCurrentData (ι := Fin DeligneCarrier.E7.E7data.n)
      e7CertData (-4) hk7).sym (quadraticRelation (DeligneCarrier.E7.E7data.rel r)) = 0) :
    DeligneCharacter.TargetLowerBoundQ W7 (DeligneCharacter.mldeCoeff 18) :=
  VacuumRelation.targetLowerBound_of_carrierData DeligneCarrier.E7.E7data e7CertData (-4) hk7 18
    e7_hc (1 / 2) e7_casimir_match hrel

end

end VOA.DeligneAudit.E7Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.E7Lie.e7_hc
#print axioms VOA.DeligneAudit.E7Lie.e7_casimir_match
#print axioms VOA.DeligneAudit.E7Lie.e7_targetLowerBound_of_rel
end AxiomAudit
