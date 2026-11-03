/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2LiePresentation
import VOA.DeligneAudit.DeligneVacuumRelationCarrier

/-!
# `G₂`: the vacuum quartic relation of `L_{-5/3}(𝔤₂)` and the MLDE target bound

the `targetLowerBound_of_carrierData` for `CD = G2data` and `D = g2CertData`, `k = -5/3`:

* `g2_hc`: `14·(-5/3)/(-5/3+4) = -10 = -2(4+1)`;
* `g2_casimir_match`: `casPoly = ⅓ Q`; here `κ⁻¹ᵢⱼ = coef(dlᵢ, j)/Dᵢ` (`kappaInv_eq`) and the sparse
  identity `3 casPoly = Q` is a kernel `quadZero` check (`casList_ok`);
* `sym_rel_zero`: the highest relation `P₀` from the singular vector `g2sv` (`sym_singular`, two
  integer shadow checks);
* `sym_rel`: all 27 relations along `g2Steps` (`sym_step`; `adG` is `adPolyT`);
* `g2_vacuumQuarticRelation`, `g2_targetLowerBound`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.G2Lie

open MvPolynomial VOA VOA.AffineGeneral VOA.AffineGeneral.SCLie VOA.DeligneAudit.VacuumRelation
  VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
  VOA.DeligneAudit.DeligneSector.G2

noncomputable section

/-- The square-bracket current data of `L_{-5/3}(𝔤₂)`. -/
abbrev G2C : SqCurrentData g2W (Fin 14) := affineCurrentData g2CertData (-5/3) g2_level_ne

theorem g2_hc : ((G2data.n : ℕ) : ℂ) * (-5/3) / (-5/3 + g2CertData.h) =
    -2 * (((4 : ℕ) : ℂ) + 1) := by
  rw [g2CertData_h]
  change ((14 : ℕ) : ℂ) * (-5/3) / (-5/3 + 4) = _
  norm_num

/-! ## The Casimir -/

theorem kappaInv_eq (a c : Fin 14) :
    g2CertData.kappaInv a c = (g2D a : ℂ)⁻¹ * (coef (g2dl a) c : ℂ) := by
  change (Pi.basisFun ℂ (Fin 14)).repr (dualV g2Checks g2dl g2D a) c = _
  rw [Pi.basisFun_repr]
  rfl

/-- `3 / Dᵢ`. -/
def eD (i : ℕ) : ℤ := 3 / g2D i

theorem eD_mul : ∀ i : Fin 14, eD i * g2D i = 3 := by decide +kernel

theorem g2D_inv (i : Fin 14) : (g2D i : ℂ)⁻¹ = (1 / 3 : ℂ) * (eD i : ℂ) := by
  have h : ((eD i : ℤ) : ℂ) * (g2D i : ℂ) = 3 := by exact_mod_cast eD_mul i
  exact inv_eq_of_mul_eq_one_right (by linear_combination h / 3)

theorem row_gen (i : Fin 14) (d : ℂ) (l : List (ℕ × ℤ)) :
    ∑ j : Fin 14, MvPolynomial.C (d * (coef l j : ℂ)) * (X i * X j) =
      MvPolynomial.C d * (l.map fun t => ((t.2 : ℤ) : MvPolynomial (Fin 14) ℂ) *
        (X i * Xn 14 t.1)).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
      have hsplit : ∀ j : Fin 14, MvPolynomial.C (d * (coef (t :: l) j : ℂ)) * (X i * X j) =
          MvPolynomial.C (d * ((if t.1 = (j : ℕ) then t.2 else 0 : ℤ) : ℂ)) * (X i * X j) +
            MvPolynomial.C (d * (coef l j : ℂ)) * (X i * X j) := by
        intro j
        rw [coef_cons, Int.cast_add, mul_add, map_add, add_mul]
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, ih, List.map_cons,
        List.sum_cons, mul_add]
      congr 1
      by_cases ht : t.1 < 14
      · rw [Finset.sum_eq_single ⟨t.1, ht⟩]
        · rw [if_pos rfl, Xn, dif_pos ht, map_mul, map_intCast]
          ring
        · intro j _ hj
          rw [if_neg (fun h => hj (Fin.ext h.symm)), Int.cast_zero, mul_zero, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_zero (fun j _ => by
          rw [if_neg (fun h => ht (by rw [h]; exact j.2)), Int.cast_zero, mul_zero, map_zero,
            zero_mul]),
          Xn, dif_neg ht, mul_zero, mul_zero, mul_zero]

/-- The rows of `3 casPoly` as a sparse quadratic list. -/
def casList : List (ℕ × ℕ × ℤ) :=
  (List.finRange 14).flatMap fun (i : Fin 14) => (g2dl i).map fun t => (i.val, t.1, eD i * t.2)

theorem casList_ok : quadZero (casList ++ scaleQ (-1) qQ) = true := by decide +kernel

theorem row_eq (i : Fin 14) :
    ∑ j, MvPolynomial.C (g2CertData.kappaInv i j) * (X i * X j) =
      MvPolynomial.C (1 / 3 : ℂ) *
        quadP 14 ((g2dl i).map fun t => (i.val, t.1, eD i * t.2)) := by
  simp only [kappaInv_eq, g2D_inv]
  rw [row_gen i (1 / 3 * (eD i : ℂ)), map_mul, mul_assoc]
  congr 1
  simp only [quadP, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  have hi : Xn 14 (i : ℕ) = X i := by simp [Xn]
  simp only [Function.comp_apply, hi]
  push_cast
  rw [map_intCast]
  ring

theorem casimir_match' :
    (∑ i, ∑ j, MvPolynomial.C (g2CertData.kappaInv i j) * (X i * X j)) =
      MvPolynomial.C (1 / 3 : ℂ) * quadraticRelation cas := by
  simp only [row_eq]
  rw [← Finset.mul_sum, cas_poly, ← quadP_eq]
  congr 1
  have h0 := quadP_eq_zero_of_quadZero (n := 14) (by norm_num) _ casList_ok
  rw [quadP_append', quadP_scaleQ] at h0
  have hg : quadP 14 casList = quadP 14 qQ := by
    push_cast at h0
    linear_combination h0
  rw [← hg, casList, quadP_flatMap', ← List.sum_ofFn, List.ofFn_eq_map]

/-- **The Casimir match**: `casPoly = ⅓ · Q`. -/
theorem g2_casimir_match :
    (affineCurrentData (ι := Fin G2data.n) g2CertData (-5/3) g2_level_ne).casPoly =
      MvPolynomial.C (1 / 3 : ℂ) * G2data.Q :=
  casimir_match'

/-! ## The relation symbols -/

/-- The singular vector `P₀ = -X₂² + 3X₅X₉ + 3X₆X₁₀`: coefficients and indices. -/
def cz : Fin 3 → ℤ := ![-1, 3, 3]
def ta : Fin 3 → Fin 14 := ![2, 5, 6]
def tb : Fin 3 → Fin 14 := ![2, 9, 10]

/-- Integer bracket shadow of `P₀`. -/
theorem hw_bracket_shadowZ : ∀ e : Fin 14, ∑ s, cz s * g2scZ (ta s) (tb s) e = 0 := by
  decide +kernel

/-- Integer form shadow of `P₀`. -/
theorem hw_form_shadowZ : ∑ s, cz s * g2fZ (ta s) (tb s) = 0 := by decide +kernel

theorem sym_hw : G2C.sym (∑ s, (cz s : ℂ) • (X (ta s) * X (tb s))) = 0 := by
  refine sym_singular g2CertData (-5/3) g2_level_ne (fun s => (cz s : ℂ)) ta tb ?_ ?_ ?_
  · have h := g2sv_proj
    rw [g2sv, quadState] at h
    simpa [termsZC, g2svTerms, Fin.sum_univ_three, cz, ta, tb, add_assoc] using h
  · intro e
    have h := hw_bracket_shadowZ e
    simp only [g2scZ] at h
    simp only [g2CertData_sc]
    exact_mod_cast h
  · have h := hw_form_shadowZ
    simp only [g2fZ] at h
    simp only [g2CertData_form]
    exact_mod_cast h

theorem sym_rel_zero : G2C.sym (quadP 14 (relQ 0)) = 0 := by
  have he : quadP 14 (relQ 0) = ∑ s, (cz s : ℂ) • (X (ta s) * X (tb s)) := by
    rw [relQ_zero]
    simp only [quadP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Fin.sum_univ_three, cz, ta, tb, Xn]
    simp [MvPolynomial.smul_eq_C_mul, map_ofNat]
    ring_nf
  rw [he]
  exact sym_hw

theorem sym_step' (st : ℕ × ℕ × ℕ) (h : stepOK st = true)
    (hj : G2C.sym (quadP 14 (relQ st.2.1)) = 0) : G2C.sym (quadP 14 (relQ st.2.2)) = 0 := by
  obtain ⟨g, j, k⟩ := st
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hg, hjk⟩, hk⟩, hz⟩ := h
  have h0 := quadP_eq_zero_of_quadZero (n := 14) (by norm_num) _ hz
  rw [quadP_append', quadP_scaleQ] at h0
  have heq : quadP 14 (relQ k) = quadP 14 (adS g2T g (relQ j)) := by
    push_cast at h0
    linear_combination -h0
  have had := adPoly_quadP ⟨g, hg⟩ _ (relQ_qInRange j (by omega))
  refine sym_step g2CertData (-5/3) g2_level_ne (b := ⟨g, hg⟩) (p := 1) (q := 1) one_ne_zero
    ?_ hj
  rw [one_smul, one_smul, heq, ← had]
  rfl

theorem sym_rel_lt : ∀ k, k < 27 → G2C.sym (quadP 14 (relQ k)) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact sym_rel_zero
    · have hmem : k ∈ g2Steps.map (·.2.2) := by
        rw [g2Steps_targets, List.mem_range']; exact ⟨k - 1, by omega, by omega⟩
      obtain ⟨st, hst, hst2⟩ := List.mem_map.mp hmem
      have hok := List.all_eq_true.mp g2Steps_ok st hst
      have hlt : st.2.1 < st.2.2 := by
        simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1.1.2
      rw [← hst2]
      exact sym_step' st hok (ih _ (by omega) (by omega))

/-- **The relation symbols of `G2data`** (the `hrel` for `G₂`). -/
theorem g2_hrel (r : Fin 27) :
    (affineCurrentData (ι := Fin G2data.n) g2CertData (-5/3) g2_level_ne).sym
      (quadraticRelation (G2data.rel r)) = 0 := by
  have e1 : quadraticRelation (G2data.rel r) = quadP 14 (relQ r) := by
    rw [quadP_eq]; exact rel_poly r
  exact (congrArg G2C.sym e1).trans (sym_rel_lt r r.2)

/-- **The vacuum quartic relation of `L_{-5/3}(𝔤₂)`.** -/
theorem g2_vacuumQuarticRelation :
    DeligneMLDE.VacuumQuarticRelation g2W
      (5 / 4 * g2W.centralCharge ^ 2 + 11 / 2 * g2W.centralCharge) :=
  vacuumQuarticRelation_of_carrierData G2data g2CertData (-5/3) g2_level_ne (1 / 3)
    g2_casimir_match g2_hrel

theorem g2W_centralCharge : g2W.centralCharge = -2 * (((4 : ℕ) : ℂ) + 1) := by
  rw [simple_centralCharge', Fintype.card_fin]
  exact g2_hc

theorem g2W_vacuum_ne_zero : g2W.vacuum ≠ 0 := simple_vacuum_ne_zero' _ _ _

/-- **The `G₂` target lower bound** `dim (L_{-5/3}(𝔤₂))_N ≥ mldeCoeff 4 N`, unconditional. -/
theorem g2_targetLowerBound :
    DeligneCharacter.TargetLowerBoundQ g2W (DeligneCharacter.mldeCoeff 4) :=
  targetLowerBound_of_carrierData G2data g2CertData (-5/3) g2_level_ne 4 g2_hc (1 / 3)
    g2_casimir_match g2_hrel

end

end VOA.DeligneAudit.G2Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Lie.g2_casimir_match
#print axioms VOA.DeligneAudit.G2Lie.g2_hrel
#print axioms VOA.DeligneAudit.G2Lie.g2_vacuumQuarticRelation
#print axioms VOA.DeligneAudit.G2Lie.g2_targetLowerBound
end AxiomAudit
