/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LiePresentation
import VOA.DeligneAudit.DeligneVacuumRelationCarrier

/-!
# `F₄`: the vacuum quartic relation of `L_{-5/2}(𝔣₄)` and the MLDE target bound

the `targetLowerBound_of_carrierData` for `CD = F4data` and `D = f4CertData`, `k = -5/2`:

* `f4_hc`: `52·(-5/2)/(-5/2+9) = -20 = -2(9+1)`;
* `f4_casimir_match`: `casPoly = ½ Q`; here `κ⁻¹ᵢⱼ = coef(dlᵢ, j)/Dᵢ` (`kappaInv_eq`) and the sparse
  identity `2 casPoly = Q` is a kernel `quadZero` check (`casList_ok`);
* `sym_rel_zero`: the highest relation `P₀` from the singular vector `f4sv` (`sym_singular`, two
  integer shadow checks);
* `sym_rel`: all 324 relations along `f4Steps` (`sym_step`; `adG` is `adPolyT`);
* `f4_vacuumQuarticRelation`, `f4_targetLowerBound`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.F4Lie

open MvPolynomial VOA VOA.AffineGeneral VOA.AffineGeneral.SCLie VOA.DeligneAudit.VacuumRelation
  VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
  VOA.DeligneAudit.DeligneSector.F4

noncomputable section

/-- The square-bracket current data of `L_{-5/2}(𝔣₄)`. -/
abbrev F4C : SqCurrentData f4W (Fin 52) := affineCurrentData f4CertData (-5/2) f4_level_ne

theorem f4_hc : ((F4data.n : ℕ) : ℂ) * (-5/2) / (-5/2 + f4CertData.h) =
    -2 * (((9 : ℕ) : ℂ) + 1) := by
  rw [f4CertData_h]
  change ((52 : ℕ) : ℂ) * (-5/2) / (-5/2 + 9) = _
  norm_num

/-! ## The Casimir -/

theorem kappaInv_eq (a c : Fin 52) :
    f4CertData.kappaInv a c = (f4D a : ℂ)⁻¹ * (coef (f4dl a) c : ℂ) := by
  change (Pi.basisFun ℂ (Fin 52)).repr (dualV f4Checks f4dl f4D a) c = _
  rw [Pi.basisFun_repr]
  rfl

/-- `2 / Dᵢ`. -/
def eD (i : ℕ) : ℤ := 2 / f4D i

theorem eD_mul : ∀ i : Fin 52, eD i * f4D i = 2 := by decide +kernel

theorem f4D_inv (i : Fin 52) : (f4D i : ℂ)⁻¹ = (1 / 2 : ℂ) * (eD i : ℂ) := by
  have h : ((eD i : ℤ) : ℂ) * (f4D i : ℂ) = 2 := by exact_mod_cast eD_mul i
  exact inv_eq_of_mul_eq_one_right (by linear_combination h / 2)

theorem row_gen (i : Fin 52) (d : ℂ) (l : List (ℕ × ℤ)) :
    ∑ j : Fin 52, MvPolynomial.C (d * (coef l j : ℂ)) * (X i * X j) =
      MvPolynomial.C d * (l.map fun t => ((t.2 : ℤ) : MvPolynomial (Fin 52) ℂ) *
        (X i * Xn 52 t.1)).sum := by
  induction l with
  | nil => simp
  | cons t l ih =>
      have hsplit : ∀ j : Fin 52, MvPolynomial.C (d * (coef (t :: l) j : ℂ)) * (X i * X j) =
          MvPolynomial.C (d * ((if t.1 = (j : ℕ) then t.2 else 0 : ℤ) : ℂ)) * (X i * X j) +
            MvPolynomial.C (d * (coef l j : ℂ)) * (X i * X j) := by
        intro j
        rw [coef_cons, Int.cast_add, mul_add, map_add, add_mul]
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib, ih, List.map_cons,
        List.sum_cons, mul_add]
      congr 1
      by_cases ht : t.1 < 52
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

/-- The rows of `2 casPoly` as a sparse quadratic list. -/
def casList : List (ℕ × ℕ × ℤ) :=
  (List.finRange 52).flatMap fun (i : Fin 52) => (f4dl i).map fun t => (i.val, t.1, eD i * t.2)

theorem casList_ok : quadZero (casList ++ scaleQ (-1) qQ) = true := by decide +kernel

theorem row_eq (i : Fin 52) :
    ∑ j, MvPolynomial.C (f4CertData.kappaInv i j) * (X i * X j) =
      MvPolynomial.C (1 / 2 : ℂ) *
        quadP 52 ((f4dl i).map fun t => (i.val, t.1, eD i * t.2)) := by
  simp only [kappaInv_eq, f4D_inv]
  rw [row_gen i (1 / 2 * (eD i : ℂ)), map_mul, mul_assoc]
  congr 1
  simp only [quadP, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  have hi : Xn 52 (i : ℕ) = X i := by simp [Xn]
  simp only [Function.comp_apply, hi]
  push_cast
  rw [map_intCast]
  ring

theorem casimir_match' :
    (∑ i, ∑ j, MvPolynomial.C (f4CertData.kappaInv i j) * (X i * X j)) =
      MvPolynomial.C (1 / 2 : ℂ) * quadraticRelation cas := by
  simp only [row_eq]
  rw [← Finset.mul_sum, cas_poly, ← quadP_eq]
  congr 1
  have h0 := quadP_eq_zero_of_quadZero (n := 52) (by norm_num) _ casList_ok
  rw [quadP_append', quadP_scaleQ] at h0
  have hg : quadP 52 casList = quadP 52 qQ := by
    push_cast at h0
    linear_combination h0
  rw [← hg, casList, quadP_flatMap', ← List.sum_ofFn, List.ofFn_eq_map]

/-- **The Casimir match**: `casPoly = ½ · Q`. -/
theorem f4_casimir_match :
    (affineCurrentData (ι := Fin F4data.n) f4CertData (-5/2) f4_level_ne).casPoly =
      MvPolynomial.C (1 / 2 : ℂ) * F4data.Q :=
  casimir_match'

/-! ## The relation symbols -/

/-- The singular vector `P₀ = -X₈² + 4X₁₉X₃₀ + 4X₂₁X₃₄ + 4X₂₅X₄₂`: coefficients and indices. -/
def cz : Fin 4 → ℤ := ![-1, 4, 4, 4]
def ta : Fin 4 → Fin 52 := ![8, 19, 21, 25]
def tb : Fin 4 → Fin 52 := ![8, 30, 34, 42]

/-- Integer bracket shadow of `P₀`. -/
theorem hw_bracket_shadowZ : ∀ e : Fin 52, ∑ s, cz s * f4scZ (ta s) (tb s) e = 0 := by
  decide +kernel

/-- Integer form shadow of `P₀`. -/
theorem hw_form_shadowZ : ∑ s, cz s * f4fZ (ta s) (tb s) = 0 := by decide +kernel

theorem sym_hw : F4C.sym (∑ s, (cz s : ℂ) • (X (ta s) * X (tb s))) = 0 := by
  refine sym_singular f4CertData (-5/2) f4_level_ne (fun s => (cz s : ℂ)) ta tb ?_ ?_ ?_
  · have h := f4sv_proj
    rw [f4sv, quadState] at h
    simpa [termsZC, f4svTerms, Fin.sum_univ_four, cz, ta, tb, add_assoc] using h
  · intro e
    have h := hw_bracket_shadowZ e
    simp only [f4scZ] at h
    simp only [f4CertData_sc]
    exact_mod_cast h
  · have h := hw_form_shadowZ
    simp only [f4fZ] at h
    simp only [f4CertData_form]
    exact_mod_cast h

theorem sym_rel_zero : F4C.sym (quadP 52 (relQ 0)) = 0 := by
  have he : quadP 52 (relQ 0) = ∑ s, (cz s : ℂ) • (X (ta s) * X (tb s)) := by
    rw [relQ_zero]
    simp only [quadP, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Fin.sum_univ_four, cz, ta, tb, Xn]
    simp [MvPolynomial.smul_eq_C_mul, map_ofNat]
    ring_nf
  rw [he]
  exact sym_hw

theorem sym_step' (st : ℕ × ℕ × ℕ) (h : stepOK st = true)
    (hj : F4C.sym (quadP 52 (relQ st.2.1)) = 0) : F4C.sym (quadP 52 (relQ st.2.2)) = 0 := by
  obtain ⟨g, j, k⟩ := st
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hg, hjk⟩, hk⟩, hz⟩ := h
  have h0 := quadP_eq_zero_of_quadZero (n := 52) (by norm_num) _ hz
  rw [quadP_append', quadP_scaleQ] at h0
  have heq : quadP 52 (relQ k) = quadP 52 (adS f4T g (relQ j)) := by
    push_cast at h0
    linear_combination -h0
  have had := adPoly_quadP ⟨g, hg⟩ _ (relQ_qInRange j (by omega))
  refine sym_step f4CertData (-5/2) f4_level_ne (b := ⟨g, hg⟩) (p := 1) (q := 1) one_ne_zero
    ?_ hj
  rw [one_smul, one_smul, heq, ← had]
  rfl

theorem sym_rel_lt : ∀ k, k < 324 → F4C.sym (quadP 52 (relQ k)) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact sym_rel_zero
    · have hmem : k ∈ f4Steps.map (·.2.2) := by
        rw [f4Steps_targets, List.mem_range']; exact ⟨k - 1, by omega, by omega⟩
      obtain ⟨st, hst, hst2⟩ := List.mem_map.mp hmem
      have hok := List.all_eq_true.mp f4Steps_ok st hst
      have hlt : st.2.1 < st.2.2 := by
        simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1.1.2
      rw [← hst2]
      exact sym_step' st hok (ih _ (by omega) (by omega))

/-- **The relation symbols of `F4data`** (the `hrel` for `F₄`). -/
theorem f4_hrel (r : Fin 324) :
    (affineCurrentData (ι := Fin F4data.n) f4CertData (-5/2) f4_level_ne).sym
      (quadraticRelation (F4data.rel r)) = 0 := by
  have e1 : quadraticRelation (F4data.rel r) = quadP 52 (relQ r) := by
    rw [quadP_eq]; exact rel_poly r
  exact (congrArg F4C.sym e1).trans (sym_rel_lt r r.2)

/-- **The vacuum quartic relation of `L_{-5/2}(𝔣₄)`.** -/
theorem f4_vacuumQuarticRelation :
    DeligneMLDE.VacuumQuarticRelation f4W
      (5 / 4 * f4W.centralCharge ^ 2 + 11 / 2 * f4W.centralCharge) :=
  vacuumQuarticRelation_of_carrierData F4data f4CertData (-5/2) f4_level_ne (1 / 2)
    f4_casimir_match f4_hrel

theorem f4W_centralCharge : f4W.centralCharge = -2 * (((9 : ℕ) : ℂ) + 1) := by
  rw [simple_centralCharge', Fintype.card_fin]
  exact f4_hc

theorem f4W_vacuum_ne_zero : f4W.vacuum ≠ 0 := simple_vacuum_ne_zero' _ _ _

/-- **The `F₄` target lower bound** `dim (L_{-5/2}(𝔣₄))_N ≥ mldeCoeff 9 N`, unconditional. -/
theorem f4_targetLowerBound :
    DeligneCharacter.TargetLowerBoundQ f4W (DeligneCharacter.mldeCoeff 9) :=
  targetLowerBound_of_carrierData F4data f4CertData (-5/2) f4_level_ne 9 f4_hc (1 / 2)
    f4_casimir_match f4_hrel

end

end VOA.DeligneAudit.F4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.F4Lie.f4_casimir_match
#print axioms VOA.DeligneAudit.F4Lie.f4_hrel
#print axioms VOA.DeligneAudit.F4Lie.f4_vacuumQuarticRelation
#print axioms VOA.DeligneAudit.F4Lie.f4_targetLowerBound
end AxiomAudit
