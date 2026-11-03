/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6Presentation
import VOA.DeligneAudit.E6VacuumChecks
import VOA.DeligneAudit.DeligneVacuumRelationCarrier

/-!
# `E₆`: the relation symbols, the vacuum quartic relation and the target bound

the `targetLowerBound_of_carrierData` for `W6 = L_{-3}(𝔢₆)` (`e6LieData`, the carrier basis of `E6data`),
following the `E7LieVacuum`:

* `e6_hc`: `78·(-3)/(-3+12) = -2(12+1)`;
* **`e6_casimir_match`**: the Sugawara quadric `Σ κ⁻¹ᵢⱼ XᵢXⱼ` is `(2/3) Q` (`e6cas_check`);
* relation `0`: `sym_singular` from the singular vector `e6hw` (`e6hw_mem`) and the two shadows;
* the other 649 relations: the `sym_step` along E3's chain `e6steps` (single-term stability certificates);
* **`e6_hrel`** and **`e6_targetLowerBound : TargetLowerBoundQ W6 (mldeCoeff 12)`**, unconditional.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA VOA.AffineGeneral VOA.AffineGeneral.SCLie VOA.DeligneAudit.VacuumRelation
  VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse

noncomputable section

/-- The square-bracket current data of `L_{-3}(𝔢₆)`. -/
abbrev E6cd : SqCurrentData W6 (Fin 78) := affineCurrentData e6LieData k6 hk6

theorem e6_hc : ((E6data.n : ℕ) : ℂ) * k6 / (k6 + e6LieData.h) = -2 * (((12 : ℕ) : ℂ) + 1) := by
  rw [e6LieData_h]
  show ((78 : ℕ) : ℂ) * ((-3 : ℤ) : ℂ) / (((-3 : ℤ) : ℂ) + 12) = _
  norm_num

/-! ## The Casimir match -/

theorem e6_kappaInv (a b : Fin 78) :
    e6LieData.kappaInv a b = (e6D a : ℂ)⁻¹ * (coef (e6dl a) b : ℂ) := by
  show (basis e6Checks).repr (dualV e6Checks e6dl e6D a) b = _
  rw [basis_repr_apply]
  rfl

/-- One row: `Σⱼ C(s · lⱼ) XᵢXⱼ = C s · quadP (i, l)`. -/
theorem e6vac_row_sum (i : Fin 78) (s : ℂ) (l : List (ℕ × ℤ)) (hl : inRange 78 l = true) :
    ∑ j : Fin 78, MvPolynomial.C (s * (coef l j : ℂ)) * (X i * X j) =
      MvPolynomial.C s * quadP 78 (l.map fun p => ((i : ℕ), p.1, p.2)) := by
  induction l with
  | nil => simp [quadP]
  | cons p l ih =>
    simp only [inRange, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    have ih := ih hl.2
    have hp : p.1 < 78 := hl.1
    simp only [coef_cons, Int.cast_add, mul_add, map_add, add_mul, Finset.sum_add_distrib, ih]
    have h1 : ∑ j : Fin 78, MvPolynomial.C (s * (((if p.1 = (j : ℕ) then p.2 else 0 : ℤ)) : ℂ)) * (X i * X j) =
        MvPolynomial.C (s * p.2) * (X i * X ⟨p.1, hp⟩) := by
      rw [Finset.sum_eq_single ⟨p.1, hp⟩]
      · simp
      · intro j _ hj
        rw [if_neg (fun h => hj (Fin.ext h.symm))]; simp
      · simp
    rw [h1]
    simp only [quadP, List.map_cons, List.sum_cons, Xn, dif_pos hp, dif_pos i.2, map_mul, map_intCast]
    ring

theorem e6_casPoly_three : (3 : MvPolynomial (Fin 78) ℂ) * E6cd.casPoly = quadP 78 e6casList := by
  have hdvd := e6D_dvd
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true, decide_eq_true_eq] at hdvd
  show (3 : MvPolynomial (Fin 78) ℂ) * ∑ i, ∑ j, MvPolynomial.C (e6LieData.kappaInv i j) * (X i * X j) = _
  rw [e6casList, quadP_flatMap', ← List.sum_ofFn, List.ofFn_eq_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [e6_kappaInv]
  rw [e6vac_row_sum i _ _ (hdvd i).2, e6casRow, quadP_scaleQ, ← mul_assoc]
  congr 1
  have hD : ((e6D i : ℤ) : ℂ) * ((3 / e6D i : ℤ) : ℂ) = 3 := by exact_mod_cast (hdvd i).1
  have hD0 : ((e6D i : ℤ) : ℂ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hD; norm_num at hD
  rw [← map_intCast (MvPolynomial.C (σ := Fin 78) (R := ℂ)), ← map_ofNat (MvPolynomial.C (σ := Fin 78) (R := ℂ)) 3,
    ← map_mul]
  congr 1
  field_simp
  linear_combination (-1 : ℂ) * hD

/-- The Casimir match in the sparse form. -/
theorem e6_casimir_match' : E6cd.casPoly = MvPolynomial.C (σ := Fin 78) (2 / 3 : ℂ) * quadP 78 qQ := by
  have h0 := quadP_eq_zero_of_quadZero (n := 78) (by norm_num) _ e6cas_check
  rw [quadP_append', quadP_scaleQ, ← e6_casPoly_three] at h0
  have h3 : (3 : MvPolynomial (Fin 78) ℂ) = MvPolynomial.C 3 := (map_ofNat _ 3).symm
  have h2 : ((-2 : ℤ) : MvPolynomial (Fin 78) ℂ) = MvPolynomial.C ((-2 : ℤ) : ℂ) := (map_intCast _ _).symm
  rw [h3, h2] at h0
  have hC1 : MvPolynomial.C (1 / 3 : ℂ) * MvPolynomial.C (3 : ℂ) = (1 : MvPolynomial (Fin 78) ℂ) := by
    rw [← map_mul]; norm_num
  have hC2 : MvPolynomial.C (σ := Fin 78) (1 / 3 : ℂ) * MvPolynomial.C ((-2 : ℤ) : ℂ) =
      -MvPolynomial.C (2 / 3 : ℂ) := by
    rw [← map_mul, ← map_neg]; norm_num
  linear_combination MvPolynomial.C (1 / 3 : ℂ) * h0 - E6cd.casPoly * hC1 - quadP 78 qQ * hC2

/-- **The Casimir match**: `casPoly = (2/3) · Q`. -/
theorem e6_casimir_match : E6cd.casPoly = MvPolynomial.C (2 / 3 : ℂ) * E6data.Q :=
  e6_casimir_match'.trans (congrArg (MvPolynomial.C (2 / 3 : ℂ) * ·) quadraticRelation_cas.symm)

/-! ## The relation symbols -/

theorem e6_formTable (a b : Fin 78) :
    e6LieData.formTable a b = (formV e6Gm [((a : ℕ), 1)] [((b : ℕ), 1)] : ℂ) :=
  ld_form e6Checks e6Gm e6_gInRange e6_symm e6Skew_all e6dl e6D e6_pair 3 24 (by norm_num) e6_cas a b

/-- The singular vector as a `Fin 4`-indexed family. -/
def e6vac_hwc : Fin 4 → ℂ := ![1, 1, -1, 1]
def e6vac_hwa : Fin 4 → Fin 78 := ![29, 32, 35, 37]
def e6vac_hwb : Fin 4 → Fin 78 := ![41, 40, 39, 38]

theorem e6vac_hw_sum_eq : (∑ s, e6vac_hwc s • J e6LieData k6 (e6vac_hwa s) (-1) (J e6LieData k6 (e6vac_hwb s) (-1) (vacuumA e6LieData k6)))
    = quadState e6LieData k6 (termsC e6hw) := by
  simp [Fin.sum_univ_four, e6vac_hwc, e6vac_hwa, e6vac_hwb, quadState, termsC, e6hw]
  abel

theorem e6_sym_hw : E6cd.sym (∑ s, e6vac_hwc s • (X (e6vac_hwa s) * X (e6vac_hwb s))) = 0 := by
  refine sym_singular e6LieData k6 hk6 e6vac_hwc e6vac_hwa e6vac_hwb ?_ ?_ ?_
  · rw [e6vac_hw_sum_eq]
    exact (Submodule.Quotient.mk_eq_zero _).mpr e6hw_mem
  · intro e
    have h := List.all_eq_true.mp e6hw_bracket_shadow e (List.mem_range.mpr e.2)
    simp only [beq_iff_eq] at h
    simp only [Fin.sum_univ_four, e6vac_hwc, e6vac_hwa, e6vac_hwb, Matrix.cons_val, ← fE6_eq_structureConstant]
    simp only [fE6, scF, sc, show ((29 : Fin 78) : ℕ) = 29 from rfl, show ((41 : Fin 78) : ℕ) = 41 from rfl,
      show ((32 : Fin 78) : ℕ) = 32 from rfl, show ((40 : Fin 78) : ℕ) = 40 from rfl,
      show ((35 : Fin 78) : ℕ) = 35 from rfl, show ((39 : Fin 78) : ℕ) = 39 from rfl,
      show ((37 : Fin 78) : ℕ) = 37 from rfl, show ((38 : Fin 78) : ℕ) = 38 from rfl]
    have h' : ((coef (entry e6T 29 41) e + coef (entry e6T 32 40) e - coef (entry e6T 35 39) e
      + coef (entry e6T 37 38) e : ℤ) : ℂ) = 0 := by exact_mod_cast h
    push_cast at h'
    linear_combination h'
  · have h := e6hw_form_shadow
    simp only [Fin.sum_univ_four, e6vac_hwc, e6vac_hwa, e6vac_hwb, Matrix.cons_val]
    simp only [e6_formTable, show ((29 : Fin 78) : ℕ) = 29 from rfl, show ((41 : Fin 78) : ℕ) = 41 from rfl,
      show ((32 : Fin 78) : ℕ) = 32 from rfl, show ((40 : Fin 78) : ℕ) = 40 from rfl,
      show ((35 : Fin 78) : ℕ) = 35 from rfl, show ((39 : Fin 78) : ℕ) = 39 from rfl,
      show ((37 : Fin 78) : ℕ) = 37 from rfl, show ((38 : Fin 78) : ℕ) = 38 from rfl]
    have h' : ((formV e6Gm [(29, 1)] [(41, 1)] + formV e6Gm [(32, 1)] [(40, 1)]
      - formV e6Gm [(35, 1)] [(39, 1)] + formV e6Gm [(37, 1)] [(38, 1)] : ℤ) : ℂ) = 0 := by exact_mod_cast h
    push_cast at h'
    norm_num
    linear_combination h'

theorem e6vac_quadP_Pq_zero : quadP 78 (Pq 0) = (-1 : ℂ) • (∑ s, e6vac_hwc s • (X (e6vac_hwa s) * X (e6vac_hwb s))) := by
  rw [Pq, if_pos (by norm_num), e6pres_relQ_zero]
  simp [quadP, Fin.sum_univ_four, e6vac_hwc, e6vac_hwa, e6vac_hwb, Xn, MvPolynomial.smul_eq_C_mul]
  ring

theorem e6_sym_rel0 : E6cd.sym (quadP 78 (Pq 0)) = 0 :=
  (congrArg E6cd.sym e6vac_quadP_Pq_zero).trans
    ((sym_smul' e6LieData k6 hk6 (-1) _).trans (by rw [e6_sym_hw, smul_zero]))

/-- One propagation step for the relation symbols. -/
theorem e6_sym_step (known : List ℕ) (hk : ∀ t ∈ known, E6cd.sym (quadP 78 (Pq t)) = 0) (st : ℕ × ℕ × ℕ)
    (h : stepOK known st = true) : E6cd.sym (quadP 78 (Pq st.2.2)) = 0 := by
  obtain ⟨g, r, s⟩ := st
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hg1, hg2⟩, hrk⟩, hr⟩, hp⟩, hl⟩, -⟩ := h
  set l := ((rowPairs g r).headD (0, 0)).1
  have hg : g < 78 := by omega
  have hrow := e6pres_stabOf_row g r ⟨hg1, hg2⟩ hr
  have e := e6pres_stab_single g r _ hrow l s hp
  have hq : qInRange 78 (Pq r) = true := List.all_eq_true.mp Pq_inRange r (List.mem_range.mpr hr)
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hstep : ((certL ((stabOf g).getD r []) : ℤ) : ℂ) •
      adG e6LieData.structureConstant ⟨g, hg⟩ (quadP 78 (Pq r)) = (l : ℂ) • quadP 78 (Pq s) := by
    have ha : adG e6LieData.structureConstant ⟨g, hg⟩ (quadP 78 (Pq r)) = quadP 78 (adS e6T g (Pq r)) :=
      e6pres_adPoly_quadP ⟨g, hg⟩ (Pq r) hq
    rw [ha, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_intCast, map_intCast]
    exact e
  exact sym_step e6LieData k6 hk6 hl' hstep (hk r hrk)

theorem e6_sym_chain : ∀ (steps : List (ℕ × ℕ × ℕ)) (known : List ℕ),
    (∀ t ∈ known, E6cd.sym (quadP 78 (Pq t)) = 0) → propOK known steps = true →
      ∀ t ∈ known ++ steps.map (·.2.2), E6cd.sym (quadP 78 (Pq t)) = 0 := by
  intro steps
  induction steps with
  | nil => intro known hk _ t ht; simpa using hk t (by simpa using ht)
  | cons st rest ih =>
    intro known hk h t ht
    simp only [propOK, Bool.and_eq_true] at h
    have hs := e6_sym_step known hk st h.1
    have hk' : ∀ t ∈ st.2.2 :: known, E6cd.sym (quadP 78 (Pq t)) = 0 := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hs
      · exact hk t ht
    apply ih _ hk' h.2
    simp only [List.map_cons, List.mem_append, List.mem_cons] at ht ⊢
    tauto

/-- **The relation symbols of `E6data`**, the `hrel` for `E₆`. -/
theorem e6_hrel (r : Fin 650) : E6cd.sym (quadraticRelation (E6data.rel r)) = 0 := by
  have hall := List.contains_iff_mem.mp (List.all_eq_true.mp e6steps_all r (List.mem_range.mpr r.2))
  have h0 : ∀ t ∈ [0], E6cd.sym (quadP 78 (Pq t)) = 0 := by
    intro t ht; rw [List.mem_singleton.mp ht]; exact e6_sym_rel0
  have hc := e6_sym_chain e6steps [0] h0 e6steps_ok r hall
  have e1 : quadraticRelation (E6data.rel r) = quadP 78 (Pq r) :=
    (quadraticRelation_rel r).trans (by rw [Pq, if_pos r.2])
  exact (congrArg E6cd.sym e1).trans hc

/-- **The `E₆` target lower bound** `dim (L_{-3}(𝔢₆))_N ≥ mldeCoeff 12 N`, unconditional. -/
theorem e6_targetLowerBound : DeligneCharacter.TargetLowerBoundQ W6 (DeligneCharacter.mldeCoeff 12) :=
  targetLowerBound_of_carrierData E6data e6LieData k6 hk6 12 e6_hc (2 / 3) e6_casimir_match e6_hrel

end

end VOA.DeligneAudit.DeligneCarrier.E6

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.e6_casimir_match
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.e6_hrel
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.e6_targetLowerBound
end AxiomAudit
