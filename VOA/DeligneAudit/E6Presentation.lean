/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorStable
import VOA.DeligneAudit.E6PresChecks
import VOA.DeligneAudit.E6SingChecks
import VOA.AffineGeneral.E6LieData
import VOA.AffineGeneral.SCSingular
import VOA.AffineGeneral.LiPresentation
import VOA.DeligneAudit.A2CarrierUpperBound
import VOA.AffineGeneral.DeligneInstance

/-!
# The explicit E₆ presentation: `I₂ⁿˢ` lies in the `C₂` kernel of `L_{-3}(𝔢₆)`

`W6 = simpleVOA e6LieData (-3)` (`L_{-3}(𝔢₆)`, currents in the carrier basis of `E6data`), `cl6` its
current-coordinate map into Li degree zero.  The A₂ method:

1. `cl6_rel_zero`: the highest relation `P₀ = -(X₂₉X₄₁ + X₃₂X₄₀ - X₃₅X₃₉ + X₃₇X₃₈)` is in the kernel: its state is the
   weight-two singular vector `e6hw` (`e6hw_q1`, `e6hw_q2` + `ld_quadState_mem_maxIdeal`), which dies in `L_{-3}`.
   No `C₂` correction is needed (the four pairs commute).
2. `cl6_step`: the kernel is stable under the coadjoint derivations (`clsG_adPoly_eq_zero`), and the stability
   certificates of `E6SectorStab42..47` give single-term identities `L · ad(g) P_r = λ P_s`.
3. `cl6_rel`: the 649-step chain `e6steps` (`e6steps_ok`, `e6steps_all`) reaches all 650 relations.
4. **`E6.I2ns_le_ker`**, **`E6.explicitPresentation`** (`ideal := E6data.I`) and
   **`E6.geometricCarrierEmbedding`** via `geometricCarrierEmbedding_of_quadraticIdeal`.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop
open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.CarrierEmbedding

noncomputable section

/-- The level `-3`. -/
abbrev k6 : ℂ := ((-3 : ℤ) : ℂ)

theorem hk6 : k6 + e6LieData.h ≠ 0 := by rw [e6LieData_h]; norm_num

/-- **`L_{-3}(𝔢₆)`.** -/
abbrev W6 := simpleVOA e6LieData k6 hk6

/-- The current-coordinate map of `L_{-3}(𝔢₆)` into Li degree zero. -/
abbrev cl6 := clsG W6 (genS e6LieData k6 hk6) (genS_weight_one e6LieData k6 hk6)

theorem fE6_eq_structureConstant : fE6 = e6LieData.structureConstant := by
  funext x y c
  exact (ld_sc e6Checks e6Gm e6_gInRange e6_symm e6Skew_all e6dl e6D e6_pair 3 24 (by norm_num) e6_cas x y c).symm

theorem e6pres_adPoly_quadP (x : Fin 78) (l : List (ℕ × ℕ × ℤ)) (hl : qInRange 78 l = true) :
    adPolyT e6LieData.structureConstant x (quadP 78 l) = quadP 78 (adS e6T x l) := by
  rw [← fE6_eq_structureConstant]
  exact adDer_quadP e6_bound x l hl

/-! ## The highest relation -/

theorem e6pres_relQ_zero : relQ 0 = [(29, 41, -1), (32, 40, -1), (35, 39, 1), (37, 38, -1)] := by decide +kernel

theorem e6pres_quadP_Pq_zero : quadP 78 (Pq 0) = -quadPoly (termsC e6hw) := by
  rw [Pq, if_pos (by norm_num), e6pres_relQ_zero]
  simp [quadP, quadPoly, termsC, e6hw, Xn, MvPolynomial.smul_eq_C_mul]
  ring

theorem e6hw_mem : quadState e6LieData k6 (termsC e6hw) ∈ maxIdeal e6LieData k6 hk6 :=
  ld_quadState_mem_maxIdeal e6Checks e6Gm e6_gInRange e6_symm e6Skew_all e6dl e6D e6_pair 3 24 (by norm_num)
    e6_cas (-3) hk6 e6hw e6hw_q1 e6hw_q2

theorem cl6_rel_zero : cl6 (quadP 78 (Pq 0)) = 0 := by
  rw [e6pres_quadP_Pq_zero, map_neg, clsG_quad_eq_zero e6LieData k6 hk6 _ e6hw_mem, neg_zero]

/-! ## Propagation -/

theorem e6pres_stab_single (g r : ℕ) (c : List ℕ) (h : stabRowOK g r c = true) (l : ℤ) (s : ℕ)
    (hp : pairsOf c.tail = [(l, s)]) :
    (certL c : MvPolynomial (Fin 78) ℂ) * quadP 78 (adS e6T g (Pq r)) = (l : MvPolynomial (Fin 78) ℂ) * quadP 78 (Pq s) := by
  simp only [stabRowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have h0 := quadP_eq_zero_of_quadZero (n := 78) (by norm_num) _ h.2
  rw [quadP_append', quadP_scaleQ, negQ, quadP_scaleQ, quadP_flatMap', hp] at h0
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, quadP_scaleQ] at h0
  push_cast at h0 ⊢
  linear_combination h0

theorem e6pres_stabOf_row (g r : ℕ) (hg : 42 ≤ g ∧ g ≤ 47) (hr : r < 651) :
    stabRowOK g r ((stabOf g).getD r []) = true := by
  have key : ∀ rows : List (List ℕ), stabOK g rows = true → stabRowOK g r (rows.getD r []) = true := by
    intro rows h
    simp only [stabOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.all_eq_true.mp h.2 r (List.mem_range.mpr hr)
  obtain ⟨h1, h2⟩ := hg
  interval_cases g
  exacts [key _ stab42_ok, key _ stab43_ok, key _ stab44_ok, key _ stab45_ok, key _ stab46_ok, key _ stab47_ok]

theorem cl6_step (known : List ℕ) (hk : ∀ t ∈ known, cl6 (quadP 78 (Pq t)) = 0) (st : ℕ × ℕ × ℕ)
    (h : stepOK known st = true) : cl6 (quadP 78 (Pq st.2.2)) = 0 := by
  obtain ⟨g, r, s⟩ := st
  simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hg1, hg2⟩, hrk⟩, hr⟩, hp⟩, hl⟩, -⟩ := h
  set l := ((rowPairs g r).headD (0, 0)).1
  have hg : g < 78 := by omega
  have hrow := e6pres_stabOf_row g r ⟨hg1, hg2⟩ hr
  have e := e6pres_stab_single g r _ hrow l s hp
  have had := clsG_adPoly_eq_zero e6LieData k6 hk6 ⟨g, hg⟩ (hk r hrk)
  have hq : qInRange 78 (Pq r) = true := List.all_eq_true.mp Pq_inRange r (List.mem_range.mpr hr)
  have had2 : cl6 (quadP 78 (adS e6T g (Pq r))) = 0 :=
    (congrArg cl6 (e6pres_adPoly_quadP ⟨g, hg⟩ (Pq r) hq).symm).trans had
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  -- `cl6 (l * P_s) = cl6 (L * ad P_r) = cl6 L * 0`
  have h3 : cl6 ((l : MvPolynomial (Fin 78) ℂ) * quadP 78 (Pq s)) = 0 :=
    (congrArg cl6 e.symm).trans ((map_mul cl6 _ _).trans
      ((congrArg (cl6 (certL ((stabOf g).getD r []) : MvPolynomial (Fin 78) ℂ) * ·) had2).trans (mul_zero _)))
  have hB : quadP 78 (Pq s) =
      MvPolynomial.C ((l : ℂ)⁻¹) * ((l : MvPolynomial (Fin 78) ℂ) * quadP 78 (Pq s)) := by
    rw [← mul_assoc, ← map_intCast (MvPolynomial.C (σ := Fin 78) (R := ℂ)) l, ← map_mul, inv_mul_cancel₀ hl',
      map_one, one_mul]
  exact (congrArg cl6 hB).trans ((map_mul cl6 _ _).trans
    ((congrArg (cl6 (MvPolynomial.C ((l : ℂ)⁻¹)) * ·) h3).trans (mul_zero _)))

theorem cl6_chain : ∀ (steps : List (ℕ × ℕ × ℕ)) (known : List ℕ),
    (∀ t ∈ known, cl6 (quadP 78 (Pq t)) = 0) → propOK known steps = true →
      ∀ t ∈ known ++ steps.map (·.2.2), cl6 (quadP 78 (Pq t)) = 0 := by
  intro steps
  induction steps with
  | nil => intro known hk _ t ht; simpa using hk t (by simpa using ht)
  | cons st rest ih =>
    intro known hk h t ht
    simp only [propOK, Bool.and_eq_true] at h
    have hs := cl6_step known hk st h.1
    have hk' : ∀ t ∈ st.2.2 :: known, cl6 (quadP 78 (Pq t)) = 0 := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hs
      · exact hk t ht
    apply ih _ hk' h.2
    simp only [List.map_cons, List.mem_append, List.mem_cons] at ht ⊢
    tauto

theorem cl6_rel (r : Fin 650) : cl6 (quadraticRelation (E6data.rel r)) = 0 := by
  have hall := List.contains_iff_mem.mp (List.all_eq_true.mp e6steps_all r (List.mem_range.mpr r.2))
  have h0 : ∀ t ∈ [0], cl6 (quadP 78 (Pq t)) = 0 := by
    intro t ht; rw [List.mem_singleton.mp ht]; exact cl6_rel_zero
  have hc := cl6_chain e6steps [0] h0 e6steps_ok r hall
  have e1 : quadraticRelation (E6data.rel r) = quadP 78 (Pq r) :=
    (quadraticRelation_rel r).trans (by rw [Pq, if_pos r.2])
  exact (congrArg cl6 e1).trans hc

/-! ## The ideal and the presentation -/

/-- **`I₂ⁿˢ` is contained in the `C₂` kernel of `L_{-3}(𝔢₆)`.** -/
theorem I2ns_le_ker : E6data.I ≤ RingHom.ker
    (MvPolynomial.aeval fun i =>
      liDegreeZeroClass W6 1 ⟨genS e6LieData k6 hk6 i, genS_weight_one e6LieData k6 hk6 i⟩).toRingHom := by
  rw [DeligneCarrierData.I, quadraticIdeal, Ideal.span_le]
  rintro _ ⟨r, rfl⟩
  exact cl6_rel r

/-- **The explicit E₆ presentation**: currents `J^a_{-1}|0⟩` of `L_{-3}(𝔢₆)` (carrier basis), ideal `I₂ⁿˢ`. -/
def explicitPresentation : CurrentC2Presentation .E6 W6 where
  gen := genS e6LieData k6 hk6
  gen_weight_one := genS_weight_one e6LieData k6 hk6
  ideal := E6data.I
  relations := I2ns_le_ker

theorem explicitPresentation_ideal : explicitPresentation.ideal = quadraticIdeal E6data.rel := rfl

/-- **The geometric carrier embedding** for the explicit E₆ presentation. -/
def geometricCarrierEmbedding : GeometricCarrierEmbedding .E6 W6 explicitPresentation (Carrier E6data.rel) :=
  geometricCarrierEmbedding_of_quadraticIdeal explicitPresentation E6data.rel rfl

/-- **`CurrentJetSurjectivity` for the explicit E₆ presentation** (the current-word spanning of the general
`L_k(𝔤)` does not look at the ideal). -/
theorem explicitCurrentJetSurjectivity : CurrentJetSurjectivity .E6 W6 explicitPresentation :=
  DeligneAudit.currentJetSurjectivity_of_genWordSpan explicitPresentation
    (VOA.AffineGeneral.Deligne.genWordsSpan .E6 e6LieData k6 hk6)

/-- **The E₆ Deligne case with the explicit ideal `I₂ⁿˢ`**, conditional only on the quadratic carrier upper bound.
It also gives `ker = I₂ⁿˢ`. -/
theorem classicallyFree_of_upperBound (hbound : QuadraticCarrierUpperBound E6data.rel W6) :
    CaseClassicallyFree .E6 W6 explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W6 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  caseClassicallyFree_of_quadraticCarrierUpperBound explicitPresentation E6data.rel rfl
    explicitCurrentJetSurjectivity hbound

end

end VOA.DeligneAudit.DeligneCarrier.E6

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.cl6_rel_zero
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.I2ns_le_ker
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.geometricCarrierEmbedding
#print axioms VOA.DeligneAudit.DeligneCarrier.E6.classicallyFree_of_upperBound
end AxiomAudit
