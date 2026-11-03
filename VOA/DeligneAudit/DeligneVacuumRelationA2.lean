/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneVacuumRelation
import VOA.DeligneAudit.DeligneMLDEA2
import VOA.DeligneAudit.A2RelationsPresentation
import VOA.DeligneAudit.A2CarrierCasimir

/-!
# A₂: the vacuum quartic relation `S(L[-2]²|0⟩) = 36·G₄⋆S(|0⟩)` (residual 1 of the MLDE route, discharged)

For `W = L_{-3/2}(sl₃)` the generic reduction `vacuumQuarticRelation_of_symbols` applies to the
eight Chevalley currents (`a2CurrentData`).  Its only input is that the cubic square symbols
`X_a · Σ K_{bc} X_b X_c` vanish in `V ⧸ currentC2`.  This follows from

* The `X_mul_casimir_eq` (`X_a · casimir ∈ I₂ⁿˢ`, with `Σ K_{bc} X_b X_c = casimir/3`);
* the highest relation: `sym (relationPoly 2) = 0`, because the square version of Perše's singular
  vector differs from the ordinary one only by `-(3/2)(e₁₂[-2]|0⟩)` (the `two_combo_eq`, plus the
  explicit square-bracket coefficients `c(1,-1,0) = 1/2`, `c(1,-1,1) = -1/12`, `c(1,-2,-1) = 1`);
* propagation along the coadjoint orbit (`sym_adG`, the seven `adPoly` identities).

Result: `A2.vacuumQuarticRelation : VacuumQuarticRelation W 36`, and the A₂ headline with the
MLDE in place of Kac–Wakimoto needs only U5, U6 and the q-series identity `A2ProductMLDE`.
-/

namespace VOA.DeligneAudit.A2

open VOA VOA.AffineSl3 VOA.ZhuCoordinate VOA.DeligneAudit.DeligneMLDE
  VOA.DeligneAudit.VacuumRelation MvPolynomial VOA.DeligneHigherRankConditionalCapstone

noncomputable section

theorem W_conformalVector :
    W.conformalVector = simpleProjection (-3 / 2) level_add_three_ne_zero (omegaA (-3 / 2)) :=
  rfl

theorem gen_primary (a : Fin 8) : W.L 1 (gen a) = 0 := by
  have hx : currentState (-3 / 2) (generator a)
      ∈ (affineSl3VOA (-3 / 2) level_add_three_ne_zero).grading 1 :=
    currentState_mem_grading _ _
  have h0 := affineSl3_qp (-3 / 2) level_add_three_ne_zero _ hx
  change W.smul W.conformalVector (1 + 1) (gen a) = 0
  rw [W_conformalVector]
  change W.smul (simpleProjection _ _ (omegaA (-3 / 2))) (1 + 1)
    (simpleProjection _ _ (currentState (-3 / 2) (generator a))) = 0
  rw [simpleProjection_product]
  change simpleProjection _ _ ((affineSl3VOA (-3 / 2) level_add_three_ne_zero).L 1 _) = 0
  rw [h0, map_zero]

theorem gen_form (a b : Fin 8) :
    W.smul (gen a) 1 (gen b) = ((-3 / 2 : ℂ) * formTable a b) • W.vacuum := by
  have h := simpleCurrentState_first_product (-3 / 2) level_add_three_ne_zero
    (generator b) (generator a)
  rw [form_generator_eq_table] at h
  exact h

theorem gen_sugawara :
    W.conformalVector = (2 * ((-3 / 2 : ℂ) + 3))⁻¹ •
      ∑ i, ∑ j, kappaInv i j • W.smul (gen i) (-1) (gen j) := by
  rw [W_conformalVector, omegaA_creation_form, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_gen_gen]

theorem kappaInv_bracket_trace (c : Fin 8) :
    ∑ i, ∑ j, kappaInv i j * bracketTable i j c = 0 := by
  fin_cases c <;> simp [Fin.sum_univ_eight, kappaInv, bracketTable]

theorem kappaInv_form_trace : ∑ i, ∑ j, kappaInv i j * formTable i j = 8 := by
  simp [Fin.sum_univ_eight, kappaInv, formTable]
  norm_num

/-- **The square-bracket current data of `L_{-3/2}(sl₃)`.** -/
def a2CurrentData : SqCurrentData W (Fin 8) where
  g := gen
  mem := gen_weight_one
  primary := gen_primary
  T := bracketTable
  bracket := smul_gen_zero
  F := formTable
  level := -3 / 2
  form := gen_form
  K := kappaInv
  hdual := 3
  ne := level_add_three_ne_zero
  sugawara := gen_sugawara
  bracket_trace := kappaInv_bracket_trace
  central := by
    rw [kappaInv_form_trace, simple_centralCharge]
    norm_num

theorem casPoly_eq : a2CurrentData.casPoly = MvPolynomial.C (1 / 3 : ℂ) * casimir := by
  simp only [SqCurrentData.casPoly, a2CurrentData]
  simp [Fin.sum_univ_eight, kappaInv, casimir, q]
  try simp only [one_div]
  have h3 : (MvPolynomial.C (3⁻¹ : ℂ) : MvPolynomial (Fin 8) ℂ) * 3 = 1 := by
    rw [← map_ofNat (MvPolynomial.C (σ := Fin 8) (R := ℂ)) 3, ← map_mul]
    norm_num
  have h2 : (MvPolynomial.C (2 / 3 : ℂ) : MvPolynomial (Fin 8) ℂ)
      = MvPolynomial.C (3⁻¹ : ℂ) * 2 := by
    rw [← map_ofNat (MvPolynomial.C (σ := Fin 8) (R := ℂ)) 2, ← map_mul]
    norm_num
  linear_combination (-2 * (X 0 * X 3 + X 1 * X 4 + X 2 * X 5)) * h3
    + (X 6 ^ 2 + X 7 ^ 2) * h2

/-- `g_a[-1] g_b[-1]|0⟩ = g_a(-1)g_b + ½ g_a(0)g_b - (1/12) g_a(1)g_b` in `W`. -/
theorem sq_sq_vacuum (a b : Fin 8) :
    a2CurrentData.sq a (-1) (a2CurrentData.sq b (-1) W.vacuum)
      = W.smul (gen a) (-1) (gen b) + (1 / 2 : ℂ) • W.smul (gen a) 0 (gen b)
        - (1 / 12 : ℂ) • W.smul (gen a) 1 (gen b) := by
  simp only [SqCurrentData.sq, a2CurrentData]
  rw [vSqZ_neg_one_vacuum, vSqZ_neg_one_current W (gen_weight_one a) (gen_weight_one b)]

-- Heartbeats raised for the `GradedVertexOperatorAlgebra` layer:
-- the extra parent projection deepens `whnf`/`isDefEq` on this concrete VOA.
set_option maxHeartbeats 400000 in
/-- The square version of the highest singular vector is `-(3/2) e₁₂[-2]|0⟩`. -/
theorem square_singular_eq :
    a2CurrentData.sq 6 (-1) (a2CurrentData.sq 2 (-1) W.vacuum)
      - a2CurrentData.sq 7 (-1) (a2CurrentData.sq 2 (-1) W.vacuum)
      + (3 : ℂ) • a2CurrentData.sq 1 (-1) (a2CurrentData.sq 0 (-1) W.vacuum)
      = (-3 / 2 : ℂ) • a2CurrentData.sq 2 (-2) W.vacuum := by
  have hT := two_combo_eq
  have h62 : W.smul (gen 6) 0 (gen 2) = gen 2 := by
    rw [smul_gen_zero]; simp [Fin.sum_univ_eight, bracketTable]
  have h72 : W.smul (gen 7) 0 (gen 2) = gen 2 := by
    rw [smul_gen_zero]; simp [Fin.sum_univ_eight, bracketTable]
  have h10 : W.smul (gen 1) 0 (gen 0) = -gen 2 := by
    rw [smul_gen_zero]; simp [Fin.sum_univ_eight, bracketTable]
  have f62 : W.smul (gen 6) 1 (gen 2) = 0 := by rw [gen_form]; simp [formTable]
  have f72 : W.smul (gen 7) 1 (gen 2) = 0 := by rw [gen_form]; simp [formTable]
  have f10 : W.smul (gen 1) 1 (gen 0) = 0 := by rw [gen_form]; simp [formTable]
  have hv : a2CurrentData.sq 2 (-2) W.vacuum = W.L (-1) (gen 2) + gen 2 := by
    simp only [SqCurrentData.sq, a2CurrentData]
    exact vSqZ_neg_two_vacuum W (gen_weight_one 2)
  have hTr : W.smul (gen 2) (-2) W.vacuum = W.L (-1) (gen 2) := by
    rw [← VertexOperatorAlgebra.T_eq_Lneg1]; rfl
  rw [sq_sq_vacuum, sq_sq_vacuum, sq_sq_vacuum, h62, h72, h10, f62, f72, f10, hv]
  rw [hTr] at hT
  linear_combination (norm := module) (1 / 2 : ℂ) • hT

theorem sym_relationPoly_two : a2CurrentData.sym (relationPoly 2) = 0 := by
  have hp : relationPoly 2 = MvPolynomial.C 1 * (X 6 * X 2) + MvPolynomial.C (-1) * (X 7 * X 2)
      + MvPolynomial.C 3 * (X 1 * X 0) := by
    rw [relationPoly_two, ← map_ofNat (MvPolynomial.C (σ := Fin 8) (R := ℂ)) 3, map_neg, map_one]
    ring
  rw [hp, SqCurrentData.sym_three]
  have hv : (1 : ℂ) • a2CurrentData.sq 6 (-1) (a2CurrentData.sq 2 (-1) W.vacuum)
      + (-1 : ℂ) • a2CurrentData.sq 7 (-1) (a2CurrentData.sq 2 (-1) W.vacuum)
      + (3 : ℂ) • a2CurrentData.sq 1 (-1) (a2CurrentData.sq 0 (-1) W.vacuum)
      = (-3 / 2 : ℂ) • a2CurrentData.sq 2 (-((2 : ℕ) : ℤ)) W.vacuum := by
    rw [show (-((2 : ℕ) : ℤ)) = -2 by norm_num, ← square_singular_eq]
    module
  rw [hv, map_smul, a2CurrentData.mkQ_sq_neg_mem 2 2 le_rfl W.vacuum, smul_zero]

/-- **Every relation of `I₂ⁿˢ` has vanishing square symbol** (coadjoint propagation). -/
theorem sym_relationPoly (e : Fin 8) : a2CurrentData.sym (relationPoly e) = 0 := by
  have ad : ∀ (b : Fin 8) (p : MvPolynomial (Fin 8) ℂ), a2CurrentData.sym p = 0 →
      a2CurrentData.sym (adPoly b p) = 0 := fun b p hp => by
    have := a2CurrentData.sym_adG b p
    rw [hp, map_zero] at this
    exact this
  have neg : ∀ p : MvPolynomial (Fin 8) ℂ, a2CurrentData.sym (-p) = 0 →
      a2CurrentData.sym p = 0 := fun p h => by
    have := a2CurrentData.sym_sub 0 p
    rw [zero_sub, h, a2CurrentData.sym_zero, zero_sub, eq_comm, neg_eq_zero] at this
    exact this
  have h2 := sym_relationPoly_two
  have h1 : a2CurrentData.sym (relationPoly 1) = 0 := by
    have := ad 3 _ h2; rwa [adPoly_f1_R2] at this
  have h0 : a2CurrentData.sym (relationPoly 0) = 0 := by
    have := ad 4 _ h2; rw [adPoly_f2_R2] at this; exact neg _ this
  have h6 : a2CurrentData.sym (relationPoly 6) = 0 := by
    have := ad 3 _ h0; rw [adPoly_f1_R0] at this; exact neg _ this
  have h7 : a2CurrentData.sym (relationPoly 7) = 0 := by
    have := ad 4 _ h1; rw [adPoly_f2_R1] at this; exact neg _ this
  have h3 : a2CurrentData.sym (relationPoly 3) = 0 := by
    have := ad 3 _ h7; rw [adPoly_f1_R7] at this; exact neg _ this
  have h4 : a2CurrentData.sym (relationPoly 4) = 0 := by
    have := ad 4 _ h6; rw [adPoly_f2_R6] at this; exact neg _ this
  have h5 : a2CurrentData.sym (relationPoly 5) = 0 := by
    have := ad 3 _ h4; rw [adPoly_f1_R4] at this; exact neg _ this
  fin_cases e
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The cubic symbols `X_a · Σ K X X` vanish (the `X_mul_casimir_mem_I2ns`). -/
theorem sym_X_mul_casPoly (a : Fin 8) : a2CurrentData.sym (X a * a2CurrentData.casPoly) = 0 := by
  refine a2CurrentData.sym_eq_zero_of_mem_span relationPoly sym_relationPoly ?_
  rw [casPoly_eq, show X a * (MvPolynomial.C (1 / 3 : ℂ) * casimir)
    = MvPolynomial.C (1 / 3 : ℂ) * (X a * casimir) by ring]
  exact Ideal.mul_mem_left _ _ (X_mul_casimir_mem_I2ns a)

/-- **Residual 1 of the MLDE route for A₂: the vacuum quartic relation of `L_{-3/2}(sl₃)`**,
`S(L[-2]²|0⟩) = 36 · G₄ ⋆ S(|0⟩)`. -/
theorem vacuumQuarticRelation : VacuumQuarticRelation W 36 := by
  have h := a2CurrentData.vacuumQuarticRelation_of_symbols
    (simple_vacuum_ne_zero _ _) sym_X_mul_casPoly
  convert h using 1
  rw [simple_centralCharge]
  norm_num

/-- `dim L_{-3/2}(sl₃)_N = mldeCoeff 3 N` for every `N`, unconditionally. -/
theorem finrank_eq_mldeCoeff' (N : ℕ) :
    (Module.finrank ℂ (W.grading N) : ℚ) = DeligneCharacter.mldeCoeff 3 N :=
  finrank_eq_mldeCoeff vacuumQuarticRelation N

/-- Kac–Wakimoto from the product identity alone. -/
theorem kacWakimotoLowerBound_of_productMLDE (hprod : A2ProductMLDE) : KacWakimotoLowerBound :=
  kacWakimotoLowerBound_of_vacuumQuarticRelation vacuumQuarticRelation hprod

/-- **The A₂ headline with the MLDE**: inputs U5, U6 and the q-series identity only. -/
theorem classicallyFree_of_productMLDE (F : ℕ → PowerSeries ℚ)
    (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries) (hprod : A2ProductMLDE) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_literatureMLDE F hU5 hU6 vacuumQuarticRelation hprod

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.a2CurrentData
#print axioms VOA.DeligneAudit.A2.sym_relationPoly
#print axioms VOA.DeligneAudit.A2.vacuumQuarticRelation
#print axioms VOA.DeligneAudit.A2.finrank_eq_mldeCoeff'
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_productMLDE
end AxiomAudit
