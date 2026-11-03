/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorLoop
import VOA.DeligneAudit.A2RelationsPresentation
import VOA.DeligneAudit.A2CarrierChain

/-!
# Step B5 for A₂: `M_m ⊂ W_m`

The full quadratic relations `I₂ = I₂ⁿˢ ⊕ ℂ Q` of `sl₃` (`fullMatrix`) span an `ad`-stable
subspace of `Sym² sl₃`: the Casimir is invariant and each `adPoly x (relationPoly a)` is an explicit
combination of the `relationPoly b` (64 identities, `ad_x_a`, checked by `ring`).  The index
`f₁₂ = 5` is diagonal-free (`f₁₂²` occurs in no relation).  Hence the cyclic `sl₃[t]`-module
`M_m = U(sl₃[t]) · δ_{(f₁₂,…,f₁₂)}` lies in the current carrier `W_m`.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.QuadraticCurrentFunctionalCarrier
open VOA.QuadraticJetCoefficientPairing VOA.AffineSl3

noncomputable section

theorem adPoly_six_mul (b : Fin 8) (p : MvPolynomial (Fin 8) ℂ) :
    adPoly b (6 * p) = 6 * adPoly b p := by
  have : (6 : MvPolynomial (Fin 8) ℂ) * p = (6 : ℂ) • p := by
    rw [MvPolynomial.smul_eq_C_mul, map_ofNat]
  rw [this, Derivation.map_smul, MvPolynomial.smul_eq_C_mul, map_ofNat]

/-- Expand `adPoly` on an explicit relation and compare by `ring` (robust variant). -/
macro "adc" : tactic => `(tactic| (
  set_option linter.unusedSimpArgs false in
  simp only [relationPoly, casimir, Fin.isValue, Matrix.cons_val, map_add, map_sub, map_neg,
    adPoly_two_mul, adPoly_three_mul, adPoly_six_mul, adPoly_q, Fin.sum_univ_eight,
    bracketTable] <;>
  (try simp) <;>
  (try simp only [MvPolynomial.smul_eq_C_mul, map_neg, map_ofNat, map_one]) <;>
  ring))

set_option maxHeartbeats 1000000 in -- eight explicit polynomial identities
/-- The Casimir is `ad`-invariant. -/
theorem casimir_ad (x : Fin 8) : adPoly x casimir = 0 := by
  fin_cases x <;> adc

theorem ad_0_0 : adPoly 0 (relationPoly 0) = 0 := by adc

theorem ad_0_1 : adPoly 0 (relationPoly 1) = relationPoly 2 := by adc

theorem ad_0_2 : adPoly 0 (relationPoly 2) = 0 := by adc

theorem ad_0_3 : adPoly 0 (relationPoly 3) = relationPoly 6 := by adc

theorem ad_0_4 : adPoly 0 (relationPoly 4) = 0 := by adc

theorem ad_0_5 : adPoly 0 (relationPoly 5) = -relationPoly 4 := by adc

theorem ad_0_6 : adPoly 0 (relationPoly 6) = -(2 * relationPoly 0) := by adc

theorem ad_0_7 : adPoly 0 (relationPoly 7) = relationPoly 0 := by adc

theorem ad_1_0 : adPoly 1 (relationPoly 0) = -relationPoly 2 := by adc

theorem ad_1_1 : adPoly 1 (relationPoly 1) = 0 := by adc

theorem ad_1_2 : adPoly 1 (relationPoly 2) = 0 := by adc

theorem ad_1_3 : adPoly 1 (relationPoly 3) = 0 := by adc

theorem ad_1_4 : adPoly 1 (relationPoly 4) = relationPoly 7 := by adc

theorem ad_1_5 : adPoly 1 (relationPoly 5) = relationPoly 3 := by adc

theorem ad_1_6 : adPoly 1 (relationPoly 6) = relationPoly 1 := by adc

theorem ad_1_7 : adPoly 1 (relationPoly 7) = -(2 * relationPoly 1) := by adc

theorem ad_2_0 : adPoly 2 (relationPoly 0) = 0 := by adc

theorem ad_2_1 : adPoly 2 (relationPoly 1) = 0 := by adc

theorem ad_2_2 : adPoly 2 (relationPoly 2) = 0 := by adc

theorem ad_2_3 : adPoly 2 (relationPoly 3) = -relationPoly 1 := by adc

theorem ad_2_4 : adPoly 2 (relationPoly 4) = relationPoly 0 := by adc

theorem ad_2_5 : adPoly 2 (relationPoly 5) = relationPoly 6 + relationPoly 7 := by adc

theorem ad_2_6 : adPoly 2 (relationPoly 6) = -relationPoly 2 := by adc

theorem ad_2_7 : adPoly 2 (relationPoly 7) = -relationPoly 2 := by adc

theorem ad_3_0 : adPoly 3 (relationPoly 0) = -relationPoly 6 := by adc

theorem ad_3_1 : adPoly 3 (relationPoly 1) = 0 := by adc

theorem ad_3_2 : adPoly 3 (relationPoly 2) = relationPoly 1 := by adc

theorem ad_3_3 : adPoly 3 (relationPoly 3) = 0 := by adc

theorem ad_3_4 : adPoly 3 (relationPoly 4) = -relationPoly 5 := by adc

theorem ad_3_5 : adPoly 3 (relationPoly 5) = 0 := by adc

theorem ad_3_6 : adPoly 3 (relationPoly 6) = 2 * relationPoly 3 := by adc

theorem ad_3_7 : adPoly 3 (relationPoly 7) = -relationPoly 3 := by adc

theorem ad_4_0 : adPoly 4 (relationPoly 0) = 0 := by adc

theorem ad_4_1 : adPoly 4 (relationPoly 1) = -relationPoly 7 := by adc

theorem ad_4_2 : adPoly 4 (relationPoly 2) = -relationPoly 0 := by adc

theorem ad_4_3 : adPoly 4 (relationPoly 3) = relationPoly 5 := by adc

theorem ad_4_4 : adPoly 4 (relationPoly 4) = 0 := by adc

theorem ad_4_5 : adPoly 4 (relationPoly 5) = 0 := by adc

theorem ad_4_6 : adPoly 4 (relationPoly 6) = -relationPoly 4 := by adc

theorem ad_4_7 : adPoly 4 (relationPoly 7) = 2 * relationPoly 4 := by adc

theorem ad_5_0 : adPoly 5 (relationPoly 0) = relationPoly 4 := by adc

theorem ad_5_1 : adPoly 5 (relationPoly 1) = -relationPoly 3 := by adc

theorem ad_5_2 : adPoly 5 (relationPoly 2) = -relationPoly 6 + -relationPoly 7 := by adc

theorem ad_5_3 : adPoly 5 (relationPoly 3) = 0 := by adc

theorem ad_5_4 : adPoly 5 (relationPoly 4) = 0 := by adc

theorem ad_5_5 : adPoly 5 (relationPoly 5) = 0 := by adc

theorem ad_5_6 : adPoly 5 (relationPoly 6) = relationPoly 5 := by adc

theorem ad_5_7 : adPoly 5 (relationPoly 7) = relationPoly 5 := by adc

theorem ad_6_0 : adPoly 6 (relationPoly 0) = 2 * relationPoly 0 := by adc

theorem ad_6_1 : adPoly 6 (relationPoly 1) = -relationPoly 1 := by adc

theorem ad_6_2 : adPoly 6 (relationPoly 2) = relationPoly 2 := by adc

theorem ad_6_3 : adPoly 6 (relationPoly 3) = -(2 * relationPoly 3) := by adc

theorem ad_6_4 : adPoly 6 (relationPoly 4) = relationPoly 4 := by adc

theorem ad_6_5 : adPoly 6 (relationPoly 5) = -relationPoly 5 := by adc

theorem ad_6_6 : adPoly 6 (relationPoly 6) = 0 := by adc

theorem ad_6_7 : adPoly 6 (relationPoly 7) = 0 := by adc

theorem ad_7_0 : adPoly 7 (relationPoly 0) = -relationPoly 0 := by adc

theorem ad_7_1 : adPoly 7 (relationPoly 1) = 2 * relationPoly 1 := by adc

theorem ad_7_2 : adPoly 7 (relationPoly 2) = relationPoly 2 := by adc

theorem ad_7_3 : adPoly 7 (relationPoly 3) = relationPoly 3 := by adc

theorem ad_7_4 : adPoly 7 (relationPoly 4) = -(2 * relationPoly 4) := by adc

theorem ad_7_5 : adPoly 7 (relationPoly 5) = -relationPoly 5 := by adc

theorem ad_7_6 : adPoly 7 (relationPoly 6) = 0 := by adc

theorem ad_7_7 : adPoly 7 (relationPoly 7) = 0 := by adc

/-- The span of the full quadratic relations. -/
abbrev relSpan : Submodule ℂ (MvPolynomial (Fin 8) ℂ) :=
  Submodule.span ℂ (Set.range fun s => quadraticRelation (fullMatrix s))

theorem relationPoly_mem_relSpan (b : Fin 8) : relationPoly b ∈ relSpan :=
  Submodule.subset_span ⟨some b, quadraticRelation_fullMatrix_some b⟩

theorem two_mul_mem_relSpan {p : MvPolynomial (Fin 8) ℂ} (hp : p ∈ relSpan) :
    2 * p ∈ relSpan := by
  rw [show (2 : MvPolynomial (Fin 8) ℂ) * p = (2 : ℂ) • p by
    rw [MvPolynomial.smul_eq_C_mul, map_ofNat]]
  exact Submodule.smul_mem _ _ hp

set_option maxHeartbeats 1000000 in -- 64 cases
theorem adPoly_relationPoly_mem (x a : Fin 8) : adPoly x (relationPoly a) ∈ relSpan := by
  fin_cases x <;> fin_cases a <;>
  simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ad_0_0, ad_0_1, ad_0_2,
    ad_0_3, ad_0_4, ad_0_5, ad_0_6, ad_0_7, ad_1_0, ad_1_1, ad_1_2, ad_1_3, ad_1_4, ad_1_5,
    ad_1_6, ad_1_7, ad_2_0, ad_2_1, ad_2_2, ad_2_3, ad_2_4, ad_2_5, ad_2_6, ad_2_7, ad_3_0,
    ad_3_1, ad_3_2, ad_3_3, ad_3_4, ad_3_5, ad_3_6, ad_3_7, ad_4_0, ad_4_1, ad_4_2, ad_4_3,
    ad_4_4, ad_4_5, ad_4_6, ad_4_7, ad_5_0, ad_5_1, ad_5_2, ad_5_3, ad_5_4, ad_5_5, ad_5_6,
    ad_5_7, ad_6_0, ad_6_1, ad_6_2, ad_6_3, ad_6_4, ad_6_5, ad_6_6, ad_6_7, ad_7_0, ad_7_1,
    ad_7_2, ad_7_3, ad_7_4, ad_7_5, ad_7_6, ad_7_7] <;>
  repeat' first
    | exact Submodule.zero_mem _
    | exact relationPoly_mem_relSpan _
    | apply two_mul_mem_relSpan
    | apply Submodule.add_mem
    | apply Submodule.neg_mem

/-- **The full relations of `sl₃` are `ad`-stable.** -/
theorem relationsStable : RelationsStable bracketTable fullMatrix := by
  intro x r
  rw [quadraticRelation_adMatrix]
  change adPoly x (quadraticRelation (fullMatrix r)) ∈ relSpan
  cases r with
  | none =>
      rw [quadraticRelation_fullMatrix_none, casimir_ad]
      exact Submodule.zero_mem _
  | some a =>
      rw [quadraticRelation_fullMatrix_some]
      exact adPoly_relationPoly_mem x a

theorem fullMatrix_diag (r : Option (Fin 8)) : fullMatrix r (5, 5) = 0 := by
  cases r with
  | none => simp [fullMatrix, casimirMatrix, entryMatrix]
  | some a =>
      fin_cases a <;> simp [fullMatrix, relationMatrix, relationEntries, entryMatrix]

/-- **Step B5 for A₂: `M_m = U(sl₃[t]) · δ_{f₁₂} ⊂ W_m`.** -/
theorem Mspace_le_carrier (m : ℕ) :
    Mspace bracketTable m (5 : Fin 8) ≤ currentCarrier fullMatrix m 0 :=
  Mspace_le bracketTable relationsStable 5 fullMatrix_diag

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.relationsStable
#print axioms VOA.DeligneAudit.A2.Mspace_le_carrier
end AxiomAudit
