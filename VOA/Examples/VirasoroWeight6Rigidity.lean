/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroWeight6Norm

/-!
# Graded rigidity of Ising and M(2,7)

The ordinary null relations come from the canonical weight-six Gram matrix.
Their actual lifted adjoint pairings vanish, while finite word reduction gives
central polynomials with nonzero derivatives at the two charges. This forces
zero central motion, and the established reconstruction gives coboundaries.
-/
namespace VOA.VirDeformModes
open Module (End)
open VirModule VirSimple VirGram56 VertexOperatorAlgebra Deform

/-- The four word states are the already proved universal weight-six basis. -/
theorem weight6Word_basis (c : ℂ) (i : Fin 4) :
    virWord (virasoroVOA c).L (weight6Words i) (vacVec c) =
      (basis6 c i : VirUniv c) := by
  fin_cases i <;>
    simp [weight6Words, virWord, Module.End.mul_apply, Module.End.one_apply,
      basis6_apply, vec6, Matrix.cons_val_zero, Matrix.cons_val_succ,
      virasoroVOA_L_eq_Lop, L6vac, L4L2vac, L3L3vac, L222vac, LeeYang.L2vac, LeeYang.L3vac, LeeYang.L2L2vac]

/-- A row kernel of the canonical weight-six matrix gives the corresponding
actual word relation in the simple quotient. -/
theorem weight6_relation_of_gram (c : ℂ) (r : Fin 4 → ℂ)
    (hr : ∀ j, ∑ i, r i * canGram6 c i j = 0) :
    weight6State (virasoroSimple c).L r (virasoroSimple c).vacuum = 0 := by
  have hb : ∀ j, ∑ i, r i * (VirGram4.canB c).form
      (basis6 c i : VirUniv c) (basis6 c j : VirUniv c) = 0 := by
    intro j
    simpa only [← canGram_basis6, GramMat.canGram_apply, VirGram4.canB] using hr j
  have hm := gram_row_relation_mem_maxIdeal (VirGram4.canB c)
    (VirGram4.canB_isFullyInvariant c) (VirGram4.canB_normalized c) (basis6 c) r hb
  have hz : (maxIdealVir c).mkQ (∑ i, r i • (basis6 c i : VirUniv c)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  simpa only [weight6State, map_sum, map_smul, ← weight6Word_basis, virWord_mkQ,
    virasoroSimple_vacuum] using hz

/-- The integral Ising coefficients are a row kernel at c=1/2. -/
theorem ising_gram6_row (j : Fin 4) :
    ∑ i, isingCoefficients i * canGram6 isingC i j = 0 := by
  fin_cases j <;> norm_num [canGram6_eq, isingCoefficients, isingC,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- The integral M(2,7) coefficients are a row kernel at c=−68/7. -/
theorem m27_gram6_row (j : Fin 4) :
    ∑ i, m27Coefficients i * canGram6 m27C i j = 0 := by
  fin_cases j <;> norm_num [canGram6_eq, m27Coefficients, m27C,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- The Ising weight-six word actually vanishes in the simple quotient. -/
theorem ising_simple_relation :
    weight6State (virasoroSimple isingC).L isingCoefficients
      (virasoroSimple isingC).vacuum = 0 :=
  weight6_relation_of_gram isingC isingCoefficients ising_gram6_row

/-- The M(2,7) weight-six word actually vanishes in the simple quotient. -/
theorem m27_simple_relation :
    weight6State (virasoroSimple m27C).L m27Coefficients
      (virasoroSimple m27C).vacuum = 0 :=
  weight6_relation_of_gram m27C m27Coefficients m27_gram6_row

/-- Taylor evaluation of the Ising word norm: its constant term is zero
and its first-order coefficient is 84084 times the central variation. -/
theorem ising_weight6_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    (δ : ℂ) (v : V) :
    let K : End ℂ (V × V) := isingC • 1 + δ • tangentShift
    (-83316 : ℂ) • K (v,0) + (165096 : ℂ) • (K^2) (v,0) +
      (3072 : ℂ) • (K^3) (v,0) = (0, (84084*δ) • v) := by
  dsimp only
  apply Prod.ext <;>
    simp [isingC, pow_succ, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, tangentShift, smul_add, smul_smul] <;> module

/-- Taylor evaluation of the M(2,7) word norm detects central variation
with the nonzero coefficient 102102. -/
theorem m27_weight6_central {V : Type*} [AddCommGroup V] [Module ℂ V]
    (δ : ℂ) (v : V) :
    let K : End ℂ (V × V) := m27C • 1 + δ • tangentShift
    (67830 : ℂ) • K (v,0) + (48951/2 : ℂ) • (K^2) (v,0) +
      (7203/4 : ℂ) • (K^3) (v,0) = (0, (102102*δ) • v) := by
  dsimp only
  apply Prod.ext <;>
    simp [m27C, pow_succ, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, tangentShift, smul_add, smul_smul] <;> module


/-- Every actual graded deformation at the ising charge has zero normalized
central variation. The ordinary quotient relation and actual word polynomial
are proved inputs, not determinant-preservation assumptions. -/
theorem ising_actual_central_variation_zero
    (D : FirstOrderDeformation (virasoroSimple isingC)) (hD : D.IsGraded) (α β : ℂ)
    (ha : D.smul₁ (virasoroSimple isingC).conformalVector 3
      (virasoroSimple isingC).conformalVector = α • (virasoroSimple isingC).vacuum)
    (hb : D.smul₁ (virasoroSimple isingC).conformalVector 1
      (virasoroSimple isingC).conformalVector = β • (virasoroSimple isingC).conformalVector) :
    2*α-β*isingC = 0 := by
  let W := virasoroSimple isingC
  let A := normalizedData D hD (virasoroSimple_grading_one _) α β ha hb
  have hv (n : ℤ) (hn : -1 ≤ n) : A.L n (W.vacuum,0) = 0 :=
    normalizedL_vacuum D β n hn
  have hp := ising_weight6_polynomial A (W.vacuum,0) hv
  have hz := virWord_pairing_obstruction D β (VirQuotForm.Bsimp _)
    weight6Words isingCoefficients ising_simple_relation
  change (VirQuotForm.Bsimp _).form W.vacuum
    (weight6Adjoint A.L isingCoefficients (weight6State A.L isingCoefficients (W.vacuum,0))).2 = 0 at hz
  have hK : A.central = isingC • 1 + (2*α-β*isingC) • tangentShift := rfl
  rw [pow_one, hK, ising_weight6_central] at hp
  rw [hp] at hz
  change (VirQuotForm.Bsimp isingC).form W.vacuum
    ((84084 * (2*α-β*isingC)) • W.vacuum) = 0 at hz
  have hB : (VirQuotForm.Bsimp isingC).form W.vacuum W.vacuum = 1 :=
    VirQuotForm.Bsimp_normalized _
  simp only [map_smul, smul_eq_mul, hB, mul_one] at hz
  linear_combination hz / 84084

/-- All graded first-order deformations of the ising simple Virasoro algebra
are coordinate changes. Central obstruction and reconstruction are both
proved, with no residual rigidity hypotheses. -/
theorem ising_graded_rigidity : Deform.IsRigidGraded (virasoroSimple isingC) := by
  intro D hD
  obtain ⟨α, β, A, ha, hb, hL, hK⟩ := virasoroSimple_exists_normalizedData _ D hD
  exact isTrivial_of_zero_central_variation _ D hD α β ha hb
    (ising_actual_central_variation_zero D hD α β ha hb)

/-- Every actual graded deformation at the m27 charge has zero normalized
central variation. The ordinary quotient relation and actual word polynomial
are proved inputs, not determinant-preservation assumptions. -/
theorem m27_actual_central_variation_zero
    (D : FirstOrderDeformation (virasoroSimple m27C)) (hD : D.IsGraded) (α β : ℂ)
    (ha : D.smul₁ (virasoroSimple m27C).conformalVector 3
      (virasoroSimple m27C).conformalVector = α • (virasoroSimple m27C).vacuum)
    (hb : D.smul₁ (virasoroSimple m27C).conformalVector 1
      (virasoroSimple m27C).conformalVector = β • (virasoroSimple m27C).conformalVector) :
    2*α-β*m27C = 0 := by
  let W := virasoroSimple m27C
  let A := normalizedData D hD (virasoroSimple_grading_one _) α β ha hb
  have hv (n : ℤ) (hn : -1 ≤ n) : A.L n (W.vacuum,0) = 0 :=
    normalizedL_vacuum D β n hn
  have hp := m27_weight6_polynomial A (W.vacuum,0) hv
  have hz := virWord_pairing_obstruction D β (VirQuotForm.Bsimp _)
    weight6Words m27Coefficients m27_simple_relation
  change (VirQuotForm.Bsimp _).form W.vacuum
    (weight6Adjoint A.L m27Coefficients (weight6State A.L m27Coefficients (W.vacuum,0))).2 = 0 at hz
  have hK : A.central = m27C • 1 + (2*α-β*m27C) • tangentShift := rfl
  rw [pow_one, hK, m27_weight6_central] at hp
  rw [hp] at hz
  change (VirQuotForm.Bsimp m27C).form W.vacuum
    ((102102 * (2*α-β*m27C)) • W.vacuum) = 0 at hz
  have hB : (VirQuotForm.Bsimp m27C).form W.vacuum W.vacuum = 1 :=
    VirQuotForm.Bsimp_normalized _
  simp only [map_smul, smul_eq_mul, hB, mul_one] at hz
  linear_combination hz / 102102

/-- All graded first-order deformations of the m27 simple Virasoro algebra
are coordinate changes. Central obstruction and reconstruction are both
proved, with no residual rigidity hypotheses. -/
theorem m27_graded_rigidity : Deform.IsRigidGraded (virasoroSimple m27C) := by
  intro D hD
  obtain ⟨α, β, A, ha, hb, hL, hK⟩ := virasoroSimple_exists_normalizedData _ D hD
  exact isTrivial_of_zero_central_variation _ D hD α β ha hb
    (m27_actual_central_variation_zero D hD α β ha hb)

end VOA.VirDeformModes
