/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeResidual
import VOA.Examples.VirasoroMovingNormDerivative

/-!
# The concrete q=3 source with a varying parameter

The finite recursion takes place in actual Verma modules and uses only
negative modes. The charge-zero coordinates therefore transport to every
charge. Its undivided numerator is the moving singular source; no division
by the terminal zero is used in that source.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The scalar diagonal on the vacuum curve with incoming and field
weight equal to 2/t-1. -/
noncomputable def threeMovingDiagonal (t : ℂ) (r : ℕ) : ℂ :=
  threeStateDiagonal 0 (vermaBSAWeight 3 t) t (vermaBSAWeight 3 t) r

/-- The negative-mode multiplier on the same moving-parameter curve. -/
noncomputable def threeMovingCoefficient (t : ℂ) (r j : ℕ) : ℂ :=
  threeStateCoefficient 0 (vermaBSAWeight 3 t) t (vermaBSAWeight 3 t) r j

/-- Actual finite triangular states. Division is used only when invoking
a nonresonant coefficient equation; the definition is total at every t. -/
noncomputable def threeMovingState (c t : ℂ) : ℕ → Verma c 0
  | 0 => highestVector c 0
  | r+1 => -(threeMovingDiagonal t (r+1))⁻¹ •
      ∑ j : Fin (r+1), threeMovingCoefficient t (r+1) j •
        vermaMode c 0 ((j:ℤ)-((r+1:ℕ):ℤ)) (threeMovingState c t j)
termination_by r => r

/-- The undivided numerator uses only earlier states. At a terminal
resonance this remains regular even though the next state denominator is zero. -/
noncomputable def threeMovingSource (c t : ℂ) (r : ℕ) : Verma c 0 :=
  ∑ j : Fin r, threeMovingCoefficient t r j •
    vermaMode c 0 ((j:ℤ)-(r:ℤ)) (threeMovingState c t j)

/-- Every constructed state belongs to its actual word level, independently
of whether a scalar denominator vanishes. -/
theorem threeMovingState_level (c t : ℂ) (r : ℕ) :
    threeMovingState c t r∈sortedSpan c 0 r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simpa [threeMovingState,negWord,energyHW] using
        (negWord_mem_sortedSpan_of_sorted c 0 sortedWord_nil rfl)
    | succ r =>
      rw [threeMovingState]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro j hj
      apply Submodule.smul_mem
      exact verma_mode_mem_level c 0 j (r+1) _ (ih j j.isLt) _ (by omega)

/-- The source numerator has its output level as well. -/
theorem threeMovingSource_level (c t : ℂ) (r : ℕ) :
    threeMovingSource c t r∈sortedSpan c 0 r := by
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact verma_mode_mem_level c 0 j r _ (threeMovingState_level c t j) _ (by omega)

/-- The states form an actual level sequence, to which the proved
positive-defect identities apply. -/
noncomputable def threeMovingSequence (c t : ℂ) : wardSequenceSpace c 0 :=
  ⟨threeMovingState c t,threeMovingState_level c t⟩

/-- At a nonzero diagonal, the recursive coefficient cancels its source
exactly. This is ordinary scalar inversion, not a primary-field assumption. -/
theorem threeMovingState_equation (c t : ℂ) (r : ℕ) (hr : 0<r)
    (hd : threeMovingDiagonal t r≠0) :
    threeMovingDiagonal t r • threeMovingState c t r+threeMovingSource c t r=0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  rw [threeMovingState]
  change _ • (-(threeMovingDiagonal t (n+1))⁻¹ • threeMovingSource c t (n+1))+_=0
  rw [smul_smul,mul_neg,mul_inv_cancel₀ hd,neg_one_smul,neg_add_cancel]

/-- With finitely many nonzero diagonals, the actual cubic source vanishes
at every prescribed earlier coefficient. The initial zero follows from
the explicit vacuum-curve diagonal. -/
theorem threeMovingSequence_below (t : ℂ) (ht : t≠0) (R : ℕ)
    (hd : ∀ r, 0<r → r<R → threeMovingDiagonal t r≠0) :
    ∀ r<R, (wardSourceAt (vermaBSACharge t) 0 (vermaBSAWeight 3 t) t
      (vermaBSAWeight 3 t) 3 (threeMovingSequence (vermaBSACharge t) t)).val r=0 := by
  intro r hr
  rw [wardSourceAt_three_state_recursion]
  change threeMovingDiagonal t r • threeMovingState _ t r+threeMovingSource _ t r=0
  by_cases hz : r=0
  · subst r
    simp [threeMovingDiagonal,threeStateDiagonal_vacuum_factor t ht,threeMovingSource]
  · exact threeMovingState_equation _ t r (by omega) (hd r (by omega) hr)

/-- Creation-only recursion has identical PBW coordinates at every charge. -/
theorem chargeTransport_threeMovingState (c c' t : ℂ) (r : ℕ) :
    chargeTransport c c' 0 (threeMovingState c t r)=threeMovingState c' t r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [threeMovingState]
    | succ r =>
      rw [threeMovingState,threeMovingState,map_smul,map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul,chargeTransport_negative _ _ _ _ (by omega),ih j j.isLt]

/-- The complete undivided source transports without changing its words. -/
theorem chargeTransport_threeMovingSource (c c' t : ℂ) (r : ℕ) :
    chargeTransport c c' 0 (threeMovingSource c t r)=threeMovingSource c' t r := by
  unfold threeMovingSource
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul,chargeTransport_negative _ _ _ _ (by omega),chargeTransport_threeMovingState]

/-- One finite word expression for the source at any parameter, with
actual charge supplied only when evaluating those words. -/
noncomputable def threeMovingExpression (t : ℂ) (r : ℕ) : VirWordExpression :=
  chargeWordExpression (threeMovingSource 0 t r)

/-- The word expression evaluates to the genuine projected moving source. -/
theorem threeMovingExpression_eval (c t : ℂ) (r : ℕ) :
    wordExpressionEval c (threeMovingExpression t r)=
      vacuumProjection c (threeMovingSource c t r) := by
  rw [threeMovingExpression,chargeWordExpression_eval,chargeTransport_threeMovingSource]

/-- Cancellation of the field parameter makes the diagonal an ordinary
quadratic polynomial in t, with its two possible resonances explicit. -/
theorem threeMovingDiagonal_polynomial (t : ℂ) (ht : t≠0) (r : ℕ) :
    threeMovingDiagonal t r=(r:ℂ)/4*(((r:ℂ)+1)*t-2)*(((r:ℂ)+2)*t-6) := by
  rw [threeMovingDiagonal,threeStateDiagonal_vacuum_factor t ht]
  unfold vermaBSAWeight
  norm_num
  field_simp
  ring

/-- The off-diagonal coefficients are affine polynomials in the moving
parameter once the vacuum-curve weight is substituted. -/
theorem threeMovingCoefficient_polynomial (t : ℂ) (ht : t≠0) (r j : ℕ) :
    threeMovingCoefficient t r j=(r:ℂ)-(j:ℂ)+2-t*((r:ℂ)+(j:ℂ)+2)/2 := by
  unfold threeMovingCoefficient threeStateCoefficient vermaBSAWeight
  norm_num
  field_simp
  ring

/-- The field parameter is differentiable at every nonzero t. -/
theorem threeMovingWeight_differentiable (t : ℂ) (ht : t≠0) :
    DifferentiableAt ℂ (fun z => vermaBSAWeight 3 z) t := by
  unfold vermaBSAWeight
  fun_prop (disch := norm_num [ht])

/-- Each explicit source multiplier is differentiable away from t=0. -/
theorem threeMovingCoefficient_differentiable (t : ℂ) (ht : t≠0) (r j : ℕ) :
    DifferentiableAt ℂ (fun z => threeMovingCoefficient z r j) t := by
  have hw := threeMovingWeight_differentiable t ht
  unfold threeMovingCoefficient threeStateCoefficient
  fun_prop

/-- The cubic diagonal is also differentiable before taking its inverse. -/
theorem threeMovingDiagonal_differentiable (t : ℂ) (ht : t≠0) (r : ℕ) :
    DifferentiableAt ℂ (fun z => threeMovingDiagonal z r) t := by
  have hw := threeMovingWeight_differentiable t ht
  unfold threeMovingDiagonal threeStateDiagonal
  fun_prop

/-- Every scalar linear coordinate of a preterminal state is differentiable
where the finitely many used denominators are nonzero. No topology on the
infinite-dimensional Verma module is postulated. -/
theorem threeMovingState_coordinate_differentiable (t : ℂ) (ht : t≠0) (r : ℕ)
    (hd : ∀ j, 0<j → j≤r → threeMovingDiagonal t j≠0)
    (ell : Verma 0 0 →ₗ[ℂ] ℂ) :
    DifferentiableAt ℂ (fun z => ell (threeMovingState 0 z r)) t := by
  induction r using Nat.strong_induction_on generalizing ell with
  | h r ih =>
    cases r with
    | zero => simpa only [threeMovingState] using differentiableAt_const (ell (highestVector 0 0))
    | succ r =>
      simp only [threeMovingState,map_smul,map_sum,smul_eq_mul]
      apply DifferentiableAt.mul
      · exact ((threeMovingDiagonal_differentiable t ht (r+1)).inv (hd _ (by omega) le_rfl)).neg
      · apply DifferentiableAt.fun_sum
        intro j hj
        apply DifferentiableAt.mul (threeMovingCoefficient_differentiable t ht _ _)
        exact ih j j.isLt (fun k hk hkj => hd k hk (by omega))
          (ell.comp (vermaMode 0 0 ((j:ℤ)-((r+1:ℕ):ℤ))))

/-- The source uses only earlier denominators; every linear coordinate is
therefore differentiable even at a terminal diagonal zero. -/
theorem threeMovingSource_coordinate_differentiable (t : ℂ) (ht : t≠0) (r : ℕ)
    (hd : ∀ j, 0<j → j<r → threeMovingDiagonal t j≠0)
    (ell : Verma 0 0 →ₗ[ℂ] ℂ) :
    DifferentiableAt ℂ (fun z => ell (threeMovingSource 0 z r)) t := by
  simp only [threeMovingSource,map_sum,map_smul,smul_eq_mul]
  apply DifferentiableAt.fun_sum
  intro j hj
  apply DifferentiableAt.mul (threeMovingCoefficient_differentiable t ht _ _)
  exact threeMovingState_coordinate_differentiable t ht j
    (fun k hk hkj => hd k hk (by omega))
    (ell.comp (vermaMode 0 0 ((j:ℤ)-(r:ℤ))))

end VOA.InverseDS.VirasoroVerma
