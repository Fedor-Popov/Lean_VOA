import VOA.DeligneAudit.DeligneFusionCVRectPBWLeadingRow
import VOA.DeligneAudit.DeligneFusionCVRectPBWLeadingSeries
import VOA.DeligneAudit.DeligneFusionCVRectPBWBoundaryDescendant

/-!
# The actual one-first, one-theta mixed PBW coefficient relation

A quadratic first-root coefficient and a second-root coefficient both annihilate
the source. Their proved commutator row becomes the full graded coefficient
once the two proved support cutoffs are imposed. No PBW coefficient ideal
presentation or dimension statement is a hypothesis.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWLeading

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.A2.CVFamily
open VOA.DeligneAudit.A2.CVRectFiltered VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectPBWBoundary

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

/-- A commuting graded operator is zero once it kills the actual graded generator. -/
theorem gradedEnd_zero_of_commute (A : Module.End ℂ (Gr R w))
    (hc : ∀ a k, A * grOp R w a k = grOp R w a k * A)
    (hw : A (grGenerator R w) = 0) : A = 0 := by
  apply LinearMap.ext_on_range (grWord_span_top R w)
  intro l
  change A (grWord R w l) = 0
  induction l with
  | nil => exact hw
  | cons x l ih =>
      rw [← grOp_grWord, ← Module.End.mul_apply, hc, Module.End.mul_apply, ih, map_zero]

theorem graded_Q_commute (a : Fin 3) (k r t : ℕ) :
    grOp R w a k * Q (grOp R w 2) r t =
      Q (grOp R w 2) r t * grOp R w a k := by
  have hc : Commute (PowerSeries.C (grOp R w a k)) (Garland.Fs (grOp R w 2)) := by
    change PowerSeries.C (grOp R w a k) * Garland.Fs (grOp R w 2) =
      Garland.Fs (grOp R w 2) * PowerSeries.C (grOp R w a k)
    apply PowerSeries.ext
    intro j
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, Garland.Fs,
      PowerSeries.coeff_mk]
    exact grOp_commute R w a 2 k j
  have he := congrArg (PowerSeries.coeff t) (hc.pow_right r).eq
  simpa only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, Q] using he

/-- Every proved simple-root coefficient relation kills the entire commuting
PBW cyclic representation, not merely its generator. -/
theorem graded_Q_zero_of_source (r t : ℕ) (hQ : Q (R.op 4) r t w = 0) :
    Q (grOp R w 2) r t = 0 := by
  have hz : orderedCoeff R w 0 0 r t = 0 := by
    simpa only [orderedCoeff, pow_zero, one_mul, Q] using hQ
  have hh := gradedOrderedCoeff_zero R w 0 0 r t (by rw [hz]; exact Submodule.zero_mem _)
  apply gradedEnd_zero_of_commute R w _ (fun a k => (graded_Q_commute R w a k r t).symm)
  simpa only [gradedOrderedCoeff, pow_zero, one_mul, Q] using hh

variable {R w} {ε ν ϱ : Weight}

private theorem first_graded_high (h : CV3Rel R w ε ν ϱ 0) (i : ℕ)
    (hi : ϱ.1 + ν.1 + ε.1 ≤ i) : grOp R w 0 i = 0 := by
  apply grOp_zero_of_source_zero R w
  apply trunc_of_cvrel h.first
  simp only [parts_length]
  omega

/-- The full `(p,q)=(1,1)` mixed coefficient is an actual graded relation. -/
theorem first_theta_second (h : CV3Rel R w ε ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) 2 +
      clippedSum (parts ϱ.2 ν.2 ε.2) (r + 1) < s + r + 2) :
    gradedOrderedCoeff R w 1 1 r s = 0 := by
  let C := clippedSum (parts ϱ.1 ν.1 ε.1) 2
  let S := C - 1
  change C + clippedSum (parts ϱ.2 ν.2 ε.2) (r + 1) < s + r + 2 at hs
  have hN : ϱ.1 + ν.1 + ε.1 ≤ C := by
    dsimp only [C]
    norm_num only [clippedSum_parts, show min 2 3 = 2 from rfl,
      show min 2 2 = 2 from rfl, show min 2 1 = 1 from rfl, Nat.mul_one]
    omega
  by_cases hzero : ϱ.1 + ν.1 + ε.1 = 0
  · have hF : Garland.Fs (grOp R w 0) = 0 := by
      apply PowerSeries.ext
      intro i
      simp only [Garland.Fs, PowerSeries.coeff_mk, map_zero]
      exact first_graded_high h i (by omega)
    simp only [gradedOrderedCoeff, pow_one, hF, zero_mul, map_zero, LinearMap.zero_apply]
  have hC : 1 ≤ C := by omega
  have hCS : S + 1 = C := Nat.sub_add_cancel hC
  by_cases hS : S ≤ s
  · let T := s - S
    have hST : S + T = s := Nat.add_sub_of_le hS
    have hA : Q (R.op 3) 2 S w = 0 := by
      have hCV : CVRel (R.op 3) (parts ϱ.1 ν.1 ε.1) w := by simpa using h.first
      exact coefficient_zero_of_cvrel_parts hCV 2 S (by change C < S + 2; omega)
    have hB : Q (R.op 4) (r + 1) T w = 0 :=
      second_coefficient_zero h (r + 1) T (by omega)
    have hF : ∀ i, S < i → grOp R w 0 i = 0 := by
      intro i hi
      exact first_graded_high h i (by omega)
    have hH : ∀ k, T < k → PowerSeries.coeff k (Garland.Fs (grOp R w 2) ^ r) = 0 := by
      intro k hk
      have hclip := clippedSum_mono (parts ϱ.2 ν.2 ε.2) (by omega : r ≤ r + 1)
      exact graded_Q_zero_of_source R w r k (second_coefficient_zero h r k (by omega))
    have he := coefficient_leading_row (grOp R w 0) (grOp R w 1)
      (Garland.Fs (grOp R w 2) ^ r) S T hF hH
    have he' := congrArg (fun A : Module.End ℂ (Gr R w) => A (grGenerator R w)) he
    have he'' : gradedOrderedCoeff R w 1 1 r (S + T) = gradedLeadingRow R w S r T := by
      simpa only [gradedOrderedCoeff, gradedLeadingRow, Garland.Fs, pow_one,
        LinearMap.sum_apply, Module.End.mul_apply] using he'
    rw [hST, gradedLeadingRow_zero R w S r T hA hB] at he''
    exact he''
  · have hclip := clippedSum_mono (parts ϱ.2 ν.2 ε.2) (by omega : r ≤ r + 1)
    have hr : clippedSum (parts ϱ.2 ν.2 ε.2) r < r := by omega
    have hG : Garland.Fs (grOp R w 2) ^ r = 0 := by
      apply PowerSeries.ext
      intro k
      simp only [map_zero]
      exact graded_Q_zero_of_source R w r k (second_coefficient_zero h r k (by omega))
    simp only [gradedOrderedCoeff, hG, mul_zero, map_zero, LinearMap.zero_apply]

end
end VOA.DeligneAudit.A2.CVRectPBWLeading

#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.graded_Q_zero_of_source
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.first_theta_second
