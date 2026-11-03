import VOA.DeligneAudit.DeligneFusionCVRectPBWTwoThetaSeries
import VOA.DeligneAudit.DeligneFusionCVRectPBWBoundaryDescendant

/-!
# Actual two-theta boundary coefficients

These coefficient relations are consequences of the actual CV source.
They use neither a dimension bound nor a PBW initial-ideal assumption.
The first partition has either no final part one, or its unique final
part one. In the latter case the actual opposite-root CV relation on
the top first-root descendant supplies the second polarization step.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWTwoTheta

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVPolarization
open VOA.DeligneAudit.A2.CVRectCommutative VOA.DeligneAudit.A2.CVRectPBWBoundary

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight}

private theorem negative_first_second (N k : ℕ) :
    (-R.op 3 N) * R.op 4 k - R.op 4 k * (-R.op 3 N) = R.op 5 (N + k) := by
  calc
    (-R.op 3 N) * R.op 4 k - R.op 4 k * (-R.op 3 N) =
        -(R.op 3 N * R.op 4 k - R.op 4 k * R.op 3 N) := by noncomm_ring
    _ = R.op 5 (N + k) := by
      rw [op_comm_end]
      simp [Fin.sum_univ_eight, bracketTable]

private theorem negative_first_theta (N k : ℕ) :
    (-R.op 3 N) * R.op 5 (N + k) = R.op 5 (N + k) * (-R.op 3 N) := by
  rw [neg_mul, mul_neg, neg_inj, ← sub_eq_zero, op_comm_end]
  simp [Fin.sum_univ_eight, bracketTable]

private theorem second_theta (N i k : ℕ) :
    R.op 4 i * R.op 5 (N + k) = R.op 5 (N + k) * R.op 4 i := by
  rw [← sub_eq_zero, op_comm_end]
  simp [Fin.sum_univ_eight, bracketTable]

/-- Two high theta factors follow by ordinary polarization when the
first auxiliary partition has no final part one. -/
theorem shifted_theta_second_two_no_one {e : ℕ}
    (h : CV3Rel R w (0, e) ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.2 ν.2 e) (r + 2) < s + (r + 2)) :
    mixedCoeff (fun k => R.op 5 (ϱ.1 + ν.1 + k)) (R.op 4) 2 r s w = 0 := by
  have hXw : (-R.op 3 (ϱ.1 + ν.1)) w = 0 := by
    rw [LinearMap.neg_apply, neg_eq_zero]
    apply trunc_of_cvrel h.first
    simp [parts_length]
  apply mixedCoeff_zero_of_Q (R.op 4) (fun k => R.op 5 (ϱ.1 + ν.1 + k))
    (-R.op 3 (ϱ.1 + ν.1)) (negative_first_second _) (negative_first_theta _)
    (second_theta _) hXw (second_coefficient_zero h (r + 2) s hs) 2 r (by omega)

/-- The actual full two-theta coefficient, with no final first-root part one. -/
theorem theta_second_two_no_one {e : ℕ}
    (h : CV3Rel R w (0, e) ν ϱ 0) (r s : ℕ)
    (hs : 2 * (ϱ.1 + ν.1) + clippedSum (parts ϱ.2 ν.2 e) (r + 2) <
      s + (r + 2)) :
    mixedCoeff (R.op 5) (R.op 4) 2 r s w = 0 := by
  apply mixedCoeff_two_zero_of_tail_and_lower (R.op 5) (R.op 4) w (ϱ.1 + ν.1)
    r s (CVRoots.sl2_highest R).hFF
  · intro hNs
    apply shifted_theta_second_two_no_one h r (s - 2 * (ϱ.1 + ν.1))
    omega
  · intro i hi his
    apply theta_second_one h r (s - i)
    have hc := clippedSum_mono (parts ϱ.2 ν.2 e) (by omega : r + 1 ≤ r + 2)
    change ϱ.1 + ν.1 + 0 + clippedSum (parts ϱ.2 ν.2 e) (r + 1) < s - i + (r + 1)
    omega
  · intro i j hi hj hij
    apply second_coefficient_zero h r (s - i - j)
    have hc := clippedSum_mono (parts ϱ.2 ν.2 e) (by omega : r ≤ r + 2)
    change clippedSum (parts ϱ.2 ν.2 e) r < s - i - j + r
    omega

/-- With one final first-root part one, the top first-root descendant
has a full opposite-root CV relation and is killed by the same first mode.
This gives two theta factors with exactly one extra cutoff unit. -/
theorem shifted_theta_second_two_one
    (h : CV3Rel R w (1, 0) ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.2 ν.2 0) (r + 2) + 1 < s + (r + 2)) :
    mixedCoeff (fun k => R.op 5 (ν.1 + ϱ.1 + k)) (R.op 4) 2 r s w = 0 := by
  let N := ν.1 + ϱ.1
  let X := -R.op 3 N
  have hX2 : X (X w) = 0 := by
    dsimp only [X, N]
    simpa only [LinearMap.neg_apply, map_neg, neg_neg, pow_two, Module.End.mul_apply]
      using first_descendant_square h
  have hQw : Q (R.op 4) (r + 2) s w = 0 :=
    second_coefficient_zero h (r + 2) s (by
      change clippedSum (parts ϱ.2 ν.2 0) (r + 2) < s + (r + 2)
      omega)
  have hQu : Q (R.op 4) (r + 2) s (X w) = 0 := by
    dsimp only [X, N]
    rw [LinearMap.neg_apply, map_neg, neg_eq_zero]
    exact second_descendant_coefficient_zero h (r + 2) s (by omega) hs
  exact mixedCoeff_two_zero_of_Q_on_successor (R.op 4)
    (fun k => R.op 5 (N + k)) X (negative_first_second N) (negative_first_theta N)
    (second_theta N) rfl hX2 hQw hQu

/-- The actual full two-theta boundary coefficient for the unique-one
first partition. The cutoff is its clipped sum at multiplicity two. -/
theorem theta_second_two_one
    (h : CV3Rel R w (1, 0) ν ϱ 0) (r s : ℕ)
    (hs : 2 * (ν.1 + ϱ.1) + 1 + clippedSum (parts ϱ.2 ν.2 0) (r + 2) <
      s + (r + 2)) :
    mixedCoeff (R.op 5) (R.op 4) 2 r s w = 0 := by
  apply mixedCoeff_two_zero_of_tail_and_lower (R.op 5) (R.op 4) w (ν.1 + ϱ.1)
    r s (CVRoots.sl2_highest R).hFF
  · intro hNs
    apply shifted_theta_second_two_one h r (s - 2 * (ν.1 + ϱ.1))
    omega
  · intro i hi his
    apply theta_second_one h r (s - i)
    have hc := clippedSum_mono (parts ϱ.2 ν.2 0) (by omega : r + 1 ≤ r + 2)
    change ϱ.1 + ν.1 + 1 + clippedSum (parts ϱ.2 ν.2 0) (r + 1) < s - i + (r + 1)
    omega
  · intro i j hi hj hij
    apply second_coefficient_zero h r (s - i - j)
    have hc := clippedSum_mono (parts ϱ.2 ν.2 0) (by omega : r ≤ r + 2)
    change clippedSum (parts ϱ.2 ν.2 0) r < s - i - j + r
    omega

/-- The no-one relation in the exact clipped-partition boundary format. -/
theorem theta_second_two_no_one_clipped {e : ℕ}
    (h : CV3Rel R w (0, e) ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 0) 2 +
      clippedSum (parts ϱ.2 ν.2 e) (r + 2) < s + (r + 2)) :
    mixedCoeff (R.op 5) (R.op 4) 2 r s w = 0 := by
  apply theta_second_two_no_one h r s
  have hc : clippedSum (parts ϱ.1 ν.1 0) 2 = 2 * (ϱ.1 + ν.1) := by
    rw [clippedSum_parts]
    norm_num
    omega
  rwa [hc] at hs

/-- The unique-one relation in the exact clipped-partition boundary format. -/
theorem theta_second_two_one_clipped
    (h : CV3Rel R w (1, 0) ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 1) 2 +
      clippedSum (parts ϱ.2 ν.2 0) (r + 2) < s + (r + 2)) :
    mixedCoeff (R.op 5) (R.op 4) 2 r s w = 0 := by
  apply theta_second_two_one h r s
  have hc : clippedSum (parts ϱ.1 ν.1 1) 2 = 2 * (ν.1 + ϱ.1) + 1 := by
    rw [clippedSum_parts]
    norm_num
    omega
  rwa [hc] at hs

end
end VOA.DeligneAudit.A2.CVRectPBWTwoTheta

#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.shifted_theta_second_two_no_one
#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.theta_second_two_no_one
#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.shifted_theta_second_two_one
#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.theta_second_two_one
#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.theta_second_two_no_one_clipped
#print axioms VOA.DeligneAudit.A2.CVRectPBWTwoTheta.theta_second_two_one_clipped
