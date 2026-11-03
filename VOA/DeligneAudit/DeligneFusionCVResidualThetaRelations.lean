import VOA.DeligneAudit.DeligneFusionCVRectPBWLeadingSymmetry

/-!
# Actual PBW boundary sources for the residual theta family

A residual highest-root part two is stronger than two final parts one.
Its sharp theta truncation also gives the top first-root descendant a
full opposite-root partition with a final part two. These proved source
relations supply the two-theta boundary despite the two simple ones.
-/

namespace VOA.DeligneAudit.A2.CVResidualThetaRelations

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectPBWBoundary VOA.DeligneAudit.A2.CVRectPBWTwoTheta
open VOA.DeligneAudit.A2.CVRectPBWLeading VOA.DeligneAudit.A2.CVRectFiltered
open VOA.DeligneAudit.A2.CVPolarization VOA.DeligneAudit.A2.CVSymmetry

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ϱ : Weight}

/-- Replacing one final part two by two parts one weakens the tail conditions. -/
theorem tail_two_le_two_ones (r k : ℕ) :
    T k (parts r 1 0) ≤ T k (parts r 0 2) := by
  simp only [parts, T_append, T_replicate, List.length_append, List.length_replicate,
    Nat.add_zero, Nat.mul_one]
  omega

/-- The residual source supplies the weaker auxiliary presentation with both
simple epsilon coordinates one, while retaining its stronger theta relation. -/
theorem weaken (h : CV3Rel R w (0, 0) (0, 0) ϱ 1) :
    CV3Rel R w (1, 1) (0, 0) ϱ 0 := by
  refine ⟨h.raising, h.cartan_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Prod.fst, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.add_comm]
      using h.cartan_first
  · simpa only [Prod.snd, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.add_comm]
      using h.cartan_second
  · simpa only [Prod.fst, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.add_comm]
      using h.lowering_first
  · simpa only [Prod.snd, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.add_comm]
      using h.lowering_second
  · simpa only [Prod.fst, Nat.zero_add, Nat.add_zero] using h.first
  · simpa only [Prod.snd, Nat.zero_add, Nat.add_zero] using h.second
  · intro m s k hm hreg
    have ht := tail_two_le_two_ones (ϱ.1 + ϱ.2) k
    change 1 + m * k + T k (parts (ϱ.1 + ϱ.2) 0 2) ≤ s + m at hreg
    apply h.highest m s k hm
    simpa only [Prod.fst, Prod.snd, Nat.zero_add] using
      (show 1 + m * k + T k (parts (ϱ.1 + ϱ.2) 1 0) ≤ s + m by omega)

/-- The source theta partition truncates one mode earlier than its weakening. -/
theorem theta_high (h : CV3Rel R w (0, 0) (0, 0) ϱ 1)
    (q : ℕ) (hq : ϱ.1 + ϱ.2 + 1 ≤ q) : R.op 5 q w = 0 := by
  apply trunc_of_cvrel h.highest
  simp only [parts_length, Nat.zero_add]
  exact hq

/-- The source simple final one gives the top first-root square. -/
theorem first_square (h : CV3Rel R w (0, 0) (0, 0) ϱ 1) :
    (R.op 3 ϱ.1 ^ 2) w = 0 := by
  have hCV : CVRel (R.op 3) (parts ϱ.1 0 1) w := by simpa using h.first
  simpa only [Nat.add_zero, Nat.add_sub_cancel_right] using
    top_square_of_cvrel (CVRoots.sl2_first R).hFF (by omega : 1 ≤ 1) hCV

/-- The strong theta truncation kills all high opposite modes on the descendant. -/
theorem descendant_second_high (h : CV3Rel R w (0, 0) (0, 0) ϱ 1)
    (q : ℕ) (hq : ϱ.2 + 1 ≤ q) : R.op 4 q (R.op 3 ϱ.1 w) = 0 := by
  have hF : R.op 4 q w = 0 := by
    apply trunc_of_cvrel h.second
    simp only [parts_length, Nat.add_zero, Nat.zero_add]
    exact hq
  have hY := theta_high h (q + ϱ.1) (by omega)
  rw [comm_apply]
  simp [Fin.sum_univ_eight, bracketTable, hF, hY]

/-- The top first-root descendant has the actual opposite partition
`3^rho₂,2`; its quadratic relations follow from the proved high-mode cutoff. -/
theorem descendant_second_cv (h : CV3Rel R w (0, 0) (0, 0) ϱ 1) :
    CVRel (R.op 4) (parts ϱ.2 1 0) (R.op 3 ϱ.1 w) := by
  have hw := weaken h
  apply cvrel_parts123 ϱ.2 1 0 (CVRoots.sl2_second R)
  · intro s
    rw [comm_apply]
    simp [Fin.sum_univ_eight, bracketTable, h.raising 1 (by decide) s]
  · intro s hs
    simpa only [Prod.fst, Nat.zero_add, Nat.add_zero, Nat.add_sub_cancel_right] using
      CVKernelGeneralHW.first_cartan_pos hw 7 (by decide) s hs
  · have hn := CVKernelGeneralHW.first_lowering_second hw
    rw [← Module.End.pow_apply] at hn
    convert hn using 1
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.add_sub_cancel_right]
    congr 2
    omega
  · intro q hq
    exact descendant_second_high h q (by omega)
  · intro s hs
    exact Q_high (CVRoots.sl2_second R).hFF (descendant_second_high h) 2 s
      (by omega)

/-- At multiplicity at least two, the descendant cutoff is exactly one unit
beyond the weakened source opposite partition. -/
theorem descendant_second_coefficient (h : CV3Rel R w (0, 0) (0, 0) ϱ 1)
    (m s : ℕ) (hm : 2 ≤ m)
    (hs : clippedSum (parts ϱ.2 0 1) m + 1 < s + m) :
    Q (R.op 4) m s (R.op 3 ϱ.1 w) = 0 := by
  apply coefficient_zero_of_cvrel_parts (descendant_second_cv h) m s
  simpa only [clippedSum_parts, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.one_mul,
    Nat.min_eq_right hm, Nat.min_eq_right (by omega : 1 ≤ m)] using hs

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

/-- The two-theta successor argument uses the actual descendant CV relation. -/
theorem shifted_theta_second_two (h : CV3Rel R w (0, 0) (0, 0) ϱ 1)
    (r s : ℕ) (hs : clippedSum (parts ϱ.2 0 1) (r + 2) + 1 < s + (r + 2)) :
    mixedCoeff (fun k => R.op 5 (ϱ.1 + k)) (R.op 4) 2 r s w = 0 := by
  let X := -R.op 3 ϱ.1
  have hX2 : X (X w) = 0 := by
    dsimp only [X]
    simpa only [LinearMap.neg_apply, map_neg, neg_neg, pow_two, Module.End.mul_apply]
      using first_square h
  have hQw : Q (R.op 4) (r + 2) s w = 0 :=
    second_coefficient_zero (weaken h) (r + 2) s (by
      change clippedSum (parts ϱ.2 0 1) (r + 2) < s + (r + 2)
      omega)
  have hQu : Q (R.op 4) (r + 2) s (X w) = 0 := by
    dsimp only [X]
    rw [LinearMap.neg_apply, map_neg, neg_eq_zero]
    exact descendant_second_coefficient h (r + 2) s (by omega) hs
  exact mixedCoeff_two_zero_of_Q_on_successor (R.op 4)
    (fun k => R.op 5 (ϱ.1 + k)) X (negative_first_second ϱ.1)
    (negative_first_theta ϱ.1) (second_theta ϱ.1) rfl hX2 hQw hQu

/-- The full exact two-theta boundary for the residual family. -/
theorem theta_second_two (h : CV3Rel R w (0, 0) (0, 0) ϱ 1) (r s : ℕ)
    (hs : clippedSum (parts ϱ.1 0 1) 2 +
      clippedSum (parts ϱ.2 0 1) (r + 2) < s + (r + 2)) :
    mixedCoeff (R.op 5) (R.op 4) 2 r s w = 0 := by
  have hw := weaken h
  have hc : clippedSum (parts ϱ.1 0 1) 2 = 2 * ϱ.1 + 1 := by
    rw [clippedSum_parts]
    norm_num
    omega
  rw [hc] at hs
  apply mixedCoeff_two_zero_of_tail_and_lower (R.op 5) (R.op 4) w ϱ.1
    r s (CVRoots.sl2_highest R).hFF
  · intro hNs
    apply shifted_theta_second_two h r (s - 2 * ϱ.1)
    omega
  · intro i hi his
    apply theta_second_one hw r (s - i)
    have hm := clippedSum_mono (parts ϱ.2 0 1) (by omega : r + 1 ≤ r + 2)
    change ϱ.1 + 1 + clippedSum (parts ϱ.2 0 1) (r + 1) < s - i + (r + 1)
    omega
  · intro i j hi hj hij
    apply second_coefficient_zero hw r (s - i - j)
    have hm := clippedSum_mono (parts ϱ.2 0 1) (by omega : r ≤ r + 2)
    change clippedSum (parts ϱ.2 0 1) r < s - i - j + r
    omega

/-- The exact residual source relation in the actual graded representation. -/
theorem theta_second_two_graded (h : CV3Rel R w (0, 0) (0, 0) ϱ 1) (r s : ℕ)
    (hs : clippedSum (parts ϱ.1 0 1) 2 +
      clippedSum (parts ϱ.2 0 1) (r + 2) < s + r + 2) :
    gradedOrderedCoeff R w 0 2 r s = 0 := by
  apply gradedOrderedCoeff_zero R w 0 2 r s
  have hz := theta_second_two h r s (by simpa only [Nat.add_assoc] using hs)
  have he : orderedCoeff R w 0 2 r s = 0 := by
    simpa only [orderedCoeff, pow_zero, one_mul, mixedCoeff] using hz
  rw [he]
  exact Submodule.zero_mem _

/-- Dynkin symmetry gives the residual opposite two-theta boundary. -/
theorem first_theta_two_graded (h : CV3Rel R w (0, 0) (0, 0) ϱ 1) (p s : ℕ)
    (hs : clippedSum (parts ϱ.1 0 1) (p + 2) +
      clippedSum (parts ϱ.2 0 1) 2 < s + p + 2) :
    gradedOrderedCoeff R w p 2 0 s = 0 := by
  apply gradedOrderedCoeff_zero_of_swap R w p 2 0 s
  apply theta_second_two_graded (cv3Rel_swap h) p s
  simpa only [Prod.fst, Prod.snd, Nat.add_comm] using hs

end
end VOA.DeligneAudit.A2.CVResidualThetaRelations

#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.weaken
#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.descendant_second_cv
#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.theta_second_two
#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.first_theta_two_graded
