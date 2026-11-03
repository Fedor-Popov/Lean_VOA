import VOA.DeligneAudit.DeligneFusionCVRectPBWBoundary
import VOA.DeligneAudit.DeligneFusionCVKernelGeneralHW
import VOA.DeligneAudit.DeligneFusionCVShort

/-!
# The unique-one descendant's actual opposite-root CV relation

When the first auxiliary epsilon is one and the second is zero, the top
first-root descendant has second-root partition `mu ++ [1]`. This uses only
actual source relations: opposite raising commutation, sharp zero-mode nil,
the theta truncation, and the square of the last retained opposite mode.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWBoundary

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectCommutative

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ν ϱ : Weight}

/-- The unique final first-root part one gives its actual top square relation. -/
theorem first_descendant_square (h : CV3Rel R w (1, 0) ν ϱ 0) :
    (R.op 3 (ν.1 + ϱ.1) ^ 2) w = 0 := by
  have hCV : CVRel (R.op 3) (parts ϱ.1 ν.1 1) w := by simpa using h.first
  simpa only [Nat.add_sub_cancel_right, Nat.add_comm ϱ.1 ν.1] using
    top_square_of_cvrel (CVRoots.sl2_first R).hFF (by omega : 1 ≤ 1) hCV

/-- The opposite-root highest-weight relation needs no first-root weight subtraction. -/
theorem first_descendant_second_raising (h : CV3Rel R w (1, 0) ν ϱ 0) (s : ℕ) :
    R.op 1 s (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  rw [comm_apply]
  simp [Fin.sum_univ_eight, bracketTable, h.raising 1 (by decide) s]

theorem first_descendant_second_cartan (h : CV3Rel R w (1, 0) ν ϱ 0)
    (s : ℕ) (hs : 1 ≤ s) :
    R.op 7 s (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  simpa only [Nat.add_zero, Nat.add_sub_cancel_right] using
    CVKernelGeneralHW.first_cartan_pos h 7 (by decide) s hs

theorem first_descendant_second_nil (h : CV3Rel R w (1, 0) ν ϱ 0) :
    (R.op 4 0 ^ (3 * ϱ.2 + 2 * ν.2 + 2)) (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  have hn := CVKernelGeneralHW.first_lowering_second h
  rw [← Module.End.pow_apply] at hn
  convert hn using 1
  congr 2
  omega

theorem first_descendant_second_trunc (h : CV3Rel R w (1, 0) ν ϱ 0)
    (s : ℕ) (hs : ϱ.2 + ν.2 + 1 ≤ s) :
    R.op 4 s (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  have hZ : R.op 4 s w = 0 := by
    apply trunc_of_cvrel h.second
    simp only [parts_length]
    omega
  have hY : R.op 5 (s + (ν.1 + ϱ.1)) w = 0 := by
    apply trunc_of_cvrel h.highest
    simp only [parts_length]
    omega
  rw [comm_apply]
  simp [Fin.sum_univ_eight, bracketTable, hZ, hY]

theorem first_descendant_second_square (h : CV3Rel R w (1, 0) ν ϱ 0) :
    (R.op 4 (ϱ.2 + ν.2) ^ 2) (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  let B := ϱ.2 + ν.2
  let a := ν.1 + ϱ.1
  have hZ : R.op 4 B w = 0 := by
    apply trunc_of_cvrel h.second
    simp [parts_length, B]
  have hu : R.op 4 B (R.op 3 a w) = R.op 5 (B + a) w := by
    rw [comm_apply]
    simp [Fin.sum_univ_eight, bracketTable, hZ]
  rw [pow_two, Module.End.mul_apply, hu, op4_op5, hZ, map_zero]

/-- The unique-one first-root descendant has the full actual second-root
CV relation with one final part one. -/
theorem second_cv_first_descendant (h : CV3Rel R w (1, 0) ν ϱ 0) :
    CVRel (R.op 4) (parts ϱ.2 ν.2 1) (R.op 3 (ν.1 + ϱ.1) w) := by
  apply cvrel_parts32_one ϱ.2 ν.2 (CVRoots.sl2_second R)
    (first_descendant_second_raising h) (first_descendant_second_cartan h)
    (first_descendant_second_nil h) (first_descendant_second_trunc h)
    (first_descendant_second_square h)

/-- A rootwise parts-one-two-three CV relation gives the exact optimized
coefficient cutoff without any ambient dimension assumption. -/
theorem coefficient_zero_of_cvrel_parts {F : ℕ → Module.End ℂ V} {u : V}
    {r n e : ℕ} (hCV : CVRel F (parts r n e) u) (m s : ℕ)
    (hs : clippedSum (parts r n e) m < s + m) : Q F m s u = 0 := by
  by_cases hm : m = 0
  · subst m
    have hs0 : 0 < s := by simpa [clippedSum] using hs
    simp [Q, hs0.ne']
  · obtain ⟨k, hk⟩ := parts_region_optimizer r n e m (by omega)
    exact hCV m s k (by omega) (by omega)

/-- The descendant coefficient cutoff is one unit beyond the original
opposite partition, uniformly at every positive multiplicity. -/
theorem second_descendant_coefficient_zero (h : CV3Rel R w (1, 0) ν ϱ 0)
    (m s : ℕ) (hm : 1 ≤ m)
    (hs : clippedSum (parts ϱ.2 ν.2 0) m + 1 < s + m) :
    Q (R.op 4) m s (R.op 3 (ν.1 + ϱ.1) w) = 0 := by
  apply coefficient_zero_of_cvrel_parts (second_cv_first_descendant h) m s
  simpa only [clippedSum_parts, Nat.mul_zero, Nat.mul_one, Nat.min_eq_right hm,
    Nat.one_mul, Nat.zero_mul, Nat.add_zero] using hs

end
end VOA.DeligneAudit.A2.CVRectPBWBoundary

#print axioms VOA.DeligneAudit.A2.CVRectPBWBoundary.first_descendant_square
#print axioms VOA.DeligneAudit.A2.CVRectPBWBoundary.second_cv_first_descendant
#print axioms VOA.DeligneAudit.A2.CVRectPBWBoundary.second_descendant_coefficient_zero
