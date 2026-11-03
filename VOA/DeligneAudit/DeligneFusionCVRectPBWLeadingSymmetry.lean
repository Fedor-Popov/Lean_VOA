import VOA.DeligneAudit.DeligneFusionCVRectPBWLeading
import VOA.DeligneAudit.DeligneFusionCVRectFilteredLeading
import VOA.DeligneAudit.DeligneFusionCVRectPBWTwoThetaCurrent
import VOA.DeligneAudit.DeligneFusionCVSymmetry

/-!
# Dynkin symmetry of actual PBW boundary coefficients

The checked Dynkin pullback preserves the actual negative-word filtration.
The highest-root sign is retained when transporting coefficients; reordering
is performed only in the proved commuting graded cyclic representation.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWLeading

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.A2.CVFamily
open VOA.DeligneAudit.A2.CVRectFiltered VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectPBWBoundary VOA.DeligneAudit.A2.CVSymmetry
open VOA.DeligneAudit.A2.CVPolarization VOA.DeligneAudit.A2.CVRectPBWTwoTheta

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

private theorem swap_nword_mem (l : List NegLtr) :
    nword (swapRep R) w l ∈ Pbelow R w (l.length + 1) := by
  induction l with
  | nil => exact Submodule.subset_span ⟨[], by simp, rfl⟩
  | cons x l ih =>
      rcases x with ⟨a, k⟩
      fin_cases a
      · change ((swapRep R).op 3 k) (nword (swapRep R) w l) ∈
          Pbelow R w (l.length + 1 + 1)
        rw [swapRep_op3]
        exact Pbelow_op R w 2 k (l.length + 1) ih
      · change ((swapRep R).op 5 k) (nword (swapRep R) w l) ∈
          Pbelow R w (l.length + 1 + 1)
        rw [swapRep_op5, LinearMap.neg_apply]
        exact (Pbelow R w (l.length + 1 + 1)).neg_mem
          (Pbelow_op R w 1 k (l.length + 1) ih)
      · change ((swapRep R).op 4 k) (nword (swapRep R) w l) ∈
          Pbelow R w (l.length + 1 + 1)
        rw [swapRep_op4]
        exact Pbelow_op R w 0 k (l.length + 1) ih

private theorem Pbelow_swap_le (n : ℕ) : Pbelow (swapRep R) w n ≤ Pbelow R w n := by
  rw [Pbelow, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  exact Pbelow_mono R w (by omega : l.length + 1 ≤ n) (swap_nword_mem R w l)

/-- The checked Dynkin involution preserves the actual PBW filtration. -/
theorem Pbelow_swap (n : ℕ) : Pbelow (swapRep R) w n = Pbelow R w n := by
  apply le_antisymm (Pbelow_swap_le R w n)
  simpa only [swapRep_swapRep] using Pbelow_swap_le (swapRep R) w n

/-- Any proved swapped graded coefficient relation transfers to the original
actual graded representation, with its two simple colors exchanged. -/
theorem gradedOrderedCoeff_zero_of_swap (p q r s : ℕ)
    (hz : gradedOrderedCoeff (swapRep R) w r q p s = 0) :
    gradedOrderedCoeff R w p q r s = 0 := by
  have hm := (orderedCoeff_mem_iff_zero (swapRep R) w r q p s).mpr hz
  rw [Pbelow_swap] at hm
  have hneg : Garland.Fs (fun k => -R.op 5 k) = (-1 : ℂ) • Garland.Fs (R.op 5) := by
    apply PowerSeries.ext
    intro k
    simp [Garland.Fs]
  simp only [orderedCoeff, swapRep_op3, swapRep_op4, swapRep_op5, hneg, smul_pow,
    mul_smul_comm, smul_mul_assoc, PowerSeries.coeff_smul, LinearMap.smul_apply] at hm
  have hm' := ((Pbelow R w (r + q + p)).smul_mem_iff
    (pow_ne_zero q (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)))).mp hm
  have hh := currentProduct_zero_of_mem R w
    (List.replicate r 2 ++ List.replicate q 1 ++ List.replicate p 0) s (by
      simpa only [currentProduct_append, currentProduct_replicate, List.length_append,
        List.length_replicate, negRoot, Matrix.cons_val_two, Matrix.cons_val_one,
        Matrix.cons_val_zero] using hm')
  have hseries (a b : Fin 3) : Commute (Garland.Fs (grOp R w a))
      (Garland.Fs (grOp R w b)) := current_series_commute (grOp_commute R w a b)
  have he : Garland.Fs (grOp R w 2) ^ r * Garland.Fs (grOp R w 1) ^ q *
      Garland.Fs (grOp R w 0) ^ p =
      Garland.Fs (grOp R w 0) ^ p * Garland.Fs (grOp R w 1) ^ q *
        Garland.Fs (grOp R w 2) ^ r := by
    rw [mul_assoc, ← ((hseries 0 1).pow_pow p q).eq, ← mul_assoc,
      ← ((hseries 0 2).pow_pow p r).eq, mul_assoc,
      ← ((hseries 1 2).pow_pow q r).eq, ← mul_assoc]
  simp only [currentProduct_append, currentProduct_replicate] at hh
  change (PowerSeries.coeff s (Garland.Fs (grOp R w 2) ^ r *
    Garland.Fs (grOp R w 1) ^ q * Garland.Fs (grOp R w 0) ^ p)) (grGenerator R w) = 0 at hh
  rw [he] at hh
  exact hh

variable {R w} {ε ν ϱ : Weight}

/-- The mirror of the actual one-first, one-theta boundary family. -/
theorem first_theta_second_mirror (h : CV3Rel R w ε ν ϱ 0) (p s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) (p + 1) +
      clippedSum (parts ϱ.2 ν.2 ε.2) 2 < s + p + 2) :
    gradedOrderedCoeff R w p 1 1 s = 0 := by
  apply gradedOrderedCoeff_zero_of_swap R w p 1 1 s
  apply first_theta_second (cv3Rel_swap h) p s
  simpa only [Prod.fst, Prod.snd, Nat.add_comm] using hs

/-- The exact one-theta source relation in graded coefficient form. -/
theorem theta_second_one_graded (h : CV3Rel R w ε ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) 1 +
      clippedSum (parts ϱ.2 ν.2 ε.2) (r + 1) < s + r + 1) :
    gradedOrderedCoeff R w 0 1 r s = 0 := by
  apply gradedOrderedCoeff_zero R w 0 1 r s
  have hc : clippedSum (parts ϱ.1 ν.1 ε.1) 1 = ϱ.1 + ν.1 + ε.1 := by
    rw [clippedSum_parts]
    norm_num
  have hz := theta_second_one h r s (by rwa [← hc])
  have he : orderedCoeff R w 0 1 r s = 0 := by
    simpa only [orderedCoeff, pow_zero, one_mul, pow_one, mixedCoeff] using hz
  rw [he]
  exact Submodule.zero_mem _

/-- The mirror exact one-theta family. -/
theorem first_theta_one_graded (h : CV3Rel R w ε ν ϱ 0) (p s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 ε.1) (p + 1) +
      clippedSum (parts ϱ.2 ν.2 ε.2) 1 < s + p + 1) :
    gradedOrderedCoeff R w p 1 0 s = 0 := by
  apply gradedOrderedCoeff_zero_of_swap R w p 1 0 s
  apply theta_second_one_graded (cv3Rel_swap h) p s
  simpa only [Prod.fst, Prod.snd, Nat.add_comm] using hs

/-- The two-theta no-first-one source relation in graded form. -/
theorem theta_second_two_no_one_graded {e : ℕ}
    (h : CV3Rel R w (0, e) ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 0) 2 +
      clippedSum (parts ϱ.2 ν.2 e) (r + 2) < s + r + 2) :
    gradedOrderedCoeff R w 0 2 r s = 0 := by
  apply gradedOrderedCoeff_zero R w 0 2 r s
  have hz := theta_second_two_no_one_clipped h r s (by simpa only [Nat.add_assoc] using hs)
  have he : orderedCoeff R w 0 2 r s = 0 := by
    simpa only [orderedCoeff, pow_zero, one_mul, mixedCoeff] using hz
  rw [he]
  exact Submodule.zero_mem _

/-- The unique-first-one two-theta source relation in graded form. -/
theorem theta_second_two_one_graded
    (h : CV3Rel R w (1, 0) ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 1) 2 +
      clippedSum (parts ϱ.2 ν.2 0) (r + 2) < s + r + 2) :
    gradedOrderedCoeff R w 0 2 r s = 0 := by
  apply gradedOrderedCoeff_zero R w 0 2 r s
  have hz := theta_second_two_one_clipped h r s (by simpa only [Nat.add_assoc] using hs)
  have he : orderedCoeff R w 0 2 r s = 0 := by
    simpa only [orderedCoeff, pow_zero, one_mul, mixedCoeff] using hz
  rw [he]
  exact Submodule.zero_mem _

/-- The mirror two-theta family when the second partition has no one. -/
theorem first_theta_two_no_one_graded {e : ℕ}
    (h : CV3Rel R w (e, 0) ν ϱ 0) (p s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 e) (p + 2) +
      clippedSum (parts ϱ.2 ν.2 0) 2 < s + p + 2) :
    gradedOrderedCoeff R w p 2 0 s = 0 := by
  apply gradedOrderedCoeff_zero_of_swap R w p 2 0 s
  apply theta_second_two_no_one_graded (cv3Rel_swap h) p s
  simpa only [Prod.fst, Prod.snd, Nat.add_comm] using hs

/-- The mirror unique-one two-theta family. -/
theorem first_theta_two_one_graded
    (h : CV3Rel R w (0, 1) ν ϱ 0) (p s : ℕ)
    (hs : clippedSum (parts ϱ.1 ν.1 0) (p + 2) +
      clippedSum (parts ϱ.2 ν.2 1) 2 < s + p + 2) :
    gradedOrderedCoeff R w p 2 0 s = 0 := by
  apply gradedOrderedCoeff_zero_of_swap R w p 2 0 s
  apply theta_second_two_one_graded (cv3Rel_swap h) p s
  simpa only [Prod.fst, Prod.snd, Nat.add_comm] using hs

end
end VOA.DeligneAudit.A2.CVRectPBWLeading

#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.Pbelow_swap
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.gradedOrderedCoeff_zero_of_swap
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.first_theta_second_mirror
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.first_theta_one_graded
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.first_theta_two_no_one_graded
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.first_theta_two_one_graded
