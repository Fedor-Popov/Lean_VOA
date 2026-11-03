import VOA.DeligneAudit.DeligneFusionCVRectPolynomialCurrent
import VOA.DeligneAudit.DeligneFusionCVRectCommutative

/-!
# A uniform mixed-current boundary relation from actual CV source data

The theta/second-root coefficient with one theta factor is already zero in the
module. Commuting a high first-root mode through a second-root CV coefficient
produces its shifted theta tail. The missing low theta modes multiply vanishing
second-root coefficients. No PBW initial-ideal inclusion is assumed here.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWBoundary

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.CVsl2 VOA.DeligneAudit.CVPart
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVPolarization
open VOA.DeligneAudit.A2.CVRectPolynomial VOA.DeligneAudit.A2.CVRectCommutative

noncomputable section

section Series

variable {A : Type*} [Semiring A]

/-- Split a series into its finite prefix and its coefficient tail. -/
theorem series_prefix_tail (F : ℕ → A) (N : ℕ) :
    PowerSeries.mk F = (finiteCurrent N F : PowerSeries A) +
      PowerSeries.X ^ N * PowerSeries.mk (fun k => F (N + k)) := by
  apply PowerSeries.ext
  intro j
  rw [map_add, PowerSeries.coeff_mk, Polynomial.coeff_coe,
    PowerSeries.coeff_X_pow_mul']
  by_cases hj : N ≤ j
  · rw [if_pos hj, finiteCurrent_coeff_ge N F j hj, zero_add, PowerSeries.coeff_mk,
      Nat.add_sub_of_le hj]
  · rw [if_neg hj, finiteCurrent_coeff_lt N F j (by omega), add_zero]

/-- The optimized root coefficient cutoff is monotone in multiplicity. -/
theorem clippedSum_mono (ξ : List ℕ) : Monotone (clippedSum ξ) := by
  intro a b hab
  induction ξ with
  | nil => simp [clippedSum]
  | cons k ξ ih =>
      simp only [clippedSum, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (min_le_min hab le_rfl) ih

end Series

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule bracketTable V} {w : V} {ε ν ϱ : Weight}

/-- All second-root coefficients beyond their optimized CV cutoff vanish,
including the multiplicity-zero polynomial coefficient case. -/
theorem second_coefficient_zero (h : CV3Rel R w ε ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.2 ν.2 ε.2) r < s + r) :
    Q (R.op 4) r s w = 0 := by
  by_cases hr : r = 0
  · subst r
    have hs0 : 0 < s := by simpa [clippedSum] using hs
    simp [Q, hs0.ne']
  · obtain ⟨k, hk⟩ := parts_region_optimizer ϱ.2 ν.2 ε.2 r (by omega)
    have hCV : CVRel (R.op 4) (parts ϱ.2 ν.2 ε.2) w := by
      simpa only [Nat.add_zero] using h.second
    exact hCV r s k (by omega) (by omega)

private theorem first_high_zero (h : CV3Rel R w ε ν ϱ 0) :
    R.op 3 (ϱ.1 + ν.1 + ε.1) w = 0 := by
  apply trunc_of_cvrel h.first
  simp [parts_length]

/-- A high first-root mode polarizes a second-root coefficient into its
shifted theta/second-root coefficient. -/
theorem shifted_theta_second_zero (h : CV3Rel R w ε ν ϱ 0) (r s : ℕ)
    (hs : clippedSum (parts ϱ.2 ν.2 ε.2) (r + 1) < s + (r + 1)) :
    mixedCoeff (fun k => R.op 5 (ϱ.1 + ν.1 + ε.1 + k)) (R.op 4) 1 r s w = 0 := by
  let N := ϱ.1 + ν.1 + ε.1
  let G := fun k => R.op 5 (N + k)
  have hQ := second_coefficient_zero h (r + 1) s hs
  apply mixedCoeff_zero_of_Q (R.op 4) G (-R.op 3 N) ?_ ?_ ?_ ?_ hQ 1 r (by omega)
  · intro k
    calc
      (-R.op 3 N) * R.op 4 k - R.op 4 k * (-R.op 3 N) =
          -(R.op 3 N * R.op 4 k - R.op 4 k * R.op 3 N) := by noncomm_ring
      _ = G k := by rw [op_comm_end]; simp [G, Fin.sum_univ_eight, bracketTable]
  · intro k
    rw [neg_mul, mul_neg, neg_inj, ← sub_eq_zero, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
  · intro i k
    rw [← sub_eq_zero, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
  · simpa only [LinearMap.neg_apply, neg_eq_zero] using first_high_zero h

/-- The entire one-theta boundary coefficient vanishes in the actual module.
The first auxiliary partition enters only through its length. -/
theorem theta_second_one (h : CV3Rel R w ε ν ϱ 0) (r s : ℕ)
    (hs : ϱ.1 + ν.1 + ε.1 + clippedSum (parts ϱ.2 ν.2 ε.2) (r + 1) < s + (r + 1)) :
    mixedCoeff (R.op 5) (R.op 4) 1 r s w = 0 := by
  let N := ϱ.1 + ν.1 + ε.1
  let Y := R.op 5
  let Z := R.op 4
  have hprefix : PowerSeries.coeff s
      ((finiteCurrent N Y : PowerSeries (Module.End ℂ V)) * Garland.Fs Z ^ r) w = 0 := by
    simp only [PowerSeries.coeff_mul, LinearMap.sum_apply, Module.End.mul_apply]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    have hij' : i + j = s := Finset.mem_antidiagonal.mp hij
    rw [Polynomial.coeff_coe]
    by_cases hi : i < N
    · rw [finiteCurrent_coeff_lt N Y i hi]
      have hclip := clippedSum_mono (parts ϱ.2 ν.2 ε.2) (by omega : r ≤ r + 1)
      have hz : Q Z r j w = 0 := second_coefficient_zero h r j (by dsimp [N] at hi; omega)
      change Y i (Q Z r j w) = 0
      rw [hz, map_zero]
    · rw [finiteCurrent_coeff_ge N Y i (by omega), LinearMap.zero_apply]
  have htail : PowerSeries.coeff s
      ((PowerSeries.X : PowerSeries (Module.End ℂ V)) ^ N *
        (PowerSeries.mk (fun k => Y (N + k)) * Garland.Fs Z ^ r)) w = 0 := by
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with hNs
    · simpa only [mixedCoeff, pow_one, Garland.Fs] using
        shifted_theta_second_zero h r (s - N) (by dsimp [N] at hNs; omega)
    · exact LinearMap.zero_apply w
  simp only [mixedCoeff, pow_one]
  change PowerSeries.coeff s (Garland.Fs Y * Garland.Fs Z ^ r) w = 0
  rw [show Garland.Fs Y = (finiteCurrent N Y : PowerSeries (Module.End ℂ V)) +
    PowerSeries.X ^ N * PowerSeries.mk (fun k => Y (N + k)) from series_prefix_tail Y N,
    add_mul, mul_assoc, map_add, LinearMap.add_apply, hprefix, htail, add_zero]

end
end VOA.DeligneAudit.A2.CVRectPBWBoundary

#print axioms VOA.DeligneAudit.A2.CVRectPBWBoundary.series_prefix_tail
#print axioms VOA.DeligneAudit.A2.CVRectPBWBoundary.shifted_theta_second_zero
#print axioms VOA.DeligneAudit.A2.CVRectPBWBoundary.theta_second_one
