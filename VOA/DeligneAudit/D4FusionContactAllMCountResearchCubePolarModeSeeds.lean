import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeModeRecurrence
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishing

/-! Arbitrary negative-current modes on admissible highest quadratic/cubic
seeds land in the literal lower ideal. No ideal-stability premise is used. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- A highest whole coefficient is the zero-lowering member of the literal family. -/
theorem highest_coeff_mem_polarIdeal (m r s : ℕ) (hr : r = 2 ∨ r = 3)
    (hs : m < r + s) :
    PowerSeries.coeff s (AllM.current m 0 ^ r) ∈ quadraticCubicPolarIdeal m := by
  simpa only [currentMap_orbit,Function.iterate_zero_apply] using
    quadraticCubicPolar_coeff_mem m r 0 0 0 s hr hs

/-- The mode-zero lowering is an explicit whole orbit polar, not a closure assumption. -/
theorem actual_zero_lower_highest_coeff_mem_polarIdeal
    (m r s : ℕ) (d : Fin 3) (hr : r = 2 ∨ r = 3) (hs : m < r + s) :
    g0Deriv m (cubeDirection d) 0 (PowerSeries.coeff s (AllM.current m 0 ^ r)) ∈
      quadraticCubicPolarIdeal m := by
  fin_cases d
  · have h := quadraticCubicPolar_coeff_mem m r 1 0 0 s hr hs
    rw [currentMap_orbit,coeff_current_iterate,coeff_current_iterate,
      coeff_current_iterate] at h
    simpa only [Function.iterate_zero_apply,Function.iterate_one] using h
  · have h := quadraticCubicPolar_coeff_mem m r 0 1 0 s hr hs
    rw [currentMap_orbit,coeff_current_iterate,coeff_current_iterate,
      coeff_current_iterate] at h
    simpa only [Function.iterate_zero_apply,Function.iterate_one] using h
  · have h := quadraticCubicPolar_coeff_mem m r 0 0 1 s hr hs
    rw [currentMap_orbit,coeff_current_iterate,coeff_current_iterate,
      coeff_current_iterate] at h
    simpa only [Function.iterate_zero_apply,Function.iterate_one] using h

/-- Exact truncation of the linear lower tail in the quadratic recurrence. -/
theorem highest_linear_coeff_eq_zero (m t : ℕ) (ht : m ≤ t) :
    PowerSeries.coeff t (AllM.current m 0 ^ 1) = 0 := by
  have hnot : ¬t < m := by omega
  simp only [pow_one,AllM.current,PowerSeries.coeff_mk,modeX,dif_neg hnot]

/-- Every negative-current mode sends each admissible HIGHEST quadratic or cubic
coefficient into the literal quadratic/cubic ideal. The lower tails are handled
before any attempt to prove closure of that ideal. -/
theorem actual_lower_highest_coeff_mem_polarIdeal
    (m r s ell : ℕ) (d : Fin 3) (hr : r = 2 ∨ r = 3) (hs : m < r + s) :
    g0Deriv m (cubeDirection d) ell (PowerSeries.coeff s (AllM.current m 0 ^ r)) ∈
      quadraticCubicPolarIdeal m := by
  rcases hr with rfl | rfl
  · rw [actual_lower_highest_coeff_recurrence m 1 s ell d]
    apply (quadraticCubicPolarIdeal m).sub_mem
    · exact actual_zero_lower_highest_coeff_mem_polarIdeal m 2 (s + ell) d
        (Or.inl rfl) (by omega)
    · exact (quadraticCubicPolarIdeal m).nsmul_mem (by
        apply Submodule.sum_mem
        intro a ha
        have ha' : a < ell := Finset.mem_range.mp ha
        rw [highest_linear_coeff_eq_zero m (s + ell - a) (by omega),mul_zero]
        exact (quadraticCubicPolarIdeal m).zero_mem) 2
  · rw [actual_lower_highest_coeff_recurrence m 2 s ell d]
    apply (quadraticCubicPolarIdeal m).sub_mem
    · exact actual_zero_lower_highest_coeff_mem_polarIdeal m 3 (s + ell) d
        (Or.inr rfl) (by omega)
    · exact (quadraticCubicPolarIdeal m).nsmul_mem (by
        apply Submodule.sum_mem
        intro a ha
        have ha' : a < ell := Finset.mem_range.mp ha
        exact (quadraticCubicPolarIdeal m).mul_mem_left _
          (highest_coeff_mem_polarIdeal m 2 (s + ell - a) (Or.inl rfl) (by omega))) 3

end
#print axioms highest_coeff_mem_polarIdeal
#print axioms actual_zero_lower_highest_coeff_mem_polarIdeal
#print axioms highest_linear_coeff_eq_zero
#print axioms actual_lower_highest_coeff_mem_polarIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
