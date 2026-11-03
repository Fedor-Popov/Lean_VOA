import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePolarModeSeeds

/-! The exact quartic highest-seed mode step modulo the literal quadratic/cubic
ideal. All finite-boundary terms are retained as admissible cubic coefficients. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- An arbitrary-mode lowering differs from the shifted zero-mode lowering by
a literal quadratic/cubic ideal member. This step does not assume ideal closure. -/
theorem quartic_highest_mode_step_mem_polarIdeal
    (m s ell : ℕ) (d : Fin 3) (hs : m < 4 + s) :
    g0Deriv m (cubeDirection d) ell (PowerSeries.coeff s (AllM.current m 0 ^ 4)) -
      g0Deriv m (cubeDirection d) 0
        (PowerSeries.coeff (s + ell) (AllM.current m 0 ^ 4)) ∈
      quadraticCubicPolarIdeal m := by
  rw [actual_lower_highest_coeff_recurrence m 3 s ell d,
    sub_right_comm,sub_self,zero_sub]
  apply (quadraticCubicPolarIdeal m).neg_mem
  exact (quadraticCubicPolarIdeal m).nsmul_mem (by
    apply Submodule.sum_mem
    intro a ha
    have ha' : a < ell := Finset.mem_range.mp ha
    exact (quadraticCubicPolarIdeal m).mul_mem_left _
      (highest_coeff_mem_polarIdeal m 3 (s + ell - a) (Or.inr rfl) (by omega))) 4

end
#print axioms quartic_highest_mode_step_mem_polarIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
