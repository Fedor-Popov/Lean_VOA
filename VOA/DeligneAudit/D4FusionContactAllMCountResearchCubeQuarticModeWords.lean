import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePolarModeClosure
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticModeStep
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeVariablePowerSlots

/-! Actual negative-current words on admissible quartic U polars reduce modulo
the literal quadratic/cubic ideal to a static polar at the summed current index. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Transport the highest one-step relation through the three proved zero-mode
strings, commuting only on the explicit whole pure-A coefficient image. -/
theorem quartic_polar_mode_step_mem_polarIdeal
    (m a b c s ell : ℕ) (d : Fin 3) (hs : m < 4 + s) :
    g0Deriv m (cubeDirection d) ell
        (PowerSeries.coeff s (currentMap m (orbit ℂ 4 a b c))) -
      g0Deriv m (cubeDirection d) 0
        (PowerSeries.coeff (s + ell) (currentMap m (orbit ℂ 4 a b c))) ∈
      quadraticCubicPolarIdeal m := by
  rw [actual_lower_orbit_coeff_eq m 4 a b c s ell d,
    actual_lower_orbit_coeff_eq m 4 a b c (s + ell) 0 d]
  have h := iterate_zero_lower_mem m 2 c
    (iterate_zero_lower_mem m 1 b (iterate_zero_lower_mem m 0 a
      (quartic_highest_mode_step_mem_polarIdeal m s ell d hs)))
  simpa only [VariablePower.iterate_deriv_sub] using h

/-- The exact number of letters in a given cube-lowering direction. -/
def negativeModeAxisCount (d : Fin 3) : List (Fin 3 × ℕ) → ℕ
  | [] => 0
  | x::l => (if x.1 = d then 1 else 0) + negativeModeAxisCount d l

private theorem polar_difference_trans (m : ℕ) {p q r : MvPolynomial (Vars m) ℂ}
    (hp : p - q ∈ quadraticCubicPolarIdeal m)
    (hq : q - r ∈ quadraticCubicPolarIdeal m) :
    p - r ∈ quadraticCubicPolarIdeal m := by
  have he : p - r = (p - q) + (q - r) := by ring
  rw [he]
  exact (quadraticCubicPolarIdeal m).add_mem hp hq

/-- All actual negative-current words reduce to one original static quartic
polar. Both the current index and each lowering count are retained exactly. -/
theorem quartic_negativeModeWord_static_mem_polarIdeal
    (m s a b c : ℕ) (l : List (Fin 3 × ℕ)) (hs : m < 4 + s) :
    negativeModeWord m l (PowerSeries.coeff s (currentMap m (orbit ℂ 4 a b c))) -
      PowerSeries.coeff (s + (l.map Prod.snd).sum)
        (currentMap m (orbit ℂ 4 (a + negativeModeAxisCount 0 l)
          (b + negativeModeAxisCount 1 l) (c + negativeModeAxisCount 2 l))) ∈
      quadraticCubicPolarIdeal m := by
  induction l with
  | nil =>
      simp only [negativeModeWord,negativeModeAxisCount,List.map_nil,List.sum_nil,
        Nat.add_zero,sub_self]
      exact (quadraticCubicPolarIdeal m).zero_mem
  | cons x l ih =>
      rcases x with ⟨d,ell⟩
      let t := s + (l.map Prod.snd).sum
      let a' := a + negativeModeAxisCount 0 l
      let b' := b + negativeModeAxisCount 1 l
      let c' := c + negativeModeAxisCount 2 l
      have hpres :
          g0Deriv m (cubeDirection d) ell
              (negativeModeWord m l
                (PowerSeries.coeff s (currentMap m (orbit ℂ 4 a b c)))) -
            g0Deriv m (cubeDirection d) ell
              (PowerSeries.coeff t (currentMap m (orbit ℂ 4 a' b' c'))) ∈
          quadraticCubicPolarIdeal m := by
        simpa only [negativeModeWord] using
          negativeModeWord_congr_polarIdeal m [(d,ell)] ih
      have hstep := quartic_polar_mode_step_mem_polarIdeal m a' b' c' t ell d
        (by dsimp [t]; omega)
      have hsum := polar_difference_trans m hpres hstep
      rw [actual_zero_polar_coefficient] at hsum
      fin_cases d <;>
        simpa [negativeModeWord,negativeModeAxisCount,polarZeroStep,t,a',b',c',
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hsum

end
#print axioms quartic_polar_mode_step_mem_polarIdeal
#print axioms quartic_negativeModeWord_static_mem_polarIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
