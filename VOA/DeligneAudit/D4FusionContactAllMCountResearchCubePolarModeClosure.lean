import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeModeImage
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePolarModeSeeds
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePolarZeroClosure

/-! Arbitrary negative-current modes preserve the literal quadratic/cubic
polar ideal. Seed preservation precedes, and proves, full ideal stability. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

theorem actual_lower_polar_coeff_mem (m r a b c s ell : ℕ) (d : Fin 3)
    (hr : r = 2 ∨ r = 3) (hs : m < r + s) :
    g0Deriv m (cubeDirection d) ell
      (PowerSeries.coeff s (currentMap m (orbit ℂ r a b c))) ∈
        quadraticCubicPolarIdeal m := by
  rw [actual_lower_orbit_coeff_eq]
  apply iterate_zero_lower_mem m 2 c
  apply iterate_zero_lower_mem m 1 b
  apply iterate_zero_lower_mem m 0 a
  exact actual_lower_highest_coeff_mem_polarIdeal m r s ell d hr hs

/-- Stability of the WHOLE ideal, including every polynomial multiplier.
No stability input is supplied, and no quotient class is differentiated. -/
theorem quadraticCubicPolarIdeal_lower_mode (m : ℕ) (d : Fin 3) (ell : ℕ)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ quadraticCubicPolarIdeal m) :
    g0Deriv m (cubeDirection d) ell p ∈ quadraticCubicPolarIdeal m := by
  change p ∈ Submodule.span _ (quadraticCubicPolarSeeds m) at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨r,a,b,c,s,hr,hs,rfl⟩ := hp
      exact actual_lower_polar_coeff_mem m r a b c s ell d hr hs
  | zero => rw [map_zero]; exact (quadraticCubicPolarIdeal m).zero_mem
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact (quadraticCubicPolarIdeal m).add_mem ihp ihq
  | smul a p hp ih =>
      change g0Deriv m (cubeDirection d) ell (a*p) ∈ quadraticCubicPolarIdeal m
      rw [Derivation.leibniz]
      exact (quadraticCubicPolarIdeal m).add_mem
        (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hp)

def negativeModeWord (m : ℕ) : List (Fin 3 × ℕ) →
    MvPolynomial (Vars m) ℂ → MvPolynomial (Vars m) ℂ
  | [], p => p
  | x::l, p => g0Deriv m (cubeDirection x.1) x.2 (negativeModeWord m l p)

theorem negativeModeWord_mem_polarIdeal (m : ℕ) (l : List (Fin 3 × ℕ))
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ quadraticCubicPolarIdeal m) :
    negativeModeWord m l p ∈ quadraticCubicPolarIdeal m := by
  induction l with
  | nil => exact hp
  | cons x l ih => exact quadraticCubicPolarIdeal_lower_mode m x.1 x.2 ih

theorem negativeModeWord_sub (m : ℕ) (l : List (Fin 3 × ℕ))
    (p q : MvPolynomial (Vars m) ℂ) :
    negativeModeWord m l (p-q) = negativeModeWord m l p - negativeModeWord m l q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change g0Deriv m (cubeDirection x.1) x.2 (negativeModeWord m l (p-q)) = _
      rw [ih,map_sub]
      rfl

theorem negativeModeWord_congr_polarIdeal (m : ℕ) (l : List (Fin 3 × ℕ))
    {p q : MvPolynomial (Vars m) ℂ} (h : p - q ∈ quadraticCubicPolarIdeal m) :
    negativeModeWord m l p - negativeModeWord m l q ∈ quadraticCubicPolarIdeal m := by
  rw [← negativeModeWord_sub]
  exact negativeModeWord_mem_polarIdeal m l h

end
#print axioms actual_lower_polar_coeff_mem
#print axioms quadraticCubicPolarIdeal_lower_mode
#print axioms negativeModeWord_congr_polarIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
