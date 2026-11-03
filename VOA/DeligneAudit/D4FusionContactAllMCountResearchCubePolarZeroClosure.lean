import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePolarZeroClosureOrbit
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeVariablePolarIdeal

/-! Zero-mode preservation of literal static polar ideals, derived from
next-polar identities and the ideal-span Leibniz rule, without closure premises. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Derivation preservation of an ideal span follows from its generator images. -/
theorem polar_ideal_span_derivation_closed {K A : Type*}
    [CommRing K] [CommRing A] [Algebra K A] (D : Derivation K A A) (S : Set A)
    (hS : ∀ p ∈ S, D p ∈ Ideal.span S) {p : A} (hp : p ∈ Ideal.span S) :
    D p ∈ Ideal.span S := by
  change p ∈ Submodule.span A S at hp
  induction hp using Submodule.span_induction with
  | mem p hp => exact hS p hp
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add p q hp hq ihp ihq => rw [map_add]; exact Ideal.add_mem _ ihp ihq
  | smul a p hp ih =>
      change D (a * p) ∈ Ideal.span S
      rw [D.leibniz]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hp)

/-- The original zero-mode current sends a whole static polar coefficient
exactly to the next static polar, with power and coefficient index unchanged. -/
theorem actual_zero_polar_coefficient (m : ℕ) (d : Fin 3) (r a b c s : ℕ) :
    g0Deriv m (cubeDirection d) 0
        (PowerSeries.coeff s (currentMap m (orbit ℂ r a b c))) =
      PowerSeries.coeff s (currentMap m (polarZeroStep ℂ d r a b c)) := by
  rw [← seriesDerivation_coeff,← currentMap_lower]
  change PowerSeries.coeff s (currentMap m (orderLower ℂ d (orbit ℂ r a b c))) = _
  rw [orderLower_orbit_step]

theorem consecutivePolar_seed_zero_mem (m n : ℕ) (d : Fin 3)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ consecutivePolarSeeds m n) :
    g0Deriv m (cubeDirection d) 0 p ∈ consecutivePolarIdeal m n := by
  obtain ⟨r,a,b,c,s,hr,hs,rfl⟩ := hp
  rw [actual_zero_polar_coefficient]
  fin_cases d
  · change PowerSeries.coeff s (currentMap m (orbit ℂ r (a + 1) b c)) ∈ _
    exact consecutivePolar_coeff_mem m n r (a + 1) b c s hr hs
  · change PowerSeries.coeff s (currentMap m (orbit ℂ r a (b + 1) c)) ∈ _
    exact consecutivePolar_coeff_mem m n r a (b + 1) c s hr hs
  · change PowerSeries.coeff s (currentMap m (orbit ℂ r a b (c + 1))) ∈ _
    exact consecutivePolar_coeff_mem m n r a b (c + 1) s hr hs

/-- Every consecutive-power literal polar ideal is preserved by zero modes.
There is no hypothesis of preservation by positive current modes. -/
theorem consecutivePolarIdeal_zero_closed (m n : ℕ) (d : Fin 3)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ consecutivePolarIdeal m n) :
    g0Deriv m (cubeDirection d) 0 p ∈ consecutivePolarIdeal m n := by
  exact polar_ideal_span_derivation_closed (g0Deriv m (cubeDirection d) 0)
    (consecutivePolarSeeds m n) (fun p hp => consecutivePolar_seed_zero_mem m n d hp) hp

/-- The literal quadratic/cubic ideal J23 has proved zero-mode preservation. -/
theorem quadraticCubicPolarIdeal_zero_closed (m : ℕ) (d : Fin 3)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ quadraticCubicPolarIdeal m) :
    g0Deriv m (cubeDirection d) 0 p ∈ quadraticCubicPolarIdeal m := by
  simpa only [consecutivePolarIdeal_two] using consecutivePolarIdeal_zero_closed m 2 d hp

/-- Naming alias for current-word assembly. -/
theorem quadraticCubicPolarIdeal_zero_lower (m : ℕ) (d : Fin 3)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ quadraticCubicPolarIdeal m) :
    g0Deriv m (cubeDirection d) 0 p ∈ quadraticCubicPolarIdeal m :=
  quadraticCubicPolarIdeal_zero_closed m d hp

theorem iterate_zero_lower_mem (m : ℕ) (d : Fin 3) (n : ℕ)
    {p : MvPolynomial (Vars m) ℂ} (hp : p ∈ quadraticCubicPolarIdeal m) :
    (((g0Deriv m (cubeDirection d) 0 : _ → _)^[n]) p) ∈ quadraticCubicPolarIdeal m := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact quadraticCubicPolarIdeal_zero_closed m d ih

end
#print axioms actual_zero_polar_coefficient
#print axioms consecutivePolarIdeal_zero_closed
#print axioms quadraticCubicPolarIdeal_zero_closed
#print axioms iterate_zero_lower_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
