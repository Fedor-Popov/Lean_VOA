import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarCheck0
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCompiler
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishing

/-! Semantic transfer of the first static C-color certificate into the literal
quadratic/cubic polar ideal. All identities concern whole polynomials/series;
contact-word coverage and quotient counts are separate. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- The cleared static polynomial identity uses un-divided actual cube orbits. -/
theorem polynomial_identity0 (K : Type*) [CommRing K] :
    (8 : ℤ) • ((MvPolynomial.X 0 : P8 K) ^ 2 * MvPolynomial.X 7 ^ 2) =
      orbit K 2 0 0 0 * orbit K 2 2 2 2 := by
  simpa only [QuarticReduced.orbitRow_eval] using
    eval_identity0 (MvPolynomial.X : Fin 8 → P8 K)

/-- Map the identity through the original signed normalized current map. -/
theorem current_identity0 (m : ℕ) :
    (8 : ℤ) • (actualCurrent m 0 ^ 2 * actualCurrent m 7 ^ 2) =
      currentMap m (orbit ℂ 2 0 0 0) * currentMap m (orbit ℂ 2 2 2 2) := by
  have h := congrArg (currentMap m) (polynomial_identity0 ℂ)
  simpa only [map_zsmul,map_mul,map_pow,currentMap_X] using h

theorem coefficient_identity0 (m : ℕ) :
    (8 : ℤ) • PowerSeries.coeff (2 * m - 3)
        (actualCurrent m 0 ^ 2 * actualCurrent m 7 ^ 2) =
      PowerSeries.coeff (2 * m - 3)
        (currentMap m (orbit ℂ 2 0 0 0) * currentMap m (orbit ℂ 2 2 2 2)) := by
  have h := congrArg (PowerSeries.coeff (2 * m - 3)) (current_identity0 m)
  simpa only [map_zsmul] using h

/-- Both whole quadratic factors have literal J23 tails; their convolution
past the summed cutoff belongs to J23 for every cutoff, including small m. -/
theorem product_coeff_mem_polarIdeal0 (m : ℕ) :
    PowerSeries.coeff (2 * m - 3)
        (currentMap m (orbit ℂ 2 0 0 0) * currentMap m (orbit ℂ 2 2 2 2)) ∈
      quadraticCubicPolarIdeal m := by
  simpa only [jetDerivative_zero] using
    (coeff_jet_product_mem (quadraticCubicPolarIdeal m)
      (currentMap m (orbit ℂ 2 0 0 0)) (currentMap m (orbit ℂ 2 2 2 2))
      2 2 m 0 0 (2 * m - 3)
      (fun k hk => quadraticCubicPolar_coeff_mem m 2 0 0 0 k (Or.inl rfl) hk)
      (fun k hk => quadraticCubicPolar_coeff_mem m 2 2 2 2 k (Or.inl rfl) hk)
      (by omega))

/-- Cancel the proved nonzero integer multiplier over Complex. The target
lands in the SMALL literal quadratic/cubic ideal, without a closure premise. -/
theorem actual_word_coeff_mem_polarIdeal0 (m : ℕ) :
    PowerSeries.coeff (2 * m - 3)
        (actualCurrent m 0 ^ 2 * actualCurrent m 7 ^ 2) ∈
      quadraticCubicPolarIdeal m := by
  have hm : (8 : ℤ) • PowerSeries.coeff (2 * m - 3)
        (actualCurrent m 0 ^ 2 * actualCurrent m 7 ^ 2) ∈
      quadraticCubicPolarIdeal m := by
    rw [coefficient_identity0]
    exact product_coeff_mem_polarIdeal0 m
  have hc : ((8 : ℤ) : ℂ) • PowerSeries.coeff (2 * m - 3)
        (actualCurrent m 0 ^ 2 * actualCurrent m 7 ^ 2) ∈
      (quadraticCubicPolarIdeal m).restrictScalars ℂ := by
    simpa only [Int.cast_smul_eq_zsmul ℂ] using hm
  exact (Submodule.smul_mem_iff ((quadraticCubicPolarIdeal m).restrictScalars ℂ)
    (by norm_num : ((8 : ℤ) : ℂ) ≠ 0)).mp hc

/-- Color seven has sign minus one twice, so the original unsigned whole
current word has EXACTLY the same coefficient and the same J23 membership. -/
theorem original_word_coeff_mem_polarIdeal0 (m : ℕ) :
    PowerSeries.coeff (2 * m - 3)
        (AllM.current m 0 ^ 2 * AllM.current m 7 ^ 2) ∈
      quadraticCubicPolarIdeal m := by
  simpa [actualCurrent,cubeSign,cubeColor] using actual_word_coeff_mem_polarIdeal0 m

end
#print axioms polynomial_identity0
#print axioms current_identity0
#print axioms product_coeff_mem_polarIdeal0
#print axioms actual_word_coeff_mem_polarIdeal0
#print axioms original_word_coeff_mem_polarIdeal0
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.CenterStaticPolar
