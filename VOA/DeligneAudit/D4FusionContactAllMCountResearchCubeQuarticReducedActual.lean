import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedActualEvaluation
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishingStrict
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-! All twenty certified actual quartic moments lie in the literal smaller
quadratic/cubic polar ideal. Three certificates are syzygies; no independence
or rank is asserted. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- The exact whole-series certificate, before any coefficient is extracted. -/
theorem certificate_current_identity (m : ℕ) (i : Fin 20) :
    certMultiplier i • actualJetTarget m (certOrder i) (certChannel i) =
      ((certProducts i).map fun p => p.coeff • actualJetProduct m p).sum := by
  have h := congrArg (currentJetEvaluate m) (certificate_jet_identity i)
  simpa only [map_zsmul,map_list_sum,List.map_map,Function.comp_def,
    currentJetEvaluate_jetTarget,currentJetEvaluate_jetProduct] using h

theorem certificate_current_coefficient_identity (m N : ℕ) (i : Fin 20) :
    certMultiplier i •
        PowerSeries.coeff N (actualJetTarget m (certOrder i) (certChannel i)) =
      ((certProducts i).map fun p =>
        p.coeff • PowerSeries.coeff N (actualJetProduct m p)).sum := by
  have h := congrArg (PowerSeries.coeff N) (certificate_current_identity m i)
  simpa only [map_zsmul,map_list_sum,List.map_map,Function.comp_def] using h

/-- The ordinary-jet convolution cutoff remains strict with Nat subtraction,
for every m and derivative order; no artificial lower bound on m is needed. -/
theorem whole_quintic_jet_cutoff (m j : ℕ) :
    2 * m < 5 + (2 * m - 3 - j) + j := by omega

theorem certificate_product_coeff_mem_polarIdeal (m : ℕ) (i : Fin 20)
    (p : ProductSpec) (hp : p ∈ certProducts i) :
    PowerSeries.coeff (2 * m - 3 - certOrder i) (actualJetProduct m p) ∈
      quadraticCubicPolarIdeal m := by
  apply quadratic_cubic_jet_product_coeff_mem_polarIdeal
  have ho := certProduct_orders i p hp
  have hc := whole_quintic_jet_cutoff m (certOrder i)
  omega

private theorem polar_zsmul_mem (m : ℕ) (z : ℤ) {p : MvPolynomial (Vars m) ℂ}
    (hp : p ∈ quadraticCubicPolarIdeal m) : z • p ∈ quadraticCubicPolarIdeal m := by
  have h := ((quadraticCubicPolarIdeal m).restrictScalars ℂ).smul_mem (z : ℂ) hp
  simpa only [Int.cast_smul_eq_zsmul ℂ] using h

/-- Cleared integer certificate multipliers are nonzero over Complex, so
the target itself lies in the SMALL literal quadratic/cubic ideal. -/
theorem certificate_current_coeff_mem_polarIdeal (m : ℕ) (i : Fin 20) :
    PowerSeries.coeff (2 * m - 3 - certOrder i)
        (actualJetTarget m (certOrder i) (certChannel i)) ∈
      quadraticCubicPolarIdeal m := by
  have hs : ((certProducts i).map fun p =>
      p.coeff • PowerSeries.coeff (2 * m - 3 - certOrder i)
        (actualJetProduct m p)).sum ∈ quadraticCubicPolarIdeal m := by
    apply list_sum_mem
    intro q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact polar_zsmul_mem m p.coeff (certificate_product_coeff_mem_polarIdeal m i p hp)
  have hm : certMultiplier i •
      PowerSeries.coeff (2 * m - 3 - certOrder i)
        (actualJetTarget m (certOrder i) (certChannel i)) ∈
      quadraticCubicPolarIdeal m := by
    rw [certificate_current_coefficient_identity]
    exact hs
  have hn : (certMultiplier i : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (certMultiplier_pos i))
  have hc : (certMultiplier i : ℂ) •
      PowerSeries.coeff (2 * m - 3 - certOrder i)
        (actualJetTarget m (certOrder i) (certChannel i)) ∈
      (quadraticCubicPolarIdeal m).restrictScalars ℂ := by
    simpa only [Int.cast_smul_eq_zsmul ℂ] using hm
  exact (Submodule.smul_mem_iff ((quadraticCubicPolarIdeal m).restrictScalars ℂ) hn).mp hc

/-- Twenty concrete finite moment endpoints, in the proper lower ideal
for m>=3, and still valid at every small m. No rank is inferred. -/
theorem certificate_quartic_moment_mem_polarIdeal (m : ℕ) (i : Fin 20) :
    actualQuarticMoment m (certOrder i) (certChannel i) ∈ quadraticCubicPolarIdeal m := by
  rw [← actualJetTarget_coeff_eq_moment]
  exact certificate_current_coeff_mem_polarIdeal m i

theorem certificate_quartic_moment_mem_powerBounded (m : ℕ) (i : Fin 20) :
    actualQuarticMoment m (certOrder i) (certChannel i) ∈ LeviRules.powerBoundedIdeal m 3 :=
  quadraticCubicPolarIdeal_le_powerBounded m (certificate_quartic_moment_mem_polarIdeal m i)

theorem certificate_quartic_moment_mem_candidate (m : ℕ) (i : Fin 20) :
    actualQuarticMoment m (certOrder i) (certChannel i) ∈ AllM.candidateIdeal m :=
  quadraticCubicPolarIdeal_le_candidate m (certificate_quartic_moment_mem_polarIdeal m i)

theorem certificate_moments_properIdeal (m : ℕ) (hm : 3 ≤ m) :
    quadraticCubicPolarIdeal m < AllM.candidateIdeal m ∧
      ∀ i : Fin 20, actualQuarticMoment m (certOrder i) (certChannel i) ∈
        quadraticCubicPolarIdeal m :=
  ⟨quadraticCubicPolarIdeal_lt_candidate m hm,certificate_quartic_moment_mem_polarIdeal m⟩

end
#print axioms certificate_current_identity
#print axioms certificate_current_coeff_mem_polarIdeal
#print axioms certificate_quartic_moment_mem_polarIdeal
#print axioms certificate_moments_properIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
