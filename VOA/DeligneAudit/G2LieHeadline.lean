/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2LieVacuum
import VOA.DeligneAudit.G2Fusion
import VOA.DeligneAudit.G2Divisor
import VOA.DeligneAudit.DeligneCharacterStarBound
import VOA.DeligneAudit.DeligneCharacterG2FusionZ

/-!
# The concrete `G₂` headline for `L_{-5/3}(𝔤₂)`

Everything instantiated: `W = g2W`, `P = explicitPresentation` (ideal `I₂ⁿˢ = G2data.I`),
`S = G2sector`, `hsurj`/`hgeom` (`G2LiePresentation`), `hD = g2_divisorComparison`,
`hc`, `hvac` and the vacuum quartic relation (`G2LieVacuum`). Named inputs left:

* U5, `FusionModuleBoundG G2sector g2FusionF` — or, in `_of_squeeze`, the count
  `G2DemazureCount`, the squeeze inputs and the universal bound;
* the star input: `G2StarBound` (`≤` form), or the two Demazure halves `G2DemazureFermionic`,
  `G2FermionicKW`.

Via the unclamped route (`DeligneCharacterG2FusionZ`, energy proved), `g2_classicallyFree_concrete_Z`
and `g2_classicallyFree_concrete_Z_of_fermionic` leave only the squeeze inputs for `g2HilbSeriesZ`, the
universal bound, and the star input.
-/

namespace VOA.DeligneAudit.G2Lie

open VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.DeligneCharacter
  VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.G2

/-- **`G₂` headline, star bound form**: `L_{-5/3}(𝔤₂)` is classically free with `C₂` ideal
`I₂ⁿˢ`, from U5 and `G2StarBound`. -/
theorem g2_classicallyFree_concrete (hU5 : FusionModuleBoundG G2sector g2FusionF)
    (hB : G2StarBound) :
    CaseClassicallyFree .G2 g2W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass g2W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  g2_classicallyFree_of_starBound g2W explicitPresentation G2sector explicitCurrentJetSurjectivity
    geometricCarrierEmbedding hU5 DeligneDivisor.G2.g2_divisorComparison g2W_centralCharge
    g2W_vacuum_ne_zero g2_vacuumQuarticRelation hB

/-- **`G₂` headline, Demazure halves form**: from U5 and the two Demazure halves. -/
theorem g2_classicallyFree_concrete_of_fermionic (hU5 : FusionModuleBoundG G2sector g2FusionF)
    (hF1 : G2Star.G2DemazureFermionic) (hF2 : G2Star.G2FermionicKW) :
    CaseClassicallyFree .G2 g2W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass g2W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  g2_classicallyFree g2W explicitPresentation G2sector explicitCurrentJetSurjectivity
    geometricCarrierEmbedding hU5 DeligneDivisor.G2.g2_divisorComparison g2W_centralCharge
    g2W_vacuum_ne_zero g2_vacuumQuarticRelation hF1 hF2

open SectorWeyl in
/-- **`G₂` headline, squeeze form**: U5 replaced by the count, the squeeze inputs and the
universal bound. -/
theorem g2_classicallyFree_concrete_of_squeeze {M : ℕ → ℕ → PowerSeries ℚ}
    (hC : G2DemazureCount) (h : FusionSqueezeInputsG (hilbSeries g2DemazureHilb) 14 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule G2sector.f V) (w : V),
      LocalWeylRelG G2sector ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤
        PowerSeries.coeff b (M 0 m))
    (hB : G2StarBound) :
    CaseClassicallyFree .G2 g2W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass g2W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  g2_classicallyFree_concrete
    (g2_fusionModuleBound_of_squeeze G2sector G2sector_n hC h huniv) hB

open SectorWeyl in
/-- **`G₂` headline, unclamped squeeze form**: no Demazure count, energy or positivity input;
named only the squeeze inputs for `g2HilbSeriesZ`, the universal bound and `G2StarBound`. -/
theorem g2_classicallyFree_concrete_Z {M : ℕ → ℕ → PowerSeries ℚ}
    (h : FusionSqueezeInputsG g2HilbSeriesZ 14 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule G2sector.f V) (w : V),
      LocalWeylRelG G2sector ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤
        PowerSeries.coeff b (M 0 m))
    (hB : G2StarBound) :
    CaseClassicallyFree .G2 g2W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass g2W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal := by
  have hU5 := g2_fusionModuleBoundZ_of_squeeze' G2sector G2sector_n h huniv
  exact g2_classicallyFree_concrete ((g2FusionF_eq_Z hU5) ▸ hU5) hB

open SectorWeyl in
/-- **`G₂` headline, unclamped squeeze form with the Demazure halves**
(`g2_classicallyFree_Z_of_squeeze'` instantiated). -/
theorem g2_classicallyFree_concrete_Z_of_fermionic {M : ℕ → ℕ → PowerSeries ℚ}
    (h : FusionSqueezeInputsG g2HilbSeriesZ 14 M)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule G2sector.f V) (w : V),
      LocalWeylRelG G2sector ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤
        PowerSeries.coeff b (M 0 m))
    (hF1 : G2Star.G2DemazureFermionic) (hF2 : G2Star.G2FermionicKW) :
    CaseClassicallyFree .G2 g2W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass g2W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  g2_classicallyFree_Z_of_squeeze' g2W explicitPresentation G2sector G2sector_n
    explicitCurrentJetSurjectivity geometricCarrierEmbedding h huniv
    DeligneDivisor.G2.g2_divisorComparison g2W_centralCharge g2W_vacuum_ne_zero
    g2_vacuumQuarticRelation hF1 hF2

end VOA.DeligneAudit.G2Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Lie.g2_classicallyFree_concrete
#print axioms VOA.DeligneAudit.G2Lie.g2_classicallyFree_concrete_of_fermionic
#print axioms VOA.DeligneAudit.G2Lie.g2_classicallyFree_concrete_of_squeeze
#print axioms VOA.DeligneAudit.G2Lie.g2_classicallyFree_concrete_Z
#print axioms VOA.DeligneAudit.G2Lie.g2_classicallyFree_concrete_Z_of_fermionic
end AxiomAudit
