/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieVacuum
import VOA.DeligneAudit.DeligneCharacterStarBound
import VOA.DeligneAudit.F4Sector
import VOA.DeligneAudit.F4Divisor

/-!
# The concrete `F₄` headline for `L_{-5/2}(𝔣₄)`

Instantiated: `W = f4W`, `P = explicitPresentation` (ideal `I₂ⁿˢ = F4data.I`, 324 relations),
`S = F4sector`, `hsurj`/`hgeom` (`F4LiePresentation`), and the MLDE target lower bound
`f4_targetLowerBound` (`F4LieVacuum`, unconditional). Named inputs left:

* U5, `FusionModuleBoundG F4sector f4FusionF` (or, in `_of_squeeze`, the squeeze inputs, the count
  and the universal bound);
* the divisor comparison `DivisorComparisonG F4sector` (the `f4_divisorComparison`; the primed
  forms have it instantiated);
* the star input `F4StarBound`.

Caveat (Naoi): for non-simply-laced `F₄` the Ravinder/Chari–Venkatesh presentation route
to U5 is not literature-verified.
-/

namespace VOA.DeligneAudit.F4Lie

open VOA.DeligneAudit.DeligneCarrier VOA.DeligneAudit.DeligneCharacter
  VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector
  VOA.DeligneAudit.DeligneSector.F4

/-- The `F₄` fusion characters: the unique solution of the mixed recursion. -/
noncomputable def f4FusionF : ℕ → PowerSeries ℚ := fusionOf (hilbSeries f4DemazureHilb)

/-- **`F₄` headline, star bound form**: `L_{-5/2}(𝔣₄)` is classically free with `C₂` ideal
`I₂ⁿˢ`, from U5, the divisor comparison and `F4StarBound`. -/
theorem f4_classicallyFree_concrete (hU5 : FusionModuleBoundG F4sector f4FusionF)
    (hD : DivisorComparisonG F4sector) (hB : F4StarBound) :
    CaseClassicallyFree .F4 f4W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass f4W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  classicallyFree_of_starBound explicitPresentation F4sector f4DemazureHilb
    explicitCurrentJetSurjectivity geometricCarrierEmbedding hU5 hD hB f4_targetLowerBound

open SectorWeyl in
/-- **`F₄` headline, squeeze form**: U5 replaced by the squeeze inputs, the count and the
universal bound. -/
theorem f4_classicallyFree_concrete_of_squeeze {M : ℕ → ℕ → PowerSeries ℚ}
    (h : FusionSqueezeInputsG (hilbSeries f4DemazureHilb) 52 M)
    (hcount : ∀ m, ∃ B, (∀ b, B ≤ b → PowerSeries.coeff b (f4FusionF m) = 0) ∧
      ∑ b ∈ Finset.range B, PowerSeries.coeff b (f4FusionF m) = ((52 : ℕ) : ℚ) ^ m)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule F4sector.f V) (w : V),
      LocalWeylRelG F4sector ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤
        PowerSeries.coeff b (M 0 m))
    (hD : DivisorComparisonG F4sector) (hB : F4StarBound) :
    CaseClassicallyFree .F4 f4W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass f4W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  f4_classicallyFree_concrete (fusionModuleBoundG_of_squeeze F4sector F4sector_n h hcount huniv)
    hD hB

/-- **`F₄` headline, star bound form, divisor comparison instantiated**. -/
theorem f4_classicallyFree_concrete' (hU5 : FusionModuleBoundG F4sector f4FusionF)
    (hB : F4StarBound) :
    CaseClassicallyFree .F4 f4W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass f4W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  f4_classicallyFree_concrete hU5 DeligneDivisor.F4.f4_divisorComparison hB

open SectorWeyl in
/-- **`F₄` headline, squeeze form, divisor comparison instantiated.** -/
theorem f4_classicallyFree_concrete_of_squeeze' {M : ℕ → ℕ → PowerSeries ℚ}
    (h : FusionSqueezeInputsG (hilbSeries f4DemazureHilb) 52 M)
    (hcount : ∀ m, ∃ B, (∀ b, B ≤ b → PowerSeries.coeff b (f4FusionF m) = 0) ∧
      ∑ b ∈ Finset.range B, PowerSeries.coeff b (f4FusionF m) = ((52 : ℕ) : ℚ) ^ m)
    (huniv : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (ρ : CurrentModule F4sector.f V) (w : V),
      LocalWeylRelG F4sector ρ w m → ∀ b, (Module.finrank ℂ (cycDeg ρ w b) : ℚ) ≤
        PowerSeries.coeff b (M 0 m))
    (hB : F4StarBound) :
    CaseClassicallyFree .F4 f4W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass f4W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = explicitPresentation.ideal :=
  f4_classicallyFree_concrete_of_squeeze h hcount huniv DeligneDivisor.F4.f4_divisorComparison hB

end VOA.DeligneAudit.F4Lie

section AxiomAudit
#print axioms VOA.DeligneAudit.F4Lie.f4_classicallyFree_concrete
#print axioms VOA.DeligneAudit.F4Lie.f4_classicallyFree_concrete_of_squeeze
#print axioms VOA.DeligneAudit.F4Lie.f4_classicallyFree_concrete'
#print axioms VOA.DeligneAudit.F4Lie.f4_classicallyFree_concrete_of_squeeze'
end AxiomAudit
