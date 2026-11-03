/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorFusion
import VOA.DeligneAudit.A2CarrierLayerBound
import VOA.DeligneAudit.A2CharacterStarReduction
import VOA.DeligneAudit.A2CarrierMehler
import VOA.Commutative.FourTriangularDeligne
import VOA.DeligneAudit.A2SectorGeneric

/-!
# A₂ Deligne classical freeness: the current headline

The top of the A₂ development. Proved: the explicit presentation, jet surjectivity, the
geometric carrier embedding and B1, the resummation D3, and the 1/(q)_d and 1/(q)_m factors
of the fusion bound. The remaining inputs are hypotheses:

* `CurrentFiberBound F`: paper B5–B8, with the literature inputs U4 (Chari–Fourier–Khandai) and
  U5 (Ravinder/Feigin);
* `MixedFusionRecursion F demazureHilbSeries`: U6 (Ravinder);
* `StarIdentity`: the q-series identity (⋆), reduced in `A2CharacterStarChain` to three
  q-series lemmas;
* `KacWakimotoLowerBound`: the Kac–Wakimoto character (literature).
-/

namespace VOA.DeligneAudit.A2

open VOA.DeligneHigherRankConditionalCapstone

/-- **A₂ Deligne classical freeness, current form.** B1 (`casimirLayerBound`) is plugged in. The
conclusion also identifies the explicit ideal `I₂ⁿˢ` with the full `C₂` kernel. -/
theorem classicallyFree_of_remainingInputs (F : ℕ → PowerSeries ℚ)
    (hF : CurrentFiberBound F) (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hstar : StarIdentity) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_fiberInputs F casimirLayerBound hF hU6 hstar hkw

/-- **A₂ headline with (⋆) reduced.** `StarReduction` is proved, so (⋆) needs only the two
q-series lemmas `ShiftedMehler` and `FourTriangular`. -/
theorem classicallyFree_of_qSeriesInputs (F : ℕ → PowerSeries ℚ)
    (hF : CurrentFiberBound F) (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hmehler : ShiftedMehler) (htri : FourTriangular) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_remainingInputs F hF hU6
    (starIdentity_of_mehler_triangular hmehler htri) hkw

/-- **A₂ headline, current minimum.** `StarReduction` and `ShiftedMehler` are proved, so the
q-series side needs only `FourTriangular` (the four-triangular-numbers theorem). The other
inputs are the fusion-fibre bound (B5–B8 with U4/U5), U6 and Kac–Wakimoto. -/
theorem classicallyFree_of_currentResiduals (F : ℕ → PowerSeries ℚ)
    (hF : CurrentFiberBound F) (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (htri : FourTriangular) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_remainingInputs F hF hU6 (starIdentity_of_fourTriangular htri) hkw

/-- The q-series identity (⋆) for A₂, a theorem: `StarReduction`, `ShiftedMehler`
and `FourTriangular` are all proved. -/
theorem starIdentity : StarIdentity := starIdentity_of_fourTriangular fourTriangular

/-- **A₂ Deligne classical freeness, current headline.** Every combinatorial input is proved.
What remains is the fusion-fibre bound (paper B6–B8, with the literature inputs U4/U5; B5 is
proved), Ravinder's mixed fusion recursion (U6), and the Kac–Wakimoto lower bound. -/
theorem classicallyFree_of_fusionAndKW (F : ℕ → PowerSeries ℚ)
    (hF : CurrentFiberBound F) (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_remainingInputs F hF hU6 starIdentity hkw

/-- **A₂ Deligne classical freeness, sharpest current form.** Proved inside: the presentation, jet
surjectivity, carrier embedding, B1, B5, the generic comparison of B8, D3 and (⋆). Remaining
hypotheses: B6 (`MFreeness`), the divisor comparison of B8 (`DivisorComparison`), and the literature
inputs U5 (`FusionModuleBound`, smallest form), U6 and Kac–Wakimoto. U4 is not needed. -/
theorem classicallyFree_of_openInputs (F : ℕ → PowerSeries ℚ)
    (hF : MFreeness) (hD : DivisorComparison)
    (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_divisorInputs F casimirLayerBound hF hD hU5 hU6 starIdentity hkw

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_remainingInputs
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_qSeriesInputs
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_currentResiduals
#print axioms VOA.DeligneAudit.A2.starIdentity
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_fusionAndKW
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_openInputs
end AxiomAudit
