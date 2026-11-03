/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorWeylRel
import VOA.DeligneAudit.A2SectorFusion

/-!
# `CurrentFiberBound` from B8 and U5; the A₂ headline

* B5 (`M_m ⊂ W_m`) is proved (`Mspace_le_carrier`).
* The fibre `W_m / B₊ W_m` is an `sl₃[t]`-module whose generator satisfies the local Weyl and fusion
  relations (`localWeylRel`).
* Given B8 (`CarrierGeneration`: `W_m ⊂ M_m`, i.e. `W_m = M_m`), the Nakayama fibre dimension is at
  most the loop-span dimension of the generator (`fiberDim_le_cycDeg`), and U5
  (`FusionModuleBound F`) bounds the latter by `[q^b] F_m`.

Hence `CurrentFiberBound F` follows from `CarrierGeneration` and `FusionModuleBound F`.
-/

namespace VOA.DeligneAudit.A2

open VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier PowerSeries

/-- **Step B8 (named hypothesis)**: the current carrier `W_m` is generated, as an `sl₃[t]`-module,
by the constant vector `δ_{f₁₂}`, i.e. `W_m ⊂ M_m` (with B5, `W_m = M_m`).  Paper: freeness of
`M_m` (B6; uses U4 and U5) plus the codimension-one comparison and normality. -/
structure CarrierGeneration : Prop where
  le : ∀ m, currentCarrier fullMatrix m 0 ≤ Mspace bracketTable m (5 : Fin 8)

/-- **`CurrentFiberBound` from B8 and U5.** -/
theorem currentFiberBound_of_generation (F : ℕ → PowerSeries ℚ) (hB8 : CarrierGeneration)
    (hU5 : FusionModuleBound F) : CurrentFiberBound F := by
  refine ⟨fun m b => ?_⟩
  have h1 := fiberDim_le_cycDeg bracketTable m relationsStable jacobiCoord 5 fullMatrix_diag
    (hB8.le m) b
  have h2 := hU5.le m (Fib fullMatrix m) (fibRep m) (wGen m) (localWeylRel m) b
  calc (currentFiberDim m b : ℚ) ≤ (Module.finrank ℂ (cycDeg (fibRep m) (wGen m) b) : ℚ) := by
        exact_mod_cast h1
    _ ≤ _ := h2

open VOA.DeligneHigherRankConditionalCapstone in
/-- **A₂ Deligne classical freeness from six named inputs**: `CasimirLayerBound` (B1),
`CarrierGeneration` (B8), `FusionModuleBound F` (U5), `MixedFusionRecursion F demazureHilbSeries`
(U6), `StarIdentity`, `KacWakimotoLowerBound`.  B5, the graded Nakayama step, the auxiliary
tensor split and the fibre's local Weyl relations are proved. -/
theorem classicallyFree_of_weylInputs (F : ℕ → PowerSeries ℚ)
    (hL : CasimirLayerBound) (hB8 : CarrierGeneration) (hU5 : FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hstar : StarIdentity) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_fiberInputs F hL (currentFiberBound_of_generation F hB8 hU5) hU6 hstar hkw

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.currentFiberBound_of_generation
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_weylInputs
end AxiomAudit
