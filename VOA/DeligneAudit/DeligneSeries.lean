/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSeriesA2
import VOA.DeligneAudit.D4FusionKernelTheta
import VOA.DeligneAudit.G2FusionKernelTheta
import VOA.DeligneAudit.F4FusionCountZ
import VOA.DeligneAudit.E6FusionKernelFinal
import VOA.DeligneAudit.E7FusionKernelFinal
import VOA.DeligneAudit.E8FusionKernelFinal
import VOA.DeligneAudit.DeligneCharacterEFusionCount
import VOA.DeligneAudit.DeligneCharacterE8FusionCount
import VOA.DeligneAudit.DeligneFusionFiniteGA2
import VOA.DeligneAudit.DeligneFusionFiniteGD4
import VOA.DeligneAudit.DeligneFusionFiniteGE6
import VOA.DeligneAudit.DeligneFusionFiniteGG2
import VOA.DeligneAudit.DeligneFusionFiniteGF4
import VOA.DeligneAudit.DeligneFusionFiniteGE7
import VOA.DeligneAudit.DeligneFusionFiniteGE8

-- The per-type table below and the fully qualified names exceed 100 characters.
set_option linter.style.longLine false

/-!
# The Deligne series: the sharpest current theorem for each type

For each type `X` of the Deligne exceptional series, `X_classicallyFree_final` states
`CaseClassicallyFree .X W P ∧ ker = I₂ⁿˢ` for the explicit simple affine VOA `W = L_k(𝔤_X)` at the Deligne
level, with its explicit `C₂` presentation `P` (ideal `I₂ⁿˢ`). This file contains wrappers only; it
proves no new mathematics.

**What is proved for every type:**
- the presentation and geometric carrier embedding;
- the MLDE target lower bound (Zhu / the vacuum quartic relation);
- the divisor comparison;
- the squeeze;
- Ravinder's kernel lemma (`rec_le`, finiteness for `a ≥ 1`);
- the finiteness clause of `FusionTotalBoundG` (`<type>_fusionTotalBoundG_of_dim`);
- the counts.

## Named inputs per type

| type | VOA | fusion bound | Demazure realization (U7) | count | star |
|---|---|---|---|---|---|
| `A₂` | `L_{-3/2}(sl₃)` | proved (`CVUniv.fusionTotalDim`) | proved (`EvalModel`) | proved | none needed |
| `G₂` | `L_{-5/3}(𝔤₂)` | `FusionTotalDimG G2sector` | `DemazureRealizationG … g2HilbSeriesZ` | proved | `G2StarBound` |
| `D₄` | `L_{-2}(so₈)` | `FusionTotalDimG D4sector` | `DemazureRealizationG … D4Wp.hilbSeriesZ` | proved | proved (`D4SchurEqE4`) |
| `F₄` | `L_{-5/2}(𝔣₄)` | `FusionTotalDimG F4sector` | `DemazureRealizationG … (hilbSeries f4DemazureHilb)` | proved | `F4StarBound` |
| `E₆` | `L_{-3}(𝔢₆)` | `FusionTotalDimG E6sector` | `DemazureRealizationG … (hilbSeries e6DemazureHilb)` | proved | `E6StarBound` |
| `E₇` | `L_{-4}(𝔢₇)` | `FusionTotalDimG E7sector` | `DemazureRealizationG … (hilbSeries e7DemazureHilb)` | proved | `E7StarBound` |
| `E₈` | `L_{-6}(𝔢₈)` | `FusionTotalDimG E8sector` | `DemazureRealizationG … (hilbSeries e8DemazureHilb)` | proved | `E8StarBound` |

`A₂` is unconditional: both universal CV base bounds and the Demazure realization
are proved. `A2_classicallyFree_final_S2` retains the older S2 interface for reuse.

## Literature sources of the named inputs (from the WS logs)

- **Fusion bound.** `FusionTotalDimG` / `FusionTotalDim`: `dim V(θ)^{*m} ≤ (dim 𝔤)^m` for the cyclic module
  with the local Weyl and fusion relations. Sources: Setia–Rani–Khandai §8 (the implemented enlarged-CV route for `A₂`);
  Kus–Littelmann Theorem3.5/Corollary3.6(3) supplies a published repair of Feigin;
  Fourier–Littelmann (simply laced);
  Ravinder, SIGMA 10 (2014) 110, case `a = 0` (any simple `𝔤`, per the abstract); Chari–Venkatesh,
  CMP 2015 (`V(ξ)`, `ξ_θ = (1^m)`). For `G₂`/`F₄` the Chari–Venkatesh exponent `⌈m(θ,α^∨)/d_α⌉` agrees with
  our truncation. This is consistent, not checked line by line.
- **Demazure realization (U7).** `D(1,nθ)` satisfies the `M_{n,0}` relations with the stated character.
  It is proved for `A₂` (the evaluation model). Sources for the others: the Chari–Venkatesh presentation of level-one Demazure modules (any simple `𝔤`), plus the
  affine Demazure character formula (for `A₂`: Sanderson, Ion; Fourier–Littelmann). The characters are
  checked numerically outside Lean.
- **Count.** `∑ coeff fusionF_m = (dim 𝔤)^m`. It is proved for all seven types, from the `q = 1`
  Demazure count and the energy (and, for `E₆`/`E₇`/`E₈`, the unclamped route).
- **Star.** `D_N ≤ mldeCoeff h N` (the `XStarBound`). It is implied by the star identity (Kac–Wakimoto
  type character identity). Proved for `D₄`; open for the others.
- Naoi caveat (`G₂`, `F₄`): `θ` is long, so `W_loc(nθ) = D(1,nθ)` along `θ`. It does not enter.
-/

namespace VOA.DeligneAudit.DeligneSeries

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG

/-- **`G₂`**: `L_{-5/3}(𝔤₂)`. -/
theorem G2_classicallyFree_final (hF : VOA.DeligneAudit.FiniteG.FusionTotalDimG G2.G2sector)
    (hD : ∀ n, DemazureRealizationG G2.G2sector (ravFam G2.G2sector)
      VOA.DeligneAudit.DeligneCarrier.g2HilbSeriesZ n)
    (hB : VOA.DeligneAudit.DeligneCharacter.G2StarBound) :
    CaseClassicallyFree .G2 VOA.DeligneAudit.G2Lie.g2W VOA.DeligneAudit.G2Lie.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.G2Lie.g2W 1
          ⟨VOA.DeligneAudit.G2Lie.explicitPresentation.gen i,
            VOA.DeligneAudit.G2Lie.explicitPresentation.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.G2Lie.explicitPresentation.ideal :=
  g2_classicallyFree_of_totalBound (VOA.DeligneAudit.FiniteG.G2.g2_fusionTotalBoundG_of_dim hF) hD hB

/-- **`D₄`**: `L_{-2}(so₈)` (star input proved). -/
theorem D4_classicallyFree_final (hF : VOA.DeligneAudit.FiniteG.FusionTotalDimG D4.D4sector)
    (hD : ∀ n, DemazureRealizationG D4.D4sector (ravFam D4.D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    CaseClassicallyFree .D4 VOA.DeligneAudit.D4Lie.W4 VOA.DeligneAudit.D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.D4Lie.W4 1
          ⟨VOA.DeligneAudit.D4Lie.explicitPresentation4.gen i,
            VOA.DeligneAudit.D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.D4Lie.explicitPresentation4.ideal :=
  d4_classicallyFree_of_totalBound (VOA.DeligneAudit.FiniteG.D4.d4_fusionTotalBoundG_of_dim hF) hD

/-- **`F₄`**: `L_{-5/2}(𝔣₄)`. -/
theorem F4_classicallyFree_final (hF : VOA.DeligneAudit.FiniteG.FusionTotalDimG F4.F4sector)
    (hD : ∀ n, DemazureRealizationG F4.F4sector (ravFam F4.F4sector)
      (VOA.DeligneAudit.DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.f4DemazureHilb) n)
    (hB : VOA.DeligneAudit.DeligneCharacter.F4StarBound) :
    CaseClassicallyFree .F4 VOA.DeligneAudit.F4Lie.f4W VOA.DeligneAudit.F4Lie.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.F4Lie.f4W 1
          ⟨VOA.DeligneAudit.F4Lie.explicitPresentation.gen i,
            VOA.DeligneAudit.F4Lie.explicitPresentation.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.F4Lie.explicitPresentation.ideal :=
  VOA.DeligneAudit.DeligneCarrier.f4_classicallyFree_of_totalBound'
    (VOA.DeligneAudit.FiniteG.F4.f4_fusionTotalBoundG_of_dim hF) hD hB

/-- **`E₆`**: `L_{-3}(𝔢₆)`. -/
theorem E6_classicallyFree_final
    (hF : VOA.DeligneAudit.FiniteG.FusionTotalDimG VOA.DeligneAudit.DeligneCarrier.E6.E6sector)
    (hD : ∀ n, DemazureRealizationG VOA.DeligneAudit.DeligneCarrier.E6.E6sector
      (ravFam VOA.DeligneAudit.DeligneCarrier.E6.E6sector)
      (VOA.DeligneAudit.DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e6DemazureHilb) n)
    (hB : VOA.DeligneAudit.DeligneCharacter.E6StarBound) :
    CaseClassicallyFree .E6 VOA.DeligneAudit.DeligneCarrier.E6.W6
        VOA.DeligneAudit.DeligneCarrier.E6.explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.DeligneCarrier.E6.W6 1
          ⟨VOA.DeligneAudit.DeligneCarrier.E6.explicitPresentation.gen i,
            VOA.DeligneAudit.DeligneCarrier.E6.explicitPresentation.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.DeligneCarrier.E6.explicitPresentation.ideal :=
  VOA.DeligneAudit.DeligneCarrier.E6.e6_classicallyFree_of_starBound
    (e6_fusionModuleBound_of_totalBound' (VOA.DeligneAudit.FiniteG.E6.e6_fusionTotalBoundG_of_dim hF) hD) hB

/-- **`E₇`**: `L_{-4}(𝔢₇)`. -/
theorem E7_classicallyFree_final
    (hF : VOA.DeligneAudit.FiniteG.FusionTotalDimG VOA.DeligneAudit.DeligneCarrier.E7.E7sector)
    (hD : ∀ n, DemazureRealizationG VOA.DeligneAudit.DeligneCarrier.E7.E7sector
      (ravFam VOA.DeligneAudit.DeligneCarrier.E7.E7sector)
      (VOA.DeligneAudit.DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e7DemazureHilb) n)
    (hB : VOA.DeligneAudit.DeligneCharacter.E7StarBound) :
    CaseClassicallyFree .E7 VOA.DeligneAudit.E7Lie.W7 VOA.DeligneAudit.E7Lie.explicitPresentation7 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.E7Lie.W7 1
          ⟨VOA.DeligneAudit.E7Lie.explicitPresentation7.gen i,
            VOA.DeligneAudit.E7Lie.explicitPresentation7.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.E7Lie.explicitPresentation7.ideal :=
  VOA.DeligneAudit.E7Lie.e7_classicallyFree_of_starBound
    (e7_fusionModuleBound_of_totalBound' (VOA.DeligneAudit.FiniteG.E7.e7_fusionTotalBoundG_of_dim hF) hD) hB

/-- **`E₈`**: `L_{-6}(𝔢₈)`. -/
theorem E8_classicallyFree_final
    (hF : VOA.DeligneAudit.FiniteG.FusionTotalDimG VOA.DeligneAudit.DeligneCarrier.E8.E8sector)
    (hD : ∀ n, DemazureRealizationG VOA.DeligneAudit.DeligneCarrier.E8.E8sector
      (ravFam VOA.DeligneAudit.DeligneCarrier.E8.E8sector)
      (VOA.DeligneAudit.DeligneCarrier.hilbSeries VOA.DeligneAudit.DeligneCharacter.e8DemazureHilb) n)
    (hB : VOA.DeligneAudit.DeligneCharacter.E8StarBound) :
    CaseClassicallyFree .E8 VOA.DeligneAudit.E8Lie.W8 VOA.DeligneAudit.E8Lie.explicitPresentation8 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.E8Lie.W8 1
          ⟨VOA.DeligneAudit.E8Lie.explicitPresentation8.gen i,
            VOA.DeligneAudit.E8Lie.explicitPresentation8.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.E8Lie.explicitPresentation8.ideal :=
  VOA.DeligneAudit.E8Lie.e8_classicallyFree_of_starBound
    (e8_fusionModuleBound_of_totalBound' (VOA.DeligneAudit.FiniteG.E8.e8_fusionTotalBoundG_of_dim hF) hD) hB

end VOA.DeligneAudit.DeligneSeries

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneSeries.A2_classicallyFree_final
#print axioms VOA.DeligneAudit.DeligneSeries.A2_classicallyFree_final_S2
#print axioms VOA.DeligneAudit.DeligneSeries.G2_classicallyFree_final
#print axioms VOA.DeligneAudit.DeligneSeries.D4_classicallyFree_final
#print axioms VOA.DeligneAudit.DeligneSeries.F4_classicallyFree_final
#print axioms VOA.DeligneAudit.DeligneSeries.E6_classicallyFree_final
#print axioms VOA.DeligneAudit.DeligneSeries.E7_classicallyFree_final
#print axioms VOA.DeligneAudit.DeligneSeries.E8_classicallyFree_final
end AxiomAudit
