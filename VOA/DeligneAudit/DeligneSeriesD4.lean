import VOA.DeligneAudit.DeligneSeries
import VOA.DeligneAudit.D4CharDemazureRealization

/-!
# `D₄` classical freeness from Input T alone

`DeligneSeries.D4_classicallyFree_final` takes two inputs for `L_{-2}(so₈)`: the fusion-product
total-dimension bound `hF` (Input T) and the Demazure realizations `hD` (Input R).  Input R is
proved for every degree by `D4Char.d4_demazureRealization`, so the `D₄` theorem needs Input T
only.
-/

namespace VOA.DeligneAudit.DeligneSeries

open VOA.DeligneHigherRankConditionalCapstone VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG

/-- **`D₄`**: `L_{-2}(so₈)` is classically free for its presentation by `105` quadrics, and the
`C₂` kernel is their ideal, assuming only the fusion-product bound (Input T); Input R is
`D4Char.d4_demazureRealization`. -/
theorem D4_classicallyFree_of_inputT (hF : VOA.DeligneAudit.FiniteG.FusionTotalDimG D4.D4sector) :
    CaseClassicallyFree .D4 VOA.DeligneAudit.D4Lie.W4 VOA.DeligneAudit.D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass VOA.DeligneAudit.D4Lie.W4 1
          ⟨VOA.DeligneAudit.D4Lie.explicitPresentation4.gen i,
            VOA.DeligneAudit.D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        VOA.DeligneAudit.D4Lie.explicitPresentation4.ideal :=
  D4_classicallyFree_final hF VOA.DeligneAudit.D4Char.d4_demazureRealization

end VOA.DeligneAudit.DeligneSeries
