import VOA.Classification.COne.PlusSplitLatticeCharacters
import VOA.Classification.COne.PlusSplitZhuNormalForms

/-! # Session 4 assembly

The new unconditional results are character-table separation, passage from
one-dimensional module tops to characters, and generation of the actual Zhu
quotient. The three explicit top-model/reduction inputs are not proved here.
The equal-bottom lifting and resonant inputs are unchanged.
-/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne

/-- Explicit top models and normal-form reductions suffice for Zhu semisimplicity. -/
theorem zhuSemisimple_of_explicit_topModels_reductions
    (hu : V2mPlusSignHalfTopModels) (ht : V2mPlusTwistedTopModels)
    (hr : V2mPlusZhuNormalFormReductions) : ZhuV2mPlusSemisimple :=
  zhuV2mPlusSemisimple_of_dimension_characters
    (zhuDimensionBound_of_normalFormReductions hr) (zhuDistinctCharacters_of_signHalf_twisted hu ht)

/-- Conditional rationality, with every remaining VOA input displayed. -/
theorem rationality_of_explicit_topModels_reductions
    (hu : V2mPlusSignHalfTopModels) (ht : V2mPlusTwistedTopModels)
    (hr : V2mPlusZhuNormalFormReductions) (hlift : V2mPlusEqualBottomZhuLifting)
    (hgen : V2mPlusResonantGeneratorComplements) : V2mPlusRationalFactGe2 :=
  rationality_of_character_bottom_generator_inputs
    (zhuDimensionBound_of_normalFormReductions hr) (zhuDistinctCharacters_of_signHalf_twisted hu ht)
    hlift hgen

end VOA.Classification.COne
