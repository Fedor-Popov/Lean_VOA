import VOA.Classification.COne.PlusSplitC2Sharp
import VOA.Classification.COne.PlusSplitResonantLifts

/-! Session nine: the sharp dimension bound is unconditional. Twisted top
models and resonant splitting remain explicit inputs to rationality. -/
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne

theorem zhuSemisimple_of_twistedTopModels (ht : V2mPlusTwistedTopModels) :
    ZhuV2mPlusSemisimple :=
  zhuV2mPlusSemisimple_of_distinctCharacters (zhuDistinctCharacters_of_twistedTopModels ht)

theorem rationality_of_distinctCharacters_resonant
    (hc : V2mPlusZhuDistinctCharacters) (hr : V2mPlusResonantGeneratorComplements) :
    V2mPlusRationalFactGe2 :=
  rationality_of_character_bottom_generator_inputs v2mPlusZhuDimensionBound_holds hc
    V2mPlus_equalBottomZhuLifting hr

/-- No normal-form or polynomial-boundary premise remains. -/
theorem rationality_of_twistedTopModels_resonant
    (ht : V2mPlusTwistedTopModels) (hr : V2mPlusResonantGeneratorComplements) :
    V2mPlusRationalFactGe2 :=
  rationality_of_distinctCharacters_resonant (zhuDistinctCharacters_of_twistedTopModels ht) hr

/-- The two remaining original construction/splitting inputs suffice. -/
theorem rationality_of_twistedTopModels_cyclicLifts
    (ht : V2mPlusTwistedTopModels) (hl : V2mPlusResonantCyclicLifts) :
    V2mPlusRationalFactGe2 :=
  rationality_of_twistedTopModels_resonant ht (resonantGeneratorComplements_of_cyclicLifts hl)

end VOA.Classification.COne
