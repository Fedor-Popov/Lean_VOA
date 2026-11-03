import VOA.DeligneAudit.SL4TAdjointSiteJointFlagAudit
import VOA.DeligneAudit.SL4TAdjointSiteFlatRelation

/-!
# The flat level relation at one adjoint site: declaration and axiom audit

**Status.** The flat level relation `ZeroAdjointFlatRelation B k` is reduced, for all
`B`, `k` with `1 ≤ k` and `2k ≤ B`, to its top blocks with at least two compound letters:

    zeroAdjointFlatRelation_of_topRelation (B k : ℕ) (hkB : 2 * k ≤ B) (hk : 1 ≤ k) :
      AdjointSiteFlatTopRelation B (B - k) → ZeroAdjointFlatRelation B k

and, combined with the ring assembly,

    adjointSiteLawB_of_stratumCount_and_flatTop (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B) :
      OneAdjointStratumCount B k → AdjointSiteFlatTopRelation B (B - k) → AdjointSiteLawB B k.

`AdjointSiteFlatTopRelation B h` is *open*: for `d ≤ B` and `2 ≤ e ≤ d + 1`,
`F(h) D_(d+1-e) (g^(B-d) q^e y^d v) ∈ M_{>(0,d,0)}`. On the blocks with `e ≤ 1` the relation is
proved with no further hypotheses (`zeroAdjointFlatRelation_unitCompound`).

Why the paper's Proposition 6.3 does not transfer for `e ≥ 2`. The order on first Levi keys
used in Lean (`higherRadicalCounts`: Levi height `k₁ - k₃` first) puts the keys `(1, b, a)`
with `a ≥ 2` *below* `(0, d, 0)`.
The proof of Proposition 6.3 uses `X_d ∈ M_{>(0,d,0)}` and `z · M_{>(0,d',0)} ⊆ M_{>(0,d'+1,0)}`;
both fail for marked words `g^α q^β y^b z^a x v` with `a ≥ 2` (they occur exactly when `e ≥ 2`,
`d ≥ 3`). The convention "every key with an `x`-letter is above `(0, d, 0)`" holds
only for `a ≤ 1`.

Proved, by file (all parameters general):
* `SL4TAdjointSiteFlatKernel`: the flat kernel space `K₃ = U(p₃ ⊕ 𝔤 t^{≥1}) q g^B v` and
  **Lemma 6.1** (`flatKernelSpace_lastLowering_zero`): `F(h) K₃ = 0`, with the `sl₂(α₂)` step
  `g^(B-1) q q(h) v = 0` (`flatCorner_secondStep`).
* `SL4TAdjointSiteFlatShift`: the flat shift current `H_s = ½((E₂₂-E₃₃)(s) - (E₀₀-E₁₁)(s))`, its
  brackets, the generic Newton-operator lemmas, and the vanishing of `e_f` on fewer than `f`
  shifted letters (`newtonEnd_shift_pow_eq_zero`).
* `SL4TAdjointSiteFlatExpansion`: **Lemma 6.2**, the expansion identity in structural form
  (`flat_expansion`), and **Proposition 6.3 at `e = 1`** (`flatTopRelation_unit`).
* `SL4TAdjointSiteFlatDescent`: the count-layer word induction, **Lemma M(i)**
  (`higherSecondLeviCountClosure_raising_le`), **Lemma 6.4** (`raising_topWord`) and the descent
  in the first second-level count (`secondLevi_topWord_descent`).
* `SL4TAdjointSiteFlatRelation`: the Newton reconstruction of `b₀ = e_f(g₂′)`
  (`newtonCoeff_flatShiftSymbol`), its realization (`flatSymbol_secondLevi_val`), the block
  theorem (`adjointSite_flatRelation_of_top`) and the consequences above.

Axiom check: the 138 declarations of the five content files are printed below: 136 depend on
exactly `[propext, Classical.choice, Quot.sound]`; the two predicates `flatParabolicColour` and
`FlatKernelLetter` depend on `[propext, Quot.sound]`. No `sorry`, `admit`, `native_decide`,
`push_neg` or project axiom is used.
-/

-- SL4TAdjointSiteFlatKernel.lean
#print axioms VOA.DeligneAudit.SL4T.flatParabolicColour
#print axioms VOA.DeligneAudit.SL4T.FlatKernelLetter
#print axioms VOA.DeligneAudit.SL4T.bracket_last_flatParabolic
#print axioms VOA.DeligneAudit.SL4T.bracket_raising_lastPair
#print axioms VOA.DeligneAudit.SL4T.bracket_middleCartan_lastPair
#print axioms VOA.DeligneAudit.SL4T.bracket_raising_middle
#print axioms VOA.DeligneAudit.SL4T.bracket_middleCartan_middle
#print axioms VOA.DeligneAudit.SL4T.bracket_middle_lastPair_zero
#print axioms VOA.DeligneAudit.SL4T.bracket_lastPair_middle_zero
#print axioms VOA.DeligneAudit.SL4T.flatCornerVector
#print axioms VOA.DeligneAudit.SL4T.flatKernelSpace
#print axioms VOA.DeligneAudit.SL4T.flatCornerVector_mem_flatKernelSpace
#print axioms VOA.DeligneAudit.SL4T.flatKernelSpace_letter
#print axioms VOA.DeligneAudit.SL4T.flatKernelSpace_positive
#print axioms VOA.DeligneAudit.SL4T.flatKernelSpace_parabolic
#print axioms VOA.DeligneAudit.SL4T.lastLowering_flatKernelLetter
#print axioms VOA.DeligneAudit.SL4T.flatKernelSpace_lastLowering_of_corner
#print axioms VOA.DeligneAudit.SL4T.flatCorner_secondStep
#print axioms VOA.DeligneAudit.SL4T.flatCorner_lastLowering_zero
#print axioms VOA.DeligneAudit.SL4T.flatKernelSpace_lastLowering_zero
-- SL4TAdjointSiteFlatShift.lean
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_le_comap
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_commute
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_intertwine
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_realizes
#print axioms VOA.DeligneAudit.SL4T.esymm_eq_zero_of_lt
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_shift_pow_eq_zero
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_eq_half
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_comm_of
#print axioms VOA.DeligneAudit.SL4T.bracket_outerCartan_first
#print axioms VOA.DeligneAudit.SL4T.bracket_lastCartan_first
#print axioms VOA.DeligneAudit.SL4T.bracket_outerCartan_compound
#print axioms VOA.DeligneAudit.SL4T.bracket_lastCartan_compound
#print axioms VOA.DeligneAudit.SL4T.bracket_outerCartan_highest
#print axioms VOA.DeligneAudit.SL4T.bracket_lastCartan_highest
#print axioms VOA.DeligneAudit.SL4T.bracket_outerCartan_middle
#print axioms VOA.DeligneAudit.SL4T.bracket_lastCartan_middle
#print axioms VOA.DeligneAudit.SL4T.bracket_outerCartan_lastPair
#print axioms VOA.DeligneAudit.SL4T.bracket_lastCartan_lastPair
#print axioms VOA.DeligneAudit.SL4T.bracket_outerCartan_last
#print axioms VOA.DeligneAudit.SL4T.bracket_lastCartan_last
#print axioms VOA.DeligneAudit.SL4T.bracket_outerCartan_raising
#print axioms VOA.DeligneAudit.SL4T.bracket_lastCartan_raising
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_first
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_compound
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_highest
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_middle
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_lastPair
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_last
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_raising
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_middlePow
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_highestPow
#print axioms VOA.DeligneAudit.SL4T.flatShiftCurrent_source_zero
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_flatShift
#print axioms VOA.DeligneAudit.SL4T.flatKernelSpace_flatShift
#print axioms VOA.DeligneAudit.SL4T.newtonEnd_flatShift_compoundPow_eq_zero
-- SL4TAdjointSiteFlatExpansion.lean
#print axioms VOA.DeligneAudit.SL4T.endomorphism_antiderivation_pow
#print axioms VOA.DeligneAudit.SL4T.bracket_compound_lastPair
#print axioms VOA.DeligneAudit.SL4T.bracket_compound_middle_zero
#print axioms VOA.DeligneAudit.SL4T.bracket_first_middle
#print axioms VOA.DeligneAudit.SL4T.bracket_highest_lastPair
#print axioms VOA.DeligneAudit.SL4T.bracket_highest_middle
#print axioms VOA.DeligneAudit.SL4T.bracket_lastPair_highest
#print axioms VOA.DeligneAudit.SL4T.flatNormalWord
#print axioms VOA.DeligneAudit.SL4T.first_flatNormalWord
#print axioms VOA.DeligneAudit.SL4T.flatLeakWord
#print axioms VOA.DeligneAudit.SL4T.flatMarkedWord
#print axioms VOA.DeligneAudit.SL4T.flatLeakSpan
#print axioms VOA.DeligneAudit.SL4T.flatMarkedSpan
#print axioms VOA.DeligneAudit.SL4T.first_flatLeakWord
#print axioms VOA.DeligneAudit.SL4T.flatNormalWord_zero
#print axioms VOA.DeligneAudit.SL4T.first_flatMarkedWord
#print axioms VOA.DeligneAudit.SL4T.flatMarkedSpan_first
#print axioms VOA.DeligneAudit.SL4T.flatLeakSpan_first
#print axioms VOA.DeligneAudit.SL4T.flat_expansion
#print axioms VOA.DeligneAudit.SL4T.flatLeakWord_corner
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_leviPow
#print axioms VOA.DeligneAudit.SL4T.flatMarkedWord_mem_higherRadical
#print axioms VOA.DeligneAudit.SL4T.firstPow_flatCorner_mem
#print axioms VOA.DeligneAudit.SL4T.flatMarkedSpan_unit_le
#print axioms VOA.DeligneAudit.SL4T.higherRadicalCountClosure_flatNewton
#print axioms VOA.DeligneAudit.SL4T.flatLeakSpan_unit_newton
#print axioms VOA.DeligneAudit.SL4T.flatTopRelation_unit
-- SL4TAdjointSiteFlatDescent.lean
#print axioms VOA.DeligneAudit.SL4T.leviRaising_middle_comm
#print axioms VOA.DeligneAudit.SL4T.leviRaising_compound_comm
#print axioms VOA.DeligneAudit.SL4T.leviOuterRaising_middle_comm
#print axioms VOA.DeligneAudit.SL4T.leviOuterRaising_compound_comm
#print axioms VOA.DeligneAudit.SL4T.leviLastRaising_middle_comm
#print axioms VOA.DeligneAudit.SL4T.leviLastRaising_compound_comm
#print axioms VOA.DeligneAudit.SL4T.leviMiddle_last_comm
#print axioms VOA.DeligneAudit.SL4T.leviCompound_last_comm
#print axioms VOA.DeligneAudit.SL4T.leviLast_raising_comm
#print axioms VOA.DeligneAudit.SL4T.leviMiddleCartan_middlePow
#print axioms VOA.DeligneAudit.SL4T.leviRaising_middlePow
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_le_of_step
#print axioms VOA.DeligneAudit.SL4T.zeroModeSecondWord_mem
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_cartan
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_lastRaising
#print axioms VOA.DeligneAudit.SL4T.secondLeviLastImage
#print axioms VOA.DeligneAudit.SL4T.secondLeviLastImage_mem
#print axioms VOA.DeligneAudit.SL4T.secondLeviLastImage_middle
#print axioms VOA.DeligneAudit.SL4T.secondLeviLastImage_compound
#print axioms VOA.DeligneAudit.SL4T.secondLeviRaisingTarget
#print axioms VOA.DeligneAudit.SL4T.secondLeviOuterRaisingTarget
#print axioms VOA.DeligneAudit.SL4T.secondLeviRaisingTarget_middle
#print axioms VOA.DeligneAudit.SL4T.secondLeviRaisingTarget_compound
#print axioms VOA.DeligneAudit.SL4T.secondLeviOuterRaisingTarget_middle
#print axioms VOA.DeligneAudit.SL4T.secondLeviOuterRaisingTarget_compound
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_raising_target
#print axioms VOA.DeligneAudit.SL4T.secondLeviCountLayer_outerRaising_target
#print axioms VOA.DeligneAudit.SL4T.secondRaisingPreimage
#print axioms VOA.DeligneAudit.SL4T.secondRaisingPreimage_finalLevi
#print axioms VOA.DeligneAudit.SL4T.higherSecondLeviCountClosure_raising_le
#print axioms VOA.DeligneAudit.SL4T.leviRaising_compoundPow
#print axioms VOA.DeligneAudit.SL4T.leviMiddleCartan_compoundPow
#print axioms VOA.DeligneAudit.SL4T.raising_topWord
#print axioms VOA.DeligneAudit.SL4T.secondLevi_topWord_descent
-- SL4TAdjointSiteFlatRelation.lean
#print axioms VOA.DeligneAudit.SL4T.flatShiftSymbol
#print axioms VOA.DeligneAudit.SL4T.newtonCoeff_flatShiftSymbol
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_pow_mk
#print axioms VOA.DeligneAudit.SL4T.flatShiftQuotCurrent
#print axioms VOA.DeligneAudit.SL4T.flatShiftQuotCurrent_mk
#print axioms VOA.DeligneAudit.SL4T.flatShiftQuotCurrent_eq
#print axioms VOA.DeligneAudit.SL4T.flatShiftQuotCurrent_raising_comm
#print axioms VOA.DeligneAudit.SL4T.flatShiftQuotCurrent_lastLowering_comm
#print axioms VOA.DeligneAudit.SL4T.higherSecondLeviCountClosure_flatShift
#print axioms VOA.DeligneAudit.SL4T.flatSymbol_secondLevi_val
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_outerRaising
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_cartan_exists
#print axioms VOA.DeligneAudit.SL4T.radicalGrassmannianAmbientEvaluation_one_weight
#print axioms VOA.DeligneAudit.SL4T.radicalCountQuot_flatTopWord
#print axioms VOA.DeligneAudit.SL4T.flatNewtonLowering_mem_higherSecondLevi
#print axioms VOA.DeligneAudit.SL4T.adjointSite_flatRelation_of_top
#print axioms VOA.DeligneAudit.SL4T.adjointSite_flatTop_of_le_one
#print axioms VOA.DeligneAudit.SL4T.AdjointSiteFlatTopRelation
#print axioms VOA.DeligneAudit.SL4T.zeroAdjointFlatRelation_unitCompound
#print axioms VOA.DeligneAudit.SL4T.zeroAdjointFlatRelation_of_topRelation
#print axioms VOA.DeligneAudit.SL4T.adjointSiteLawB_of_stratumCount_and_flatTop
