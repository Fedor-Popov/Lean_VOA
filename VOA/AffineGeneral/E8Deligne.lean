/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.E8Dimension
import VOA.AffineGeneral.DeligneInstance

/-!
# The Deligne case `E₈` on `L_{-6}(𝔢₈)`

`e8Data` is Lie data for `e8Lie = (V_{E₈})₁` in the normalization `Killing/60` (so `h = 30`), indexed by
`Fin 248 = Fin (currentDimension E₈)` through `finrank_e8Lie` (`LieData.reindex`).  On
`L_{-6}(𝔢₈) = simpleVOA e8Data (-6) _` the general Deligne chain gives the `C₂` presentation and
`CurrentJetSurjectivity` (`e8_currentJetSurjectivity`), so the `E₈` case rests only on the two remaining
packages (`e8_classicallyFree_of_two_inputs`).

The level `-6 = -h∨/6 - 1` is the Deligne level for `h∨ = 30`.  That `Killing/60` is the normalization
with roots of length `2` is `Normalization.e8_standard` (`LatticeNormalization`).
-/

namespace VOA.AffineGeneral

namespace E8Deligne

open VOA.AffineGeneral.CartanSimple VOA.AffineGeneral.E8Dim VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- Lie data for `𝔢₈` (form `Killing/60`, `h = 30`), indexed by `Fin 248`. -/
def e8Data : LieData ((2 * 30 : ℂ)⁻¹ • killingForm ℂ e8Lie) (Fin HigherRankDeligneCase.E8.currentDimension) :=
  (standardData e8Lie 30 (by norm_num)).reindex (finCongr finrank_e8Lie)

theorem e8Data_h : e8Data.h = 30 := by
  rw [e8Data, LieData.reindex_h, standardData_h]

theorem e8_level_ne : (-6 : ℂ) + e8Data.h ≠ 0 := by
  rw [e8Data_h]; norm_num

/-- **`L_{-6}(𝔢₈)`.** -/
abbrev e8SimpleVOA := simpleVOA e8Data (-6) e8_level_ne

/-- **`CurrentJetSurjectivity` for the Deligne case `E₈`.** -/
theorem e8_currentJetSurjectivity :
    CurrentJetSurjectivity .E8 e8SimpleVOA (Deligne.presentation .E8 e8Data (-6) e8_level_ne) :=
  Deligne.currentJetSurjectivity .E8 e8Data (-6) e8_level_ne

/-- **The Deligne case `E₈`, conditional on the two remaining packages.** -/
theorem e8_classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .E8 e8SimpleVOA
      (Deligne.presentation .E8 e8Data (-6) e8_level_ne) Carrier)
    (hchar : OrdinaryCarrierCharacter e8SimpleVOA Carrier) :
    CaseClassicallyFree .E8 e8SimpleVOA (Deligne.presentation .E8 e8Data (-6) e8_level_ne) :=
  Deligne.classicallyFree_of_two_inputs .E8 e8Data (-6) e8_level_ne Carrier hgeom hchar

end

end E8Deligne

end VOA.AffineGeneral
