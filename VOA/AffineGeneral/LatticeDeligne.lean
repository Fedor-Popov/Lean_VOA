/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.RootCounts
import VOA.AffineGeneral.E8Deligne

/-!
# The Deligne cases `D₄`, `E₆`, `E₇` on `L_k(𝔤)`

As in `E8Deligne`: Lie data in the normalization `Killing/(2h)` with `h = 6, 12, 18`, indexed by
`Fin (currentDimension)` through `finrank_d4Lie = 28`, `finrank_e6Lie = 78`, `finrank_e7Lie = 133`; on
`L_{-2}(𝔰𝔬₈)`, `L_{-3}(𝔢₆)`, `L_{-4}(𝔢₇)` the general chain gives `CurrentJetSurjectivity` and the reduction
of each case to the two remaining packages.  That `Killing/(2h)` with these `h` is the standard
normalization (roots of length `2`) is `Normalization.{d4,e6,e7}_standard` (`LatticeNormalization`).
-/

namespace VOA.AffineGeneral.LatticeDeligne

open VOA.AffineGeneral.CartanSimple VOA.AffineGeneral.RootCounts VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-! ## `D4` -/

/-- Lie data for `d4Lie` (form `Killing/12`, `h = 6`), indexed by `Fin 28`. -/
def d4Data :
    LieData ((2 * 6 : ℂ)⁻¹ • killingForm ℂ d4Lie) (Fin HigherRankDeligneCase.D4.currentDimension) :=
  (standardData d4Lie 6 (by norm_num)).reindex (finCongr finrank_d4Lie)

theorem d4Data_h : d4Data.h = 6 := by
  rw [d4Data, LieData.reindex_h, standardData_h]

theorem d4_level_ne : (-2 : ℂ) + d4Data.h ≠ 0 := by
  rw [d4Data_h]; norm_num

/-- `L_{-2}` of `d4Lie`. -/
abbrev d4SimpleVOA := simpleVOA d4Data (-2) d4_level_ne

theorem d4_currentJetSurjectivity :
    CurrentJetSurjectivity .D4 d4SimpleVOA (Deligne.presentation .D4 d4Data (-2) d4_level_ne) :=
  Deligne.currentJetSurjectivity .D4 d4Data (-2) d4_level_ne

/-- **The Deligne case `D4`, conditional on the two remaining packages.** -/
theorem d4_classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .D4 d4SimpleVOA
      (Deligne.presentation .D4 d4Data (-2) d4_level_ne) Carrier)
    (hchar : OrdinaryCarrierCharacter d4SimpleVOA Carrier) :
    CaseClassicallyFree .D4 d4SimpleVOA (Deligne.presentation .D4 d4Data (-2) d4_level_ne) :=
  Deligne.classicallyFree_of_two_inputs .D4 d4Data (-2) d4_level_ne Carrier hgeom hchar

/-! ## `E6` -/

/-- Lie data for `e6Lie` (form `Killing/24`, `h = 12`), indexed by `Fin 78`. -/
def e6Data :
    LieData ((2 * 12 : ℂ)⁻¹ • killingForm ℂ e6Lie) (Fin HigherRankDeligneCase.E6.currentDimension) :=
  (standardData e6Lie 12 (by norm_num)).reindex (finCongr finrank_e6Lie)

theorem e6Data_h : e6Data.h = 12 := by
  rw [e6Data, LieData.reindex_h, standardData_h]

theorem e6_level_ne : (-3 : ℂ) + e6Data.h ≠ 0 := by
  rw [e6Data_h]; norm_num

/-- `L_{-3}` of `e6Lie`. -/
abbrev e6SimpleVOA := simpleVOA e6Data (-3) e6_level_ne

theorem e6_currentJetSurjectivity :
    CurrentJetSurjectivity .E6 e6SimpleVOA (Deligne.presentation .E6 e6Data (-3) e6_level_ne) :=
  Deligne.currentJetSurjectivity .E6 e6Data (-3) e6_level_ne

/-- **The Deligne case `E6`, conditional on the two remaining packages.** -/
theorem e6_classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .E6 e6SimpleVOA
      (Deligne.presentation .E6 e6Data (-3) e6_level_ne) Carrier)
    (hchar : OrdinaryCarrierCharacter e6SimpleVOA Carrier) :
    CaseClassicallyFree .E6 e6SimpleVOA (Deligne.presentation .E6 e6Data (-3) e6_level_ne) :=
  Deligne.classicallyFree_of_two_inputs .E6 e6Data (-3) e6_level_ne Carrier hgeom hchar

/-! ## `E7` -/

/-- Lie data for `e7Lie` (form `Killing/36`, `h = 18`), indexed by `Fin 133`. -/
def e7Data :
    LieData ((2 * 18 : ℂ)⁻¹ • killingForm ℂ e7Lie) (Fin HigherRankDeligneCase.E7.currentDimension) :=
  (standardData e7Lie 18 (by norm_num)).reindex (finCongr finrank_e7Lie)

theorem e7Data_h : e7Data.h = 18 := by
  rw [e7Data, LieData.reindex_h, standardData_h]

theorem e7_level_ne : (-4 : ℂ) + e7Data.h ≠ 0 := by
  rw [e7Data_h]; norm_num

/-- `L_{-4}` of `e7Lie`. -/
abbrev e7SimpleVOA := simpleVOA e7Data (-4) e7_level_ne

theorem e7_currentJetSurjectivity :
    CurrentJetSurjectivity .E7 e7SimpleVOA (Deligne.presentation .E7 e7Data (-4) e7_level_ne) :=
  Deligne.currentJetSurjectivity .E7 e7Data (-4) e7_level_ne

/-- **The Deligne case `E7`, conditional on the two remaining packages.** -/
theorem e7_classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .E7 e7SimpleVOA
      (Deligne.presentation .E7 e7Data (-4) e7_level_ne) Carrier)
    (hchar : OrdinaryCarrierCharacter e7SimpleVOA Carrier) :
    CaseClassicallyFree .E7 e7SimpleVOA (Deligne.presentation .E7 e7Data (-4) e7_level_ne) :=
  Deligne.classicallyFree_of_two_inputs .E7 e7Data (-4) e7_level_ne Carrier hgeom hchar

end

end VOA.AffineGeneral.LatticeDeligne
