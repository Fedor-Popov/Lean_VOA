/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.DeligneInstance
import VOA.AffineGeneral.Sl3Instance

/-!
# The A₂ Deligne case through the general construction

A check that the general route applies end to end: with `D := sl3Data` (trace form, `h = 3`) at the
A₂ Deligne level `k = -3/2`, `Deligne.currentJetSurjectivity` and
`Deligne.classicallyFree_of_two_inputs` instantiate on `L_{-3/2}(sl₃) = simpleVOA sl3Data (-3/2) _`,
leaving the same two packages as the bespoke `DeligneAudit.A2` route.
-/

namespace VOA.AffineGeneral.A2General

open VOA.AffineGeneral VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- `sl3Data`, indexed by the A₂ current dimension. -/
abbrev D : LieData AffineSl3.form (Fin (HigherRankDeligneCase.currentDimension .A2)) := sl3Data

theorem level_ne : (-3 / 2 : ℂ) + D.h ≠ 0 := by
  show (-3 / 2 : ℂ) + 3 ≠ 0
  norm_num

/-- `CurrentJetSurjectivity` for A₂ through the general construction. -/
theorem currentJetSurjectivity :
    CurrentJetSurjectivity .A2 (simpleVOA D (-3 / 2) level_ne)
      (Deligne.presentation .A2 D (-3 / 2) level_ne) :=
  Deligne.currentJetSurjectivity .A2 D (-3 / 2) level_ne

/-- The A₂ Deligne case on the general `L_{-3/2}(sl₃)`, conditional on the two remaining packages. -/
theorem classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .A2 (simpleVOA D (-3 / 2) level_ne)
      (Deligne.presentation .A2 D (-3 / 2) level_ne) Carrier)
    (hchar : OrdinaryCarrierCharacter (simpleVOA D (-3 / 2) level_ne) Carrier) :
    CaseClassicallyFree .A2 (simpleVOA D (-3 / 2) level_ne)
      (Deligne.presentation .A2 D (-3 / 2) level_ne) :=
  Deligne.classicallyFree_of_two_inputs .A2 D (-3 / 2) level_ne Carrier hgeom hchar

end

end VOA.AffineGeneral.A2General
