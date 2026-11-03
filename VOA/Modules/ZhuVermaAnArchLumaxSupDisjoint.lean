/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLumax
import VOA.Modules.ZhuVermaAnArchMUJNaturalCanonical

/-!
# `MaxJData.sup_bottom_disjoint` proved — the maximal-`J` residue drops 3 → 2 fields

`Modules.ZhuVermaAnArchLumax` reduced the per-`U` maximal-`J` datum `LUMaxData` to the residue
`MaxJData D` = `{bottom_regen, sup_bottom_disjoint, quot_submodule_graded}` (with
`J := supBotTrivialGraded` and `quot_graded_simple` *proved* from `bottom_regen`).
`Modules.ZhuVermaAnArchMUJNaturalCanonical` proved, for the canonical `Jcanon`, the surprising
*non-deep* fact that the supremum of bottom-trivial layer-graded submodules is itself bottom-trivial
(`Jcanon_inf_deg0_eq_bot`), via pure layer independence — **no** generation-from-bottom.

This file transports that argument to `Lumax`'s `supBotTrivialGraded` (the sup over *graded*
bottom-trivial submodules) and **proves `MaxJData.sup_bottom_disjoint` as a TERM**.  So the
maximal-`J` residue drops from **three** carried fields to **two**: only `bottom_regen`
(generation-from-bottom, Gannon Thm 5.3.4 / DJ Thm 4.13) and `quot_submodule_graded`
(`L₀`-semisimplicity) remain — the genuine deep DLM content.

## What is built (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`MUModuleData.le_pos_layers_of_layerGraded`** — a layer-graded, bottom-trivial submodule lives
  in the positive layers `⨆_{n≠0} MU.deg n`.
* **`MUModuleData.supBotTrivialGraded_bottom_disjoint`** — **`sup_bottom_disjoint`**: each
  `BotTrivialGraded` summand is layer-graded (`layerGraded_of_isGraded`) + bottom-trivial, hence
  lives in the positive layers; so does their sup, which is therefore disjoint from the bottom
  `MU.deg 0 = M(U)_h` (layer independence, `MU.isInternal_deg`).
* **`MUModuleData.MaxJData.ofRegenSubGraded`** — the `MaxJData` residue from just the two genuine
  deep fields `bottom_regen` + `quot_submodule_graded` (`sup_bottom_disjoint` supplied as the term).

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), §4 (Thm 4.13); DLM3 §4; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchLumax` (`supBotTrivialGraded`, `BotTrivialGraded`, `MaxJData`),
`ZhuVermaAnArchMUJNaturalCanonical` (`layerGraded_of_isGraded`, `Jcanon_inf_deg0_eq_bot`).
-/

namespace VOA

open scoped BigOperators DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace MUModuleData

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-- **A layer-graded, bottom-trivial submodule lives in the positive layers** `⨆_{n≠0} MU.deg n`. -/
theorem le_pos_layers_of_layerGraded (S : Submodule ℂ (MU W U))
    (hlay : InducedAssignment.IsLayerGraded U S)
    (hbot : S ⊓ MU.deg W U 0 = ⊥) :
    S ≤ ⨆ (j : ℕ) (_ : j ≠ 0), MU.deg W U j := by
  rw [hlay]
  refine iSup_le fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [hbot]; exact bot_le
  · exact le_trans inf_le_right (le_iSup₂ (f := fun j _ => MU.deg W U j) n hn)

/-- **`sup_bottom_disjoint`** — the supremum of all bottom-trivial graded submodules is
itself bottom-trivial (`J ⊓ M(U)_h = ⊥`).  Each `BotTrivialGraded` summand is layer-graded
(`layerGraded_of_isGraded` on its `Q_graded`) and bottom-trivial (`Q_disjoint`, with
`M(U)_h = MU.deg 0`), so lives in the positive layers `⨆_{n≠0} MU.deg n`; so does the sup, which is
therefore disjoint from `MU.deg 0` by layer independence.  **No generation-from-bottom needed.** -/
theorem supBotTrivialGraded_bottom_disjoint (D : MUModuleData W U h) :
    (D.supBotTrivialGraded).carrier ⊓ D.toOrdVModule.weight h = ⊥ := by
  have hwh : D.toOrdVModule.weight h = MU.deg W U 0 := by
    rw [MUModuleData.toOrdVModule_weight]; have := D.cweight_cast 0; simpa using this
  have hdisj : Disjoint (MU.deg W U 0) (⨆ (j : ℕ) (_ : j ≠ 0), MU.deg W U j) :=
    iSupIndep_def.mp (MU.isInternal_deg W U).submodule_iSupIndep 0
  rw [hwh]
  have hle : (D.supBotTrivialGraded).carrier ≤ ⨆ (j : ℕ) (_ : j ≠ 0), MU.deg W U j := by
    change (⨆ T : BotTrivialGraded D, T.Q.carrier) ≤ _
    refine iSup_le fun T => ?_
    refine le_pos_layers_of_layerGraded T.Q.carrier
      (InducedAssignment.layerGraded_of_isGraded T.Q_graded) ?_
    rw [← hwh]; exact T.Q_disjoint
  refine le_bot_iff.mp ?_
  calc (D.supBotTrivialGraded).carrier ⊓ MU.deg W U 0
      ≤ (⨆ (j : ℕ) (_ : j ≠ 0), MU.deg W U j) ⊓ MU.deg W U 0 := inf_le_inf_right _ hle
    _ = ⊥ := by rw [inf_comm]; exact disjoint_iff.mp hdisj

/-- **`MaxJData` from just `bottom_regen` + `quot_submodule_graded`.**  With `sup_bottom_disjoint`
supplied as the term `supBotTrivialGraded_bottom_disjoint`, the maximal-`J` residue drops from three
carried fields to two — only generation-from-bottom (`bottom_regen`) and `L₀`-semisimplicity
(`quot_submodule_graded`), the genuine deep DLM content. -/
def MaxJData.ofRegenSubGraded (D : MUModuleData W U h)
    (bottom_regen : ∀ Q : WeakModule.Submodule' D.toOrdVModule.toWeakModule,
      OrdVModule.IsGradedSubmodule D.toOrdVModule Q →
        Q.carrier ⊓ D.toOrdVModule.weight h ≠ ⊥ → Q.carrier = ⊤)
    (quot_submodule_graded : ∀ Q : WeakModule.Submodule'
        (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded
          D.supBotTrivialGraded_isGraded).toWeakModule,
      OrdVModule.IsGradedSubmodule
        (OrdVModule.quotient D.toOrdVModule D.supBotTrivialGraded D.supBotTrivialGraded_isGraded) Q) :
    MaxJData D where
  bottom_regen := bottom_regen
  sup_bottom_disjoint := D.supBotTrivialGraded_bottom_disjoint
  quot_submodule_graded := quot_submodule_graded

end MUModuleData

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
