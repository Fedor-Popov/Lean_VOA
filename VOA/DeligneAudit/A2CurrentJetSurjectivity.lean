/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Instance
import VOA.Filtered.GeneratorCurrentLiSpanning
import VOA.Examples.AffineSl3Reconstruction

/-!
# `CurrentJetSurjectivity` for every Deligne case with current spanning, and for A₂ outright

* `currentJetSurjectivity_of_genWordSpan`: for any case and any VOA, the capstone package
  `CurrentJetSurjectivity` follows from `GeneratorWordsSpanLiFiltration` of the currents (Li's
  filtration is spanned by current words of the right depth).  This replaces the unusable
  `hdec` route (`span(gen ∪ {1}) ⊔ C₂ = ⊤`, false for every Deligne VOA).
* `A2.genWordsSpan`: Li's filtration of the actual simple `L_{-3/2}(sl₃)` is spanned by current
  words.  Proof: the sl₃ current commutator gives the tracked estimate on the universal VOA
  (`generatorModeTracked_of_current_comm`), current words span it (`wordStateA_span`), and the
  property descends to the maximal quotient.
* `A2.currentJetSurjectivity`: the A₂ package is **discharged**.  The A₂ capstone rests on
  the two remaining packages only (`A2.classicallyFree_of_two_inputs`).
-/

namespace VOA.DeligneAudit

open VOA.AffineSl3 VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- **Current-word spanning of Li's filtration discharges `CurrentJetSurjectivity`**, for any
Deligne case and any VOA. -/
theorem currentJetSurjectivity_of_genWordSpan {V : Type*} [AddCommGroup V] [Module ℂ V]
    {case : HigherRankDeligneCase} {W : VertexOperatorAlgebra V}
    (P : CurrentC2Presentation case W)
    (h : GeneratorWordsSpanLiFiltration W P.gen (fun _ => 1)) :
    CurrentJetSurjectivity case W P :=
  ⟨fun p N => liPresentedJetBidegreeMap_surjective_of_genWordSpan W P.gen (fun _ => 1)
      P.gen_weight_one h P.ideal P.relations_vanish p N,
    liInfinitePresentedJetMap_surjective_of_genWordSpan W P.gen (fun _ => 1)
      P.gen_weight_one h P.ideal P.relations_vanish⟩

namespace A2

/-- The universal affine `sl₃` VOA at the Deligne level. -/
abbrev U := affineSl3VOA (-3 / 2) level_add_three_ne_zero

/-- The eight universal Chevalley current states. -/
abbrev ugen (a : Fin 8) : Vacuum (-3 / 2) := currentState (-3 / 2) (generator a)

theorem smul_ugen (a : Fin 8) (m : ℤ) (v : Vacuum (-3 / 2)) :
    U.smul (ugen a) m v = J (-3 / 2) a m v := by
  change mode (YA (-3 / 2) level_add_three_ne_zero (currentState (-3 / 2) (generator a))) m v = _
  rw [mode_YA_currentState]
  rfl

theorem genWordState_ugen (l : List (Fin 8 × ℕ)) :
    genWordState U ugen (fun _ => 1) l = wordStateA (-3 / 2) l := by
  induction l with
  | nil => rfl
  | cons ar rest ih =>
      obtain ⟨a, r⟩ := ar
      rw [genWordState_cons, smul_ugen, ih, wordStateA_cons]

/-- Li's filtration of the universal `V^{-3/2}(sl₃)` is spanned by current words. -/
theorem universal_genWordsSpan : GeneratorWordsSpanLiFiltration U ugen (fun _ => 1) := by
  apply generatorWordsSpanLiFiltration_of_tracked
  · exact generatorModeTracked_of_current_comm (J (-3 / 2)) structureConstant
      (fun a b m => (m : ℂ) * (-3 / 2) * formTable a b) smul_ugen
      (fun a b m p => by
        rw [current_comm]
        rfl)
      (fun a m hm => J_vacuum_nonneg (-3 / 2) a hm)
  · rw [show genWordState U ugen (fun _ => 1) = wordStateA (-3 / 2) from
      funext genWordState_ugen]
    exact wordStateA_span (-3 / 2)

/-- **Li's filtration of the actual simple `L_{-3/2}(sl₃)` is spanned by current words.** -/
theorem genWordsSpan : GeneratorWordsSpanLiFiltration W presentation.gen (fun _ => 1) :=
  generatorWordsSpanLiFiltration_quotient (QuotVOA.maxGradedIdeal U)
    (QuotVOA.maxGradedIdeal_isIdeal U) (QuotVOA.maxGradedIdeal_isGradedIdeal U)
    universal_genWordsSpan

/-- **The A₂ `CurrentJetSurjectivity` package, discharged.** -/
theorem currentJetSurjectivity : CurrentJetSurjectivity .A2 W presentation :=
  currentJetSurjectivity_of_genWordSpan presentation genWordsSpan

/-- **A₂ Deligne case, conditional on the two remaining packages.** -/
theorem classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .A2 W presentation Carrier)
    (hchar : OrdinaryCarrierCharacter W Carrier) :
    CaseClassicallyFree .A2 W presentation :=
  classicallyFree_of_inputs Carrier currentJetSurjectivity hgeom hchar

end A2

end

end VOA.DeligneAudit
