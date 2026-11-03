import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanFusionOuter

/-! Exhaustion of the twelve D₄ fusion colours. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

noncomputable section

private theorem fusion_cases : ∀ c : Fin 28, 16 ≤ c.val →
    c = D4sector.c₀ ∨
      (∃ i : Fin 8, radIndex i.castSucc = c) ∨
      c = negativeIndex 0 ∨ c = negativeIndex 1 ∨ c = negativeIndex 3 := by
  decide +kernel

theorem twoGen_one_fusion_all (c : Fin 28) (hc : D4sector.fusion c) :
    twoCurrent.op c 1 (twoGen 1) = 0 := by
  have hc' : 16 ≤ c.val := hc
  rcases fusion_cases c hc' with hθ | ⟨i, hi⟩ | h0 | h1 | h3
  · subst c
    exact twoGen_one_theta_fusion
  · subst c
    exact twoGen_one_rad_fusion i
  · subst c
    exact twoGen_outer_fusion 1 0 (by decide) (by decide)
  · subst c
    exact twoGen_outer_fusion 1 1 (by decide) (by decide)
  · subst c
    exact twoGen_outer_fusion 1 3 (by decide) (by decide)

theorem twoOne_fusion_all (c : Fin 28) (hc : D4sector.fusion c) :
    twoOneCurrent.op c 1 twoOneGen = 0 := by
  have hc' : 16 ≤ c.val := hc
  rcases fusion_cases c hc' with hθ | ⟨i, hi⟩ | h0 | h1 | h3
  · subst c
    exact twoOne_theta_fusion
  · subst c
    exact twoOne_rad_fusion i
  · subst c
    exact twoOne_outer_fusion 0 (by decide) (by decide)
  · subst c
    exact twoOne_outer_fusion 1 (by decide) (by decide)
  · subst c
    exact twoOne_outer_fusion 3 (by decide) (by decide)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoGen_one_fusion_all
#print axioms VOA.DeligneAudit.Toroidal.twoOne_fusion_all
