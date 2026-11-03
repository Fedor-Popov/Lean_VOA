import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanFusionAll

/-! The unconditional multiplicity-two positive-span and presented rank bounds. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem twoOne_raising (c : Fin 28) (hc : D4sector.raising c) (r : ℕ) :
    twoOneCurrent.op c r twoOneGen = 0 := by
  change (twoM 1).mkQ (twoCurrent.op c r (twoGen 0)) = 0
  rw [twoGen_raising 0 c hc r, map_zero]

theorem twoOne_cartan_zero (c : Fin 28) (hc : D4sector.cartan c) :
    twoOneCurrent.op c 0 twoOneGen =
      ((D4sector.thetaH c : ℕ) : ℂ) • twoOneGen := by
  change (twoM 1).mkQ (twoCurrent.op c 0 (twoGen 0)) = _
  rw [twoGen_cartan_zero 0 c hc, map_smul]
  rfl

private theorem lowering_cases : ∀ c : Fin 28, D4sector.lowering c →
    c = negativeIndex 0 ∨ c = negativeIndex 1 ∨
      c = negativeIndex 2 ∨ c = negativeIndex 3 := by
  intro c hc
  change 16 ≤ c.val ∧ c.val < 20 at hc
  have hv : c.val = 16 ∨ c.val = 17 ∨ c.val = 18 ∨ c.val = 19 := by omega
  rcases hv with h0 | h1 | h2 | h3
  · left
    apply Fin.ext
    simpa [negativeIndex] using h0
  · right; left
    apply Fin.ext
    simpa [negativeIndex] using h1
  · right; right; left
    apply Fin.ext
    simpa [negativeIndex] using h2
  · right; right; right
    apply Fin.ext
    simpa [negativeIndex] using h3

theorem twoGen_one_lowering (c : Fin 28) (hc : D4sector.lowering c) :
    (twoCurrent.op c 0)^[D4sector.lowExp c + 1] (twoGen 1) = 0 := by
  rcases lowering_cases c hc with h0 | h1 | h2 | h3
  · subst c
    simpa [outer_exp_zero (0 : Fin 12) (by decide) (by decide)] using
      twoGen_outer_lowering 1 0 (by decide) (by decide)
  · subst c
    simpa [outer_exp_zero (1 : Fin 12) (by decide) (by decide)] using
      twoGen_outer_lowering 1 1 (by decide) (by decide)
  · subst c
    simpa [D4sector, lowExpD4, negativeIndex] using twoGen_center_lowering 1
  · subst c
    simpa [outer_exp_zero (3 : Fin 12) (by decide) (by decide)] using
      twoGen_outer_lowering 1 3 (by decide) (by decide)

theorem twoOne_lowering (c : Fin 28) (hc : D4sector.lowering c) :
    (twoOneCurrent.op c 0)^[D4sector.lowExp c + 1] twoOneGen = 0 := by
  rcases lowering_cases c hc with h0 | h1 | h2 | h3
  · subst c
    simpa [outer_exp_zero (0 : Fin 12) (by decide) (by decide)] using
      twoOne_outer_lowering 0 (by decide) (by decide)
  · subst c
    simpa [outer_exp_zero (1 : Fin 12) (by decide) (by decide)] using
      twoOne_outer_lowering 1 (by decide) (by decide)
  · subst c
    simpa [D4sector, lowExpD4, negativeIndex] using twoOne_center_lowering
  · subst c
    simpa [outer_exp_zero (3 : Fin 12) (by decide) (by decide)] using
      twoOne_outer_lowering 3 (by decide) (by decide)

theorem twoGen_one_localWeyl :
    LocalWeylRelG D4sector twoCurrent (twoGen 1) 1 where
  raising := twoGen_raising 1
  cartan_pos := twoGen_one_cartan_pos
  cartan_zero := by
    intro c hc
    simpa only [one_mul] using twoGen_cartan_zero 1 c hc
  lowering := by
    intro c hc
    simpa only [one_mul] using twoGen_one_lowering c hc
  fusion := twoGen_one_fusion_all
  cartanN_pos := by
    intro c hc
    exact False.elim hc
  cartanN_zero := by
    intro c hc
    exact False.elim hc

theorem twoOne_localWeyl :
    LocalWeylRelG D4sector twoOneCurrent twoOneGen 1 where
  raising := twoOne_raising
  cartan_pos := twoOne_cartan_pos
  cartan_zero := by
    intro c hc
    simpa only [one_mul] using twoOne_cartan_zero c hc
  lowering := by
    intro c hc
    simpa only [one_mul] using twoOne_lowering c hc
  fusion := twoOne_fusion_all
  cartanN_pos := by
    intro c hc
    exact False.elim hc
  cartanN_zero := by
    intro c hc
    exact False.elim hc

theorem twoPositiveSpanBound : TwoPositiveSpanBound :=
  twoPositiveSpanBound_of_localWeyl
    twoGen_one_localWeyl twoOne_localWeyl

theorem presentedRankBoundE_two : PresentedRankBoundE 2 (by norm_num) :=
  presentedRankBoundE_two_of_span twoPositiveSpanBound

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoOne_raising
#print axioms VOA.DeligneAudit.Toroidal.twoOne_cartan_zero
#print axioms VOA.DeligneAudit.Toroidal.twoGen_one_lowering
#print axioms VOA.DeligneAudit.Toroidal.twoOne_lowering
#print axioms VOA.DeligneAudit.Toroidal.twoGen_one_localWeyl
#print axioms VOA.DeligneAudit.Toroidal.twoOne_localWeyl
#print axioms VOA.DeligneAudit.Toroidal.twoPositiveSpanBound
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_two
