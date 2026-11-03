import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveLeftRecursion
import VOA.DeligneAudit.DeligneFusionCVRectStarCount
import VOA.DeligneAudit.DeligneFusionCVRectList

/-!
# Actual five-family left count from its terminal five-tail base

Every ordinary left site is eliminated by the constructed positive and
zero-site quotient maps. This intermediate theorem takes only the terminal
base count; the public closed count is instantiated separately with the
actual five-tail base theorem once that independent proof is available.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectStarCount
open VOA.DeligneAudit.A2.CVRectList

noncomputable section

def LeftBound (left right center : List ℕ) : Prop :=
  FiniteDimensional ℂ (FiveFamily left right center) ∧
    Module.finrank ℂ (FiveFamily left right center) ≤ 5 * starWeight left right center

private theorem bound_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) (hb : LeftBound left right center) : LeftBound left' right center := by
  haveI := hb.1
  refine ⟨finiteDimensional_left_perm hp right center, ?_⟩
  rw [← finrank_left_perm hp right center, ← starWeight_perm hp right center]
  exact hb.2

/-- The well-founded induction uses actual primitive and shift quotient
recursions; no recurrence or coefficient-ideal inclusion is an input. -/
theorem five_family_bound_of_base
    (hbase : ∀ right center : List ℕ, LeftBound [] right center) :
    ∀ left right center : List ℕ, LeftBound left right center := by
  have hall : ∀ m left right center, leafComplexity left = m →
      LeftBound left right center := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro left right center hm
      by_cases hl : left = []
      · subst left
        exact hbase right center
      · obtain ⟨K, ks, hp, hmax⟩ := exists_max_cons left hl
        have hc : leafComplexity (K :: ks) = m := (leafComplexity_perm hp).symm.trans hm
        have hb : LeftBound (K :: ks) right center := by
          by_cases hK : K = 0
          · subst K
            have hs := ih (leafComplexity ks)
              ((leafComplexity_remove ks 0).trans_eq hc) ks right center rfl
            haveI := hs.1
            have hz := left_zero_bound ks right center
            refine ⟨hz.1, ?_⟩
            simpa only [starWeight_zero] using hz.2.trans hs.2
          · have hpos : 1 ≤ K := by omega
            have hs := ih (leafComplexity ks)
              ((leafComplexity_remove ks K).trans_eq hc) ks right (K :: center) rfl
            have hd := ih (leafComplexity ((K - 1) :: ks))
              ((leafComplexity_decrement ks K hpos).trans_eq hc)
              ((K - 1) :: ks) right center rfl
            haveI := hs.1
            haveI := hd.1
            have hr := left_dimension_step ks right center K hpos hmax
            refine ⟨hr.1, hr.2.trans ((Nat.add_le_add hd.2 hs.2).trans_eq ?_)⟩
            rw [starWeight_active ks right center K hpos]
            omega
        exact bound_perm hp.symm right center hb
  intro left right center
  exact hall (leafComplexity left) left right center rfl

end

end VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveLeft.five_family_bound_of_base
