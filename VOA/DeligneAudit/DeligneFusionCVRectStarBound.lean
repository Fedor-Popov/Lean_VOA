import VOA.DeligneAudit.DeligneFusionCVRectStarRecursion
import VOA.DeligneAudit.DeligneFusionCVRectStarEliminate

/-!
# The well-founded star polynomial upper-count induction

The right and central capacities are generalized in the induction.
Only the total left capacity plus the number of left sites decreases.
No map from mixed CV modules or ordinary three-current action is used.
-/

namespace VOA.DeligneAudit.A2.CVRectStarBound

open VOA.DeligneAudit.A2.CVRectStarFamily
open VOA.DeligneAudit.A2.CVRectStarRecursion
open VOA.DeligneAudit.A2.CVRectStarCount
open VOA.DeligneAudit.A2.CVRectList

noncomputable section

def Bound (left right center : List ℕ) : Prop :=
  FiniteDimensional ℂ (Family left right center) ∧
    Module.finrank ℂ (Family left right center) ≤ starWeight left right center

private theorem bound_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) (hb : Bound left right center) : Bound left' right center := by
  haveI := hb.1
  refine ⟨finiteDimensional_left_perm hp right center, ?_⟩
  rw [← finrank_left_perm hp right center, ← starWeight_perm hp right center]
  exact hb.2

private theorem bound_of_zero_step
    (hzero : ∀ left right center, FiniteDimensional ℂ (Family left right center) →
      FiniteDimensional ℂ (Family (0 :: left) right center) ∧
        Module.finrank ℂ (Family (0 :: left) right center) ≤
          Module.finrank ℂ (Family left right center)) :
    ∀ left right center, Bound left right center := by
  have hall : ∀ m left right center, leafComplexity left = m → Bound left right center := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro left right center hm
      by_cases hl : left = []
      · subst left
        exact base_bound right center
      · obtain ⟨K, ks, hp, hmax⟩ := exists_max_cons left hl
        have hc : leafComplexity (K :: ks) = m := (leafComplexity_perm hp).symm.trans hm
        have hb : Bound (K :: ks) right center := by
          by_cases hK : K = 0
          · subst K
            have hs := ih (leafComplexity ks)
              ((leafComplexity_remove ks 0).trans_eq hc) ks right center rfl
            have hz := hzero ks right center hs.1
            refine ⟨hz.1, hz.2.trans (hs.2.trans_eq ?_)⟩
            exact (starWeight_zero ks right center).symm
          · have hpos : 1 ≤ K := by omega
            have hs := ih (leafComplexity ks)
              ((leafComplexity_remove ks K).trans_eq hc) ks right (K :: center) rfl
            have hd := ih (leafComplexity ((K - 1) :: ks))
              ((leafComplexity_decrement ks K hpos).trans_eq hc)
              ((K - 1) :: ks) right center rfl
            haveI := hs.1
            haveI := hd.1
            have hr := active_family_dimension_step ks right center K hpos hmax
            refine ⟨hr.1, hr.2.trans ((Nat.add_le_add hd.2 hs.2).trans_eq ?_)⟩
            rw [starWeight_active ks right center K hpos]
            omega
        exact bound_perm hp.symm right center hb
  intro left right center
  exact hall (leafComplexity left) left right center rfl

/-- The actual canonical three-color star quotient is finite-dimensional
and has the full rectangular product upper bound. All recursive ideal
and quotient maps have been constructed; no recurrence is an input. -/
theorem family_bound (left right center : List ℕ) : Bound left right center :=
  bound_of_zero_step
    (fun left right center hfd => by
      haveI := hfd
      exact CVRectStarEliminate.left_zero_bound left right center)
    left right center

/-- The two leaf orientations with capacities one, two and three have
the combined actual polynomial `3/6/10` upper bound. This does not
assert a mixed CV-to-PBW presentation. -/
theorem parts_bound (r n e r' n' e' : ℕ) (center : List ℕ) :
    FiniteDimensional ℂ
      (Family (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1)
        (List.replicate r' 3 ++ List.replicate n' 2 ++ List.replicate e' 1) center) ∧
      Module.finrank ℂ
        (Family (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1)
          (List.replicate r' 3 ++ List.replicate n' 2 ++ List.replicate e' 1) center) ≤
        3 ^ (e + e') * 6 ^ (n + n') * 10 ^ (r + r') *
          (center.map (fun k => k + 1)).prod := by
  have hb := family_bound
    (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1)
    (List.replicate r' 3 ++ List.replicate n' 2 ++ List.replicate e' 1) center
  refine ⟨hb.1, ?_⟩
  simpa only [starWeight_parts] using hb.2

#print axioms family_bound
#print axioms parts_bound

end

end VOA.DeligneAudit.A2.CVRectStarBound
