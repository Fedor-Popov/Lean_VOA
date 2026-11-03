import VOA.DeligneAudit.DeligneFusionCVRectOneColor
import VOA.DeligneAudit.DeligneFusionCVRectFamilyPerm
import VOA.DeligneAudit.DeligneFusionCVRectEliminate

/-!
# The well-founded count for the actual canonical rectangular family

The positive-capacity branches use the proved canonical quotient
recursions. Zero capacities are removed by actual finite-variable maps.
The count induction decreases capacities plus the number of active
colors, and reorders capacities by exact ideal invariance.
-/

namespace VOA.DeligneAudit.A2.CVRectBound

open VOA.DeligneAudit.A2.CVRectFamily
open VOA.DeligneAudit.A2.CVRectFamilyPerm
open VOA.DeligneAudit.A2.CVRectOneColor
open VOA.DeligneAudit.A2.CVRectCount
open VOA.DeligneAudit.A2.CVRectList
open VOA.DeligneAudit.A2.CVRectEliminate

noncomputable section

def Bound (two one : List ℕ) : Prop :=
  FiniteDimensional ℂ (Family two one) ∧
    Module.finrank ℂ (Family two one) ≤ familyWeight two one

private theorem bound_perm {two two' one one' : List ℕ}
    (ht : two.Perm two') (ho : one.Perm one') (hb : Bound two one) : Bound two' one' := by
  haveI := hb.1
  refine ⟨finiteDimensional_perm ht ho, ?_⟩
  rw [← finrank_perm ht ho, ← familyWeight_perm ht ho]
  exact hb.2

/-- The induction is kept separate from the finite-variable zero-site
construction, so that the latter is supplied by actual proved maps. -/
private theorem bound_of_zero_steps
    (hzeroA : ∀ two one, FiniteDimensional ℂ (Family two one) →
      FiniteDimensional ℂ (Family (0 :: two) one) ∧
        Module.finrank ℂ (Family (0 :: two) one) ≤ Module.finrank ℂ (Family two one))
    (hzeroI : ∀ one, FiniteDimensional ℂ (Family [] one) →
      FiniteDimensional ℂ (Family [] (0 :: one)) ∧
        Module.finrank ℂ (Family [] (0 :: one)) ≤ Module.finrank ℂ (Family [] one)) :
    ∀ two one, Bound two one := by
  have hall : ∀ m two one, complexity two one = m → Bound two one := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro two one hm
      by_cases ht : two = []
      · subst two
        by_cases ho : one = []
        · subst one
          exact ⟨empty_finiteDimensional, by simp only [empty_finrank, familyWeight,
            List.map_nil, List.prod_nil, mul_one, le_refl]⟩
        · obtain ⟨K, ks, hp, hmax⟩ := exists_max_cons one ho
          have hc : complexity [] (K :: ks) = m :=
            (complexity_perm (List.Perm.refl []) hp).symm.trans hm
          have hb : Bound [] (K :: ks) := by
            by_cases hK : K = 0
            · subst K
              have hs := ih (complexity [] ks)
                ((complexity_inactive_remove [] ks 0).trans_eq hc) [] ks rfl
              have hz := hzeroI ks hs.1
              refine ⟨hz.1, hz.2.trans (hs.2.trans_eq ?_)⟩
              exact (familyWeight_inactive_zero [] ks).symm
            · have hpos : 1 ≤ K := by omega
              have hs := ih (complexity [] ks)
                ((complexity_inactive_remove [] ks K).trans_eq hc) [] ks rfl
              have hl := ih (complexity [] ((K - 1) :: ks))
                ((complexity_inactive_decrement [] ks K hpos).trans_eq hc)
                [] ((K - 1) :: ks) rfl
              haveI := hs.1
              haveI := hl.1
              have hd := one_color_dimension_step ks K hpos hmax
              refine ⟨hd.1, hd.2.trans ((Nat.add_le_add hl.2 hs.2).trans_eq ?_)⟩
              rw [familyWeight_inactive [] ks K hpos]
              omega
          exact bound_perm (List.Perm.refl []) hp.symm hb
      · obtain ⟨K, ks, hp, hmax⟩ := exists_max_cons two ht
        have hc : complexity (K :: ks) one = m :=
          (complexity_perm hp (List.Perm.refl one)).symm.trans hm
        have hb : Bound (K :: ks) one := by
          by_cases hK : K = 0
          · subst K
            have hs := ih (complexity ks one)
              ((complexity_active_zero_remove ks one).trans_eq hc) ks one rfl
            have hz := hzeroA ks one hs.1
            refine ⟨hz.1, hz.2.trans (hs.2.trans_eq ?_)⟩
            exact (familyWeight_active_zero ks one).symm
          · have hpos : 1 ≤ K := by omega
            have hs := ih (complexity ks (K :: one))
              ((complexity_shift ks one K).trans_eq hc) ks (K :: one) rfl
            have hl := ih (complexity ((K - 1) :: ks) one)
              ((complexity_active_decrement ks one K hpos).trans_eq hc)
              ((K - 1) :: ks) one rfl
            haveI := hs.1
            haveI := hl.1
            have hd := active_family_dimension_step ks one K hpos hmax
            refine ⟨hd.1, hd.2.trans ((Nat.add_le_add hl.2 hs.2).trans_eq ?_)⟩
            rw [familyWeight_active ks one K hpos]
            omega
        exact bound_perm hp.symm (List.Perm.refl one) hb
  intro two one
  exact hall (complexity two one) two one rfl

/-- The actual finite canonical family has its full product upper bound.
Every recursive map, including both zero-capacity eliminations, has
been constructed from the defining coefficient ideals. -/
theorem family_bound (two one : List ℕ) : Bound two one :=
  bound_of_zero_steps
    (fun two one hfd => by
      haveI := hfd
      exact active_zero_bound two one)
    (fun one hfd => by
      haveI := hfd
      exact inactive_zero_bound [] one)
    two one

/-- The capacities needed by the Deligne one-orientation bases have the
actual bound `3^e 6^n 10^r`, with no dimension or fusion premise. -/
theorem parts_bound (r n e : ℕ) :
    FiniteDimensional ℂ
      (Family (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1) []) ∧
      Module.finrank ℂ
        (Family (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1) []) ≤
          3 ^ e * 6 ^ n * 10 ^ r := by
  have hb := family_bound (List.replicate r 3 ++ List.replicate n 2 ++ List.replicate e 1) []
  refine ⟨hb.1, ?_⟩
  simpa only [familyWeight_parts] using hb.2

#print axioms family_bound
#print axioms parts_bound

end

end VOA.DeligneAudit.A2.CVRectBound
