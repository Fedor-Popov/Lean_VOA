import VOA.DeligneAudit.DeligneFusionCVRectAdjointOrdinaryRecursion
import VOA.DeligneAudit.DeligneFusionCVRectAdjointThree
import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveLeftBound

/-!
# The actual adjoint-site polynomial product upper count

Ordinary xy capacities at least two are reduced by their proved
primitive/shift maps. When all ordinary xy capacities are at most one,
the actual adjoint-site split contributes `3+5=8`.
This is a polynomial quotient theorem; CV relation transfer is separate.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointBound

open VOA.DeligneAudit.A2.CVRectList
open VOA.DeligneAudit.A2.CVRectStarCount
open VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectAdjointFamily

noncomputable section

theorem adjoint_order_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) : adjointOrder left right center = adjointOrder left' right center := by
  funext p q r
  simp only [adjointOrder, background, excess_perm hp]

theorem adjoint_finiteDimensional_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) [FiniteDimensional ℂ (AdjointFamily left right center)] :
    FiniteDimensional ℂ (AdjointFamily left' right center) := by
  have hf := (inferInstance : FiniteDimensional ℂ (AdjointFamily left right center))
  unfold AdjointFamily Model ideal at hf ⊢
  rw [hp.length_eq.symm, adjoint_order_perm hp.symm]
  exact hf

theorem adjoint_finrank_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) :
    Module.finrank ℂ (AdjointFamily left right center) =
      Module.finrank ℂ (AdjointFamily left' right center) := by
  unfold AdjointFamily Model ideal
  rw [hp.length_eq, adjoint_order_perm hp]

def AdjointBound (left right center : List ℕ) : Prop :=
  FiniteDimensional ℂ (AdjointFamily left right center) ∧
    Module.finrank ℂ (AdjointFamily left right center) ≤ 8 * starWeight left right center

private theorem adjoint_bound_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) (hb : AdjointBound left right center) :
    AdjointBound left' right center := by
  haveI := hb.1
  refine ⟨adjoint_finiteDimensional_perm hp right center, ?_⟩
  rw [← adjoint_finrank_perm hp right center, ← starWeight_perm hp right center]
  exact hb.2

private theorem adjoint_small_bound (left right center : List ℕ)
    (hleft : ∀ k ∈ left, k ≤ 1) : AdjointBound left right center := by
  have hthree := CVRectAdjointThree.three_family_bound left right center
  have hfive := CVRectAdjointFiveLeft.five_family_bound left right center
  haveI := hthree.1
  haveI := hfive.1
  have hs := CVRectAdjointRecursion.special_family_dimension_step left right center hleft
  refine ⟨hs.1, hs.2.trans ?_⟩
  omega

/-- The adjoint-site polynomial quotient is finite-dimensional with
the full actual `8` times rectangular product upper bound. No dimension
recurrence, ideal inclusion or colon strictness hypothesis is an input. -/
theorem adjoint_family_bound (left right center : List ℕ) : AdjointBound left right center := by
  have hall : ∀ m left right center, leafComplexity left = m → AdjointBound left right center := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro left right center hm
      by_cases hsmall : ∀ k ∈ left, k ≤ 1
      · exact adjoint_small_bound left right center hsmall
      · have hne : left ≠ [] := by
          intro he
          subst left
          exact hsmall (by simp)
        obtain ⟨K, ks, hp, hmax⟩ := exists_max_cons left hne
        have hK : 2 ≤ K := by
          by_contra hK
          apply hsmall
          intro k hk
          rcases List.mem_cons.mp (hp.mem_iff.mp hk) with rfl | hk'
          · omega
          · have hh := hmax k hk'
            omega
        have hc : leafComplexity (K :: ks) = m := (leafComplexity_perm hp).symm.trans hm
        have hs := ih (leafComplexity ks)
          ((leafComplexity_remove ks K).trans_eq hc) ks right (K :: center) rfl
        have hd := ih (leafComplexity ((K - 1) :: ks))
          ((leafComplexity_decrement ks K (by omega)).trans_eq hc)
          ((K - 1) :: ks) right center rfl
        haveI := hs.1
        haveI := hd.1
        have hr := CVRectAdjointOrdinaryRecursion.ordinary_adjoint_dimension_step
          ks right center K hK hmax
        have hb : AdjointBound (K :: ks) right center := by
          refine ⟨hr.1, hr.2.trans ((Nat.add_le_add hd.2 hs.2).trans_eq ?_)⟩
          rw [starWeight_active ks right center K (by omega)]
          omega
        exact adjoint_bound_perm hp.symm right center hb
  exact hall (leafComplexity left) left right center rfl

/-- The residual-theta specialization has the actual polynomial count
`8 * 10^(a+b)`, uniformly in the two rectangular multiplicities. -/
theorem adjoint_cubes_bound (a b : ℕ) :
    FiniteDimensional ℂ (AdjointFamily (List.replicate a 3) (List.replicate b 3) []) ∧
      Module.finrank ℂ (AdjointFamily (List.replicate a 3) (List.replicate b 3) []) ≤
        8 * 10 ^ (a + b) := by
  have hb := adjoint_family_bound (List.replicate a 3) (List.replicate b 3) []
  have hw : starWeight (List.replicate a 3) (List.replicate b 3) [] = 10 ^ (a + b) := by
    simp only [starWeight, List.map_replicate, List.prod_replicate, List.map_nil,
      List.prod_nil, CVRectCount.rectangleWeight_three, mul_one, pow_add]
  exact ⟨hb.1, by simpa only [hw] using hb.2⟩

end
end VOA.DeligneAudit.A2.CVRectAdjointBound

#print axioms VOA.DeligneAudit.A2.CVRectAdjointBound.adjoint_family_bound
#print axioms VOA.DeligneAudit.A2.CVRectAdjointBound.adjoint_cubes_bound
