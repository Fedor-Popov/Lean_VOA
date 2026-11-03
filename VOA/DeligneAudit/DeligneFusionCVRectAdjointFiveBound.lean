import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveBase

/-! # The unconditional five-shape tail count from actual quotient maps -/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveBound

open VOA.DeligneAudit.A2.CVRectList
open VOA.DeligneAudit.A2.CVRectStarCount
open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectAdjointFiveOrder
open VOA.DeligneAudit.A2.CVRectAdjointFiveFamily
open VOA.DeligneAudit.A2.CVRectAdjointFiveRecursion

noncomputable section

theorem tail_order_perm {active active' : List ℕ} (hp : active.Perm active')
    (center : List ℕ) : fiveTailOrder active center = fiveTailOrder active' center := by
  funext p q r
  simp only [fiveTailOrder, tailBackground, excess_perm hp]

theorem tail_finiteDimensional_perm {active active' : List ℕ} (hp : active.Perm active')
    (center : List ℕ) [FiniteDimensional ℂ (FiveTailFamily active center)] :
    FiniteDimensional ℂ (FiveTailFamily active' center) := by
  have hf := (inferInstance : FiniteDimensional ℂ (FiveTailFamily active center))
  unfold FiveTailFamily Model ideal at hf ⊢
  rw [hp.length_eq.symm, tail_order_perm hp.symm]
  exact hf

theorem tail_finrank_perm {active active' : List ℕ} (hp : active.Perm active')
    (center : List ℕ) :
    Module.finrank ℂ (FiveTailFamily active center) =
      Module.finrank ℂ (FiveTailFamily active' center) := by
  unfold FiveTailFamily Model ideal
  rw [hp.length_eq, tail_order_perm hp]

def TailBound (active center : List ℕ) : Prop :=
  FiniteDimensional ℂ (FiveTailFamily active center) ∧
    Module.finrank ℂ (FiveTailFamily active center) ≤ 5 * starWeight active [] center

private theorem tail_bound_perm {active active' : List ℕ} (hp : active.Perm active')
    (center : List ℕ) (hb : TailBound active center) : TailBound active' center := by
  haveI := hb.1
  refine ⟨tail_finiteDimensional_perm hp center, ?_⟩
  rw [← tail_finrank_perm hp center, ← starWeight_perm hp [] center]
  exact hb.2

/-- The five-shape polynomial quotient has the actual rectangular
product upper count. Only capacities at least two are recursed; when
all ordinary capacities are at most one the actual `3+2` split applies. -/
theorem five_tail_family_bound (active center : List ℕ) : TailBound active center := by
  have hall : ∀ m active center, leafComplexity active = m → TailBound active center := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro active center hm
      by_cases hsmall : ∀ k ∈ active, k ≤ 1
      · exact CVRectAdjointFiveBase.five_tail_small_bound active center hsmall
      · have hne : active ≠ [] := by
          intro he
          subst active
          exact hsmall (by simp)
        obtain ⟨K, ks, hp, hmax⟩ := exists_max_cons active hne
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
          ((leafComplexity_remove ks K).trans_eq hc) ks (K :: center) rfl
        have hd := ih (leafComplexity ((K - 1) :: ks))
          ((leafComplexity_decrement ks K (by omega)).trans_eq hc) ((K - 1) :: ks) center rfl
        haveI := hs.1
        haveI := hd.1
        have hr := ordinary_tail_dimension_step ks center K hK hmax
        have hb : TailBound (K :: ks) center := by
          refine ⟨hr.1, hr.2.trans ((Nat.add_le_add hd.2 hs.2).trans_eq ?_)⟩
          rw [starWeight_active ks [] center K (by omega)]
          omega
        exact tail_bound_perm hp.symm center hb
  exact hall (leafComplexity active) active center rfl

/-- The no-xy-site branch of the original five-shape family has its
actual count five, by the exact coordinate-swap equivalence. -/
theorem five_base_bound (right center : List ℕ) :
    FiniteDimensional ℂ (FiveFamily [] right center) ∧
      Module.finrank ℂ (FiveFamily [] right center) ≤ 5 * starWeight [] right center := by
  have hb := five_tail_family_bound right center
  haveI := hb.1
  let E := (fiveTailEquiv right center).toLinearEquiv
  refine ⟨E.symm.finiteDimensional, ?_⟩
  rw [E.finrank_eq]
  have hw : starWeight right [] center = starWeight [] right center := by
    simp only [starWeight, List.map_nil, List.prod_nil, mul_one, one_mul]
  simpa only [hw] using hb.2

end
end VOA.DeligneAudit.A2.CVRectAdjointFiveBound

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveBound.five_tail_family_bound
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveBound.five_base_bound
