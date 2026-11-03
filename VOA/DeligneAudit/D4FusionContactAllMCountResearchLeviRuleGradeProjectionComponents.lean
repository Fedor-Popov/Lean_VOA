import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleGradeProjection

/-! Exact homogeneous-component equality and a coordinatewise interface
for simultaneous PBW, current, C and color gradings. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
noncomputable section

variable {K σ ι M κ : Type*} [CommSemiring K] [AddCommMonoid M]

theorem matching_span_eq_ideal_component (w : σ → M)
    (f : ι → MvPolynomial σ K) (d : ι → M)
    (hf : ∀ i, (f i).IsWeightedHomogeneous w (d i)) (n : M) :
    Submodule.span K (matchingGradeProducts w f d n) =
      (Ideal.span (Set.range f)).restrictScalars K ⊓
        MvPolynomial.weightedHomogeneousSubmodule K w n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨i,e,he,rfl⟩
    constructor
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
    · have hg := (MvPolynomial.isWeightedHomogeneous_monomial w e (1:K) rfl).mul (hf i)
      rw [he] at hg
      exact hg
  · intro p hp
    exact homogeneous_ideal_mem_matching_span w f d hf hp.1 hp.2

/-- Combining separately proved degrees requires no extra multigrading datum. -/
theorem weighted_pi_iff (w : σ → κ → M) (n : κ → M) (p : MvPolynomial σ K) :
    p.IsWeightedHomogeneous w n ↔
      ∀ j, p.IsWeightedHomogeneous (fun i => w i j) (n j) := by
  have heval (e : σ →₀ ℕ) (j : κ) :
      Finsupp.weight w e j=Finsupp.weight (fun i => w i j) e := by
    simp only [Finsupp.weight_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply]
  constructor
  · intro hp j e he
    rw [← heval]
    exact congrFun (hp he) j
  · intro hp e he
    funext j
    rw [heval]
    exact hp j he

end
#print axioms matching_span_eq_ideal_component
#print axioms weighted_pi_iff
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
