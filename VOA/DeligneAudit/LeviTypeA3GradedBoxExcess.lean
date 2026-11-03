import VOA.DeligneAudit.LeviTypeA3GradedWordResidual

/-! A homogeneous Garland box has no words beyond its weight. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_box_degree_le (m : ℕ) (f : ℕ →₀ ℕ)
    (hf : BoxP m f) : Finsupp.degree f ≤ m := by
  by_cases hzero : f = 0
  · subst f
    simp
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hzero
    have h := hf i hi
    omega

theorem a3_box_weight_first (f : ℕ →₀ ℕ) :
    (Finsupp.weight om f).1 = Finsupp.degree f := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
    Prod.fst_sum, om]

/-- The second box in a pair is empty if its requested word length
exceeds its local Weyl weight. -/
theorem a3PairBoxSpan_eq_bot_of_excess
    (j : Fin 2) (xs zs : List ℕ) (m t d : ℕ) (hmt : m < t) :
    a3PairBoxSpan ρ w j xs zs m t d = ⊥ := by
  rw [a3PairBoxSpan, eq_bot_iff, Submodule.span_le]
  intro v hv
  obtain ⟨f, hf, hw, _⟩ := hv
  have hdeg := a3_box_degree_le m f hf
  have hfst := congrArg Prod.fst hw
  rw [a3_box_weight_first] at hfst
  omega

/-- The first two-box target is empty when either boxed word is too long. -/
theorem a3TwoBoxKeySpan_eq_bot_of_excess (a b : ℕ) (k : A3RadicalKey)
    (hcount : a < k.d₁ ∨ b < k.d₂) :
    a3TwoBoxKeySpan ρ w a b k = ⊥ := by
  rw [a3TwoBoxKeySpan, eq_bot_iff, Submodule.span_le]
  intro v hv
  obtain ⟨f, g, zs, r, s, hf, hg, hwf, hwg, _, _, _⟩ := hv
  rcases hcount with ha | hb
  · have hdeg := a3_box_degree_le a f hf
    have hfst := congrArg Prod.fst hwf
    rw [a3_box_weight_first] at hfst
    omega
  · have hdeg := a3_box_degree_le b g hg
    have hfst := congrArg Prod.fst hwg
    rw [a3_box_weight_first] at hfst
    omega

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_box_degree_le
#print axioms VOA.DeligneAudit.A3Sector.a3_box_weight_first
#print axioms VOA.DeligneAudit.A3Sector.a3PairBoxSpan_eq_bot_of_excess
#print axioms VOA.DeligneAudit.A3Sector.a3TwoBoxKeySpan_eq_bot_of_excess
