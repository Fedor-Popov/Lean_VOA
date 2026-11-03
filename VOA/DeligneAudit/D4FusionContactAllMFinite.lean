import VOA.DeligneAudit.D4FusionContactAllMCandidate
import VOA.DeligneAudit.D4FusionContactM2Spanning

/-! The proved high-word ideal gives actual finiteness of the all-m
polynomial model. This is a coarse finite spanning theorem; it makes
no claim about the sharp count 28^m. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllM

noncomputable section

theorem model_high_words_zero (m : ℕ) (l : List (Vars m))
    (hl : 2 * m + 1 ≤ l.length) :
    ((modelIdeal m).restrictScalars ℂ).mkQ (wordMonomial ℂ (Vars m) l) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change wordMonomial ℂ (Vars m) l ∈ modelIdeal m
  apply (show highWordIdeal m ≤ modelIdeal m from le_sup_right)
  exact Ideal.subset_span ⟨l, hl, rfl⟩

/-- Actual finiteness, with no source model, rank, flatness or count premise. -/
theorem finite_model (m : ℕ) : FiniteDimensional ℂ (Model m) := by
  apply finite_of_high_words ((modelIdeal m).restrictScalars ℂ).mkQ
    ((modelIdeal m).restrictScalars ℂ).mkQ_surjective (2 * m)
  exact model_high_words_zero m

instance (m : ℕ) : FiniteDimensional ℂ (Model m) := finite_model m

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllM

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.model_high_words_zero
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllM.finite_model
