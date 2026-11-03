import VOA.DeligneAudit.D4FusionContactPolynomialGrDimensionUniversal

/-! Actual universal PBW rank bounds imply sums of current-degree bounds
in arbitrary ungraded sources. Universal degree projections prove the only
independence used. Source FD, flatness and dimension bounds are not premises. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

noncomputable section
variable (spec : RelSpec 28)

abbrev universalPBWGr := Gr (univRepG contactF spec) (wUG contactF spec)

section UniversalBound
variable [FiniteDimensional ℂ (universalPBWGr spec)]

/-- Actual universal highest relations and finite PBW symbols imply actual
universal source finiteness and rank, without assuming the latter. -/
theorem universal_source_bound {m : ℕ}
    (hU : HighestRel (univRepG contactF spec) (wUG contactF spec) m) :
    FiniteDimensional ℂ (UModG contactF spec) ∧
      Module.finrank ℂ (UModG contactF spec) ≤ Module.finrank ℂ (universalPBWGr spec) :=
  source_bound_of_span _ _ hU (universal_word_span contactF spec)

/-- Every current-degree piece of an arbitrary source is finite, and every
finite sum of its degree ranks is bounded by the actual universal PBW rank. -/
theorem source_current_degree_bound {m : ℕ}
    (hU : HighestRel (univRepG contactF spec) (wUG contactF spec) m)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {R : CurrentModule contactF V} {w : V} (h : Sat contactF R w spec) :
    (∀ d, FiniteDimensional ℂ (cycDeg R w d)) ∧
      ∀ B, (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤
        Module.finrank ℂ (universalPBWGr spec) := by
  obtain ⟨hfd, hrank⟩ := universal_source_bound spec hU
  letI : FiniteDimensional ℂ (UModG contactF spec) := hfd
  exact ⟨fun d => source_cycDeg_finite_of_univ h d,
    fun B => (sum_source_cycDeg_le_univ h B).trans hrank⟩

end UniversalBound

/-- A genuine finite model quotient mapping onto the actual universal PBW
symbols bounds every arbitrary source's current-degree sum. Its model rank
can then be bounded by the separately proved polynomial count. -/
theorem source_degree_bound_of_surjective_model {m : ℕ}
    (hU : HighestRel (univRepG contactF spec) (wUG contactF spec) m)
    {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [FiniteDimensional ℂ Q]
    (L : Q →ₗ[ℂ] universalPBWGr spec) (hsurj : Function.Surjective L)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {R : CurrentModule contactF V} {w : V} (h : Sat contactF R w spec) :
    (∀ d, FiniteDimensional ℂ (cycDeg R w d)) ∧
      ∀ B, (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤
        Module.finrank ℂ Q := by
  letI : FiniteDimensional ℂ (universalPBWGr spec) := Module.Finite.of_surjective L hsurj
  obtain ⟨hfd, hsum⟩ := source_current_degree_bound spec hU h
  exact ⟨hfd, fun B => (hsum B).trans (LinearMap.finrank_le_finrank_of_surjective hsurj)⟩

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.universal_source_bound
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_current_degree_bound
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_degree_bound_of_surjective_model
