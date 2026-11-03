import VOA.DeligneAudit.D4FusionContactM2Dimension
import VOA.DeligneAudit.D4FusionContactM2DimensionSource

/-! # The actual D4 multiplicity-two sharp total upper bound

The polynomial model is finite from the checked normal span and 784-word
certificate. Current-degree independence is used in the homogeneous universal
source before mapping to each arbitrary target. Target degree pieces may overlap;
no target-rank sum or source-finiteness premise is used.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.D4
open Polynomial

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V}

theorem localWeyl_two_bound (h : LocalWeylRelG D4sector R w 2) :
    (∀ d, FiniteDimensional ℂ (cycDeg R w d)) ∧
      ∀ B, (∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d)) ≤ 784 := by
  have hQ := m2Model_bound
  letI : FiniteDimensional ℂ M2Model := hQ.1
  have hU := univ_localWeylRelG D4sector 2
  obtain ⟨hfd,hsum⟩ := source_degree_bound_of_surjective_model (lwSpec D4sector 2)
    m2_universal_highest (m2ModelMap hU) (m2ModelMap_surjective hU)
    ((localWeylRelG_iff D4sector R w 2).mp h)
  exact ⟨hfd,fun B => (hsum B).trans hQ.2⟩

theorem localWeyl_two_finite (h : LocalWeylRelG D4sector R w 2) (d : ℕ) :
    FiniteDimensional ℂ (cycDeg R w d) := (localWeyl_two_bound h).1 d

/-- This is the m=2 total dimension bound only, not an all-m D4 input. -/
theorem localWeyl_two_total_dim (h : LocalWeylRelG D4sector R w 2) (B : ℕ) :
    ∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d) ≤ 784 :=
  (localWeyl_two_bound h).2 B

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_two_bound
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_two_finite
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_two_total_dim
