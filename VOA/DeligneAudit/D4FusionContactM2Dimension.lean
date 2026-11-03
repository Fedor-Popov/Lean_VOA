import VOA.DeligneAudit.D4FusionContactM2DimensionCore
import VOA.DeligneAudit.D4FusionContactM2Reduction

/-! # The actual m=2 contact polynomial model has rank at most 784

The checked ideal relations give the concrete normal-word span. Its exact
finite count supplies the upper bound. Ambient finiteness is a conclusion.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.D4FusionContact.M2Certificate

noncomputable section

theorem m2Model_bound : FiniteDimensional ℂ M2Model ∧ Module.finrank ℂ M2Model ≤ 784 := by
  have h := finite_finrank_le_of_span_fin
    (fun i : Fin normalEnumeration.length =>
      (m2ModelIdeal.restrictScalars ℂ).mkQ (polyWord ((normalEnumeration.get i).map varIndex)))
    m2_normalEnumeration_span
  simpa only [normalEnumeration_length] using h

theorem m2Model_finite : FiniteDimensional ℂ M2Model := m2Model_bound.1

theorem m2Model_finrank_le : Module.finrank ℂ M2Model ≤ 784 := m2Model_bound.2

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.m2Model_bound
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.m2Model_finite
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.m2Model_finrank_le
