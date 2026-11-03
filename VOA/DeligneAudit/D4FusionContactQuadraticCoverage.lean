import VOA.DeligneAudit.D4FusionContactQuadraticTable
import VOA.DeligneAudit.D4FusionContactTable

/-! The quadratic certificate covers every sorted pair of the eight active roots. -/
namespace VOA.DeligneAudit.D4FusionContact.Quadratic

theorem pair_coverage : ∀ i j : Fin 8,
    (radIndex i.castSucc).val ≤ (radIndex j.castSucc).val →
      ∃ k : Fin 36, pair k = (radIndex i.castSucc, radIndex j.castSucc) := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact.Quadratic

#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.pair_coverage
