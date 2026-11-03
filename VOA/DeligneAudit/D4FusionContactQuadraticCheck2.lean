import VOA.DeligneAudit.D4FusionContactQuadraticData

namespace VOA.DeligneAudit.D4FusionContact.Quadratic

set_option maxRecDepth 100000 in
theorem eliminate_12 : ∀ k : Fin 36, basis 12 k = eliminationRhs 12 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_13 : ∀ k : Fin 36, basis 13 k = eliminationRhs 13 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_14 : ∀ k : Fin 36, basis 14 k = eliminationRhs 14 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_15 : ∀ k : Fin 36, basis 15 k = eliminationRhs 15 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_16 : ∀ k : Fin 36, basis 16 k = eliminationRhs 16 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_17 : ∀ k : Fin 36, basis 17 k = eliminationRhs 17 k := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact.Quadratic
