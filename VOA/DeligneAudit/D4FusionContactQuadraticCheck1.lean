import VOA.DeligneAudit.D4FusionContactQuadraticData

namespace VOA.DeligneAudit.D4FusionContact.Quadratic

set_option maxRecDepth 100000 in
theorem eliminate_06 : ∀ k : Fin 36, basis 6 k = eliminationRhs 6 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_07 : ∀ k : Fin 36, basis 7 k = eliminationRhs 7 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_08 : ∀ k : Fin 36, basis 8 k = eliminationRhs 8 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_09 : ∀ k : Fin 36, basis 9 k = eliminationRhs 9 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_10 : ∀ k : Fin 36, basis 10 k = eliminationRhs 10 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_11 : ∀ k : Fin 36, basis 11 k = eliminationRhs 11 k := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact.Quadratic
