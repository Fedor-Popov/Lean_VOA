import VOA.DeligneAudit.D4FusionContactQuadraticData

namespace VOA.DeligneAudit.D4FusionContact.Quadratic

set_option maxRecDepth 100000 in
theorem eliminate_00 : ∀ k : Fin 36, basis 0 k = eliminationRhs 0 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_01 : ∀ k : Fin 36, basis 1 k = eliminationRhs 1 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_02 : ∀ k : Fin 36, basis 2 k = eliminationRhs 2 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_03 : ∀ k : Fin 36, basis 3 k = eliminationRhs 3 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_04 : ∀ k : Fin 36, basis 4 k = eliminationRhs 4 k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eliminate_05 : ∀ k : Fin 36, basis 5 k = eliminationRhs 5 k := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact.Quadratic
