import VOA.DeligneAudit.D4FusionContactQuadraticSourceData

namespace VOA.DeligneAudit.D4FusionContact.Quadratic.Source
open scoped BigOperators

set_option maxRecDepth 100000 in
theorem recurrence_01 : ∀ k : Fin 36,
    raw 1 k = derive (direction 1) (raw (previous 1)) k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem recurrence_02 : ∀ k : Fin 36,
    raw 2 k = derive (direction 2) (raw (previous 2)) k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem recurrence_03 : ∀ k : Fin 36,
    raw 3 k = derive (direction 3) (raw (previous 3)) k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem recurrence_04 : ∀ k : Fin 36,
    raw 4 k = derive (direction 4) (raw (previous 4)) k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem recurrence_05 : ∀ k : Fin 36,
    raw 5 k = derive (direction 5) (raw (previous 5)) k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem recurrence_06 : ∀ k : Fin 36,
    raw 6 k = derive (direction 6) (raw (previous 6)) k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem recurrence_07 : ∀ k : Fin 36,
    raw 7 k = derive (direction 7) (raw (previous 7)) k := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem recurrence_08 : ∀ k : Fin 36,
    raw 8 k = derive (direction 8) (raw (previous 8)) k := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact.Quadratic.Source
