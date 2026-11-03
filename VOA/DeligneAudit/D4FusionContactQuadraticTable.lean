import VOA.DeligneAudit.D4FusionContactQuadraticCheck0
import VOA.DeligneAudit.D4FusionContactQuadraticCheck1
import VOA.DeligneAudit.D4FusionContactQuadraticCheck2
import VOA.DeligneAudit.D4FusionContactQuadraticCheck3
import VOA.DeligneAudit.D4FusionContactQuadraticCheck4
import VOA.DeligneAudit.D4FusionContactQuadraticCheck5
import Mathlib.Tactic.FinCases

namespace VOA.DeligneAudit.D4FusionContact.Quadratic

set_option maxRecDepth 100000 in
theorem raw_eq_factor : ∀ r : Fin 27, ∀ j : Fin 36,
    raw r j = factor r * normalized r j := by
  decide +kernel

theorem factor_ne_zero : ∀ r : Fin 27, factor r ≠ 0 := by decide +kernel

theorem normalColumn_injective : Function.Injective normalColumn := by decide +kernel

theorem elimination (j k : Fin 36) : basis j k = eliminationRhs j k := by
  fin_cases j
  · exact eliminate_00 k
  · exact eliminate_01 k
  · exact eliminate_02 k
  · exact eliminate_03 k
  · exact eliminate_04 k
  · exact eliminate_05 k
  · exact eliminate_06 k
  · exact eliminate_07 k
  · exact eliminate_08 k
  · exact eliminate_09 k
  · exact eliminate_10 k
  · exact eliminate_11 k
  · exact eliminate_12 k
  · exact eliminate_13 k
  · exact eliminate_14 k
  · exact eliminate_15 k
  · exact eliminate_16 k
  · exact eliminate_17 k
  · exact eliminate_18 k
  · exact eliminate_19 k
  · exact eliminate_20 k
  · exact eliminate_21 k
  · exact eliminate_22 k
  · exact eliminate_23 k
  · exact eliminate_24 k
  · exact eliminate_25 k
  · exact eliminate_26 k
  · exact eliminate_27 k
  · exact eliminate_28 k
  · exact eliminate_29 k
  · exact eliminate_30 k
  · exact eliminate_31 k
  · exact eliminate_32 k
  · exact eliminate_33 k
  · exact eliminate_34 k
  · exact eliminate_35 k

end VOA.DeligneAudit.D4FusionContact.Quadratic

#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.raw_eq_factor
#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.elimination
