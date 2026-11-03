/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordCheckData

/-! Column-support bounds are checked separately from coefficient
equalities: no unlisted coordinate may wrap into a tensor index. -/
namespace VOA.DeligneAudit.D4Two.Certificate

def columnRangeChecks : Bool :=
  (List.range 28).all fun c =>
    (List.range 29).all fun j => rangeCheck 29 (rawColumn c j)

theorem column_range_checks : columnRangeChecks = true := by
  decide +kernel

end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.column_range_checks
