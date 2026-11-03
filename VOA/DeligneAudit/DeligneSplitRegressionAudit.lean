/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.DeligneAudit.E6Divisor
import VOA.DeligneAudit.E7Divisor
import VOA.DeligneAudit.E7LieSingular
import VOA.DeligneAudit.E8LieSingular

/-!
# Integration audit for the divisor and singular-vector split repairs

Import the four semantic consumers together, including their finite kernel checks.
These audits certify the repaired declarations; they do not discharge the remaining
named inputs of Deligne classical freeness.
-/

#print axioms VOA.DeligneAudit.DeligneDivisor.E6.e6_divisorComparison
#print axioms VOA.DeligneAudit.DeligneDivisor.E7.e7_divisorComparison
#print axioms VOA.DeligneAudit.E7Lie.simpleProjection_sv
#print axioms VOA.DeligneAudit.E8Lie.simpleProjection_sv
