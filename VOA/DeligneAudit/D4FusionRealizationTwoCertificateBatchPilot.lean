/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateBatchPilotPart00
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateBatchPilotPart08
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateBatchPilotPart16
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateBatchPilotPart24

namespace VOA.DeligneAudit.D4Two.Certificate

theorem batchPilot_equality : batchPilotCases.all batchPilotCheck = true := by
  apply batch_all_of_getD batchPilotCases default batchPilotCheck
  have hlen : batchPilotCases.length = 32 := by decide +kernel
  apply (congrArg (fun len => (List.range' 0 len).all
    (fun i => batchPilotCheck (batchPilotCases.getD i default)) = true) hlen).mpr
  exact batch_range_join 0 16 16 16 32 rfl rfl
    (batch_range_join 0 8 8 8 16 rfl rfl batchPilot_part00 batchPilot_part08)
    (batch_range_join 16 8 24 8 16 rfl rfl batchPilot_part16 batchPilot_part24)

end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.batchPilot_equality
