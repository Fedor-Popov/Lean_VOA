/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateData
import VOA.DeligneAudit.D4FusionRealizationTwoCertificatePilotData

namespace VOA.DeligneAudit.D4Two.Certificate

theorem pilot_equality :
    zeroOnCheck pilotCoordinates
      (scale pilotDenominator
        (applyColumns (pairColumn 28 (fun i => pilotColumns.getD i []) 15 3) pilotSource) ++
       scale (-1) pilotTarget) = true := by
  decide +kernel

end VOA.DeligneAudit.D4Two.Certificate
