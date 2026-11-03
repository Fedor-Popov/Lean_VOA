/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieSteps
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4LieStepsDCheck000N04
import VOA.DeligneAudit.F4LieStepsDCheck004N04
import VOA.DeligneAudit.F4LieStepsDCheck008N04
import VOA.DeligneAudit.F4LieStepsDCheck012N04
import VOA.DeligneAudit.F4LieStepsDCheck016N04
import VOA.DeligneAudit.F4LieStepsDCheck020N04
import VOA.DeligneAudit.F4LieStepsDCheck024N04
import VOA.DeligneAudit.F4LieStepsDCheck028N04
import VOA.DeligneAudit.F4LieStepsDCheck032N04
import VOA.DeligneAudit.F4LieStepsDCheck036N04
import VOA.DeligneAudit.F4LieStepsDCheck040N04
import VOA.DeligneAudit.F4LieStepsDCheck044N04
import VOA.DeligneAudit.F4LieStepsDCheck048N04
import VOA.DeligneAudit.F4LieStepsDCheck052N04
import VOA.DeligneAudit.F4LieStepsDCheck056N04
import VOA.DeligneAudit.F4LieStepsDCheck060N04
import VOA.DeligneAudit.F4LieStepsDCheck064N04
import VOA.DeligneAudit.F4LieStepsDCheck068N04
import VOA.DeligneAudit.F4LieStepsDCheck072N04
import VOA.DeligneAudit.F4LieStepsDCheck076N04

/-! # `F₄` propagation steps, block D (bounded kernel checks) -/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

theorem f4StepsD_ok : f4StepsD.all stepOK = true := by
  apply f4_all_of_getD f4StepsD (0, 0, 0) stepOK
  exact f4_range_length 0 f4StepsD.length 80 (by decide +kernel)
    (f4_range_join 0 40 40 40 80 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 20 20 20 40 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 8 8 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 4 4 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_d_r000_n04
    f4_step_d_r004_n04)
    (f4_range_join 8 4 12 8 12 (by decide +kernel) (by decide +kernel)
    f4_step_d_r008_n04
    (f4_range_join 12 4 16 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_d_r012_n04
    f4_step_d_r016_n04)))
    (f4_range_join 20 8 28 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 20 4 24 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_d_r020_n04
    f4_step_d_r024_n04)
    (f4_range_join 28 4 32 8 12 (by decide +kernel) (by decide +kernel)
    f4_step_d_r028_n04
    (f4_range_join 32 4 36 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_d_r032_n04
    f4_step_d_r036_n04))))
    (f4_range_join 40 20 60 20 40 (by decide +kernel) (by decide +kernel)
    (f4_range_join 40 8 48 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 40 4 44 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_d_r040_n04
    f4_step_d_r044_n04)
    (f4_range_join 48 4 52 8 12 (by decide +kernel) (by decide +kernel)
    f4_step_d_r048_n04
    (f4_range_join 52 4 56 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_d_r052_n04
    f4_step_d_r056_n04)))
    (f4_range_join 60 8 68 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 60 4 64 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_d_r060_n04
    f4_step_d_r064_n04)
    (f4_range_join 68 4 72 8 12 (by decide +kernel) (by decide +kernel)
    f4_step_d_r068_n04
    (f4_range_join 72 4 76 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_d_r072_n04
    f4_step_d_r076_n04)))))

#print axioms f4StepsD_ok

end VOA.DeligneAudit.DeligneSector.F4
