/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4LieSteps
import VOA.DeligneAudit.F4SectorChecksAssembly
import VOA.DeligneAudit.F4StepCheckC000N04
import VOA.DeligneAudit.F4StepCheckC004N04
import VOA.DeligneAudit.F4StepCheckC008N04
import VOA.DeligneAudit.F4StepCheckC012N04
import VOA.DeligneAudit.F4StepCheckC016N04
import VOA.DeligneAudit.F4StepCheckC020N04
import VOA.DeligneAudit.F4StepCheckC024N04
import VOA.DeligneAudit.F4StepCheckC028N04
import VOA.DeligneAudit.F4StepCheckC032N04
import VOA.DeligneAudit.F4StepCheckC036N04
import VOA.DeligneAudit.F4StepCheckC040N04
import VOA.DeligneAudit.F4StepCheckC044N04
import VOA.DeligneAudit.F4StepCheckC048N04
import VOA.DeligneAudit.F4StepCheckC052N04
import VOA.DeligneAudit.F4StepCheckC056N04
import VOA.DeligneAudit.F4StepCheckC060N04
import VOA.DeligneAudit.F4StepCheckC064N04
import VOA.DeligneAudit.F4StepCheckC068N04
import VOA.DeligneAudit.F4StepCheckC072N04
import VOA.DeligneAudit.F4StepCheckC076N04
import VOA.DeligneAudit.F4StepCheckC080N01

/-! Small independently checked F4 certificate ranges. -/
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem f4StepsC_ok : f4StepsC.all stepOK = true := by
  apply f4_all_of_getD f4StepsC (0, 0, 0) stepOK
  exact f4_range_length 0 f4StepsC.length 81 (by decide +kernel)
    (f4_range_join 0 40 40 41 81 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 20 20 20 40 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 8 8 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 0 4 4 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_c_r000_n04
    f4_step_c_r004_n04)
    (f4_range_join 8 4 12 8 12 (by decide +kernel) (by decide +kernel)
    f4_step_c_r008_n04
    (f4_range_join 12 4 16 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_c_r012_n04
    f4_step_c_r016_n04)))
    (f4_range_join 20 8 28 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 20 4 24 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_c_r020_n04
    f4_step_c_r024_n04)
    (f4_range_join 28 4 32 8 12 (by decide +kernel) (by decide +kernel)
    f4_step_c_r028_n04
    (f4_range_join 32 4 36 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_c_r032_n04
    f4_step_c_r036_n04))))
    (f4_range_join 40 20 60 21 41 (by decide +kernel) (by decide +kernel)
    (f4_range_join 40 8 48 12 20 (by decide +kernel) (by decide +kernel)
    (f4_range_join 40 4 44 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_c_r040_n04
    f4_step_c_r044_n04)
    (f4_range_join 48 4 52 8 12 (by decide +kernel) (by decide +kernel)
    f4_step_c_r048_n04
    (f4_range_join 52 4 56 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_c_r052_n04
    f4_step_c_r056_n04)))
    (f4_range_join 60 12 72 9 21 (by decide +kernel) (by decide +kernel)
    (f4_range_join 60 4 64 8 12 (by decide +kernel) (by decide +kernel)
    f4_step_c_r060_n04
    (f4_range_join 64 4 68 4 8 (by decide +kernel) (by decide +kernel)
    f4_step_c_r064_n04
    f4_step_c_r068_n04))
    (f4_range_join 72 4 76 5 9 (by decide +kernel) (by decide +kernel)
    f4_step_c_r072_n04
    (f4_range_join 76 4 80 1 5 (by decide +kernel) (by decide +kernel)
    f4_step_c_r076_n04
    f4_step_c_r080_n01)))))

#print axioms f4StepsC_ok

end VOA.DeligneAudit.DeligneSector.F4
