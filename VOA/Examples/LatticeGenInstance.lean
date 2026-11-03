/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenGradedField

/-!
# The general even positive-definite lattice VOA `V_L`

The 19-field `VertexOperatorAlgebra (LatModuleGen L)` instance for an even positive-definite lattice
`L`, central charge `c = rank L`, assembled from the reconstruction-derived vertex map `YfullGen`
and the conformal layer (`omegaLatGen`, `YfullGen_virasoro`, `YfullGen_L0_grading`,
`YfullGen_translation_omega`, `YfullGen_grading_mode`).  Generalizes the A₁ lattice VOA
(`latticeVOA_A1_of_locality`) to arbitrary even positive-definite `L`; `rank = 1` recovers `c = 1`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-- **The general even positive-definite lattice vertex operator algebra** `V_L`, central charge
`c = rank L`.  The charge-pair locality gate is discharged inside `YfullGen`
(`latYfullGen_of_locality`), so this construction is unconditional given `hEven`/`hPos`. -/
noncomputable def latticeVOAGen (hEven : L.Even) (hPos : L.PosDef) :
    VertexOperatorAlgebra (LatModuleGen L) where
  grading := gradingLatGen L
  isInternal := gradingLatGen_isInternal_of_posDef L hEven hPos
  finrank := gradingLatGen_finrank_of_posDef L hEven hPos
  Y := YfullGen L hEven hPos
  vacuum := latVacuumGen L
  vacuum_mem := by
    rw [gradingLatGen_zero_eq_span_vacuum L hEven hPos]
    exact Submodule.mem_span_singleton_self (latVacuumGen L)
  grading_mode := fun u hu v hv j => YfullGen_grading_mode L hEven hPos u hu v hv j
  vacuum_Y := YfullGen_vacuum L hEven hPos
  creation := YfullGen_creation L hEven hPos
  locality := YfullGen_local L hEven hPos
  regularity := YfullGen_regularity L hEven hPos
  conformalVector := omegaLatGen L
  conformal_mem := omegaLatGen_mem L
  centralCharge := (rank L : ℂ)
  virasoro := YfullGen_virasoro L hEven hPos
  L0_grading := fun v hv => YfullGen_L0_grading L hEven hPos v hv
  translation := YfullGen_translation_omega L hEven hPos
  vacuum_grade := gradingLatGen_zero_eq_span_vacuum L hEven hPos
  positivity := fun n hn => gradingLatGen_positivity L hEven hPos n hn

/-- The lattice VOA has central charge exactly `rank L` (recovering `c = 1` for the rank-`1` case). -/
theorem latticeVOAGen_centralCharge (hEven : L.Even) (hPos : L.PosDef) :
    (latticeVOAGen L hEven hPos).centralCharge = (rank L : ℂ) := rfl

end VOA.LatGen
