/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3Structure

/-!
# Finite A2 structure tables

These tables are checked against the actual trace-zero matrix commutator
and trace form by kernel-checked finite arithmetic. They separate finite
matrix simplification from the much larger free-field operators.
-/
namespace VOA.AffineSl3
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

/-- The Chevalley structure constants, in the established eight-element order. -/
def bracketTable : Fin 8 → Fin 8 → Fin 8 → ℂ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![-2, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, -2, 0, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0]],
    ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0]],
    ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, -2, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
    ![![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, -2, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]]

/-- The trace form in the same basis, with the non-diagonal Cartan block. -/
def formTable : Fin 8 → Fin 8 → ℂ :=
  ![![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, -1],
    ![0, 0, 0, 0, 0, 0, -1, 2]]

/-- Every tabulated bracket coefficient equals the coefficient of the
actual matrix commutator. -/
theorem structureConstant_eq_table (a b c : Fin 8) :
    structureConstant a b c=bracketTable a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [bracketTable,structureConstant,coordinates,generator,Ring.lie_def,
      e1,e2,e12,f1,f2,f12,h1,h2,Matrix.mul_apply,Fin.sum_univ_three,Matrix.single,Fin.ext_iff]

/-- Every tabulated pairing equals the actual trace of the product. -/
theorem form_generator_eq_table (a b : Fin 8) : form (generator a) (generator b)=formTable a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [formTable,generator,form_apply,e1,e2,e12,f1,f2,f12,h1,h2,
      Matrix.trace,Matrix.mul_apply,Fin.sum_univ_three,Matrix.single,Fin.ext_iff]

end
end VOA.AffineSl3
