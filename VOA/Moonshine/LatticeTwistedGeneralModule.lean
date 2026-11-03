/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGeneralGrading
import VOA.Moonshine.LatticeTwistedModule

/-! # Charge-parametric module for even lattices
Adapted from `LatticeTwistedModule` using only `TwistedCharge` relations.
The existing generic oscillator and lattice-state results are reused. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

variable (L : IntegralLattice.{0}) (hEven : L.Even) (C : TwistedCharge L) (hPos : L.PosDef)
variable [FiniteDimensional ℂ C.carrier]

/-- The ordinary twisted module requires a finite-dimensional charge space because
`TwistedModule.finrank` requires finite-dimensional weight spaces. The fields,
product formula, and Jacobi identity above require no such assumption. -/
noncomputable def latticeTwistedModule :
    TwistedModule (thetaAut L hEven hPos) 2
      (FockT (rank L) ⊗[ℂ] Space L hEven C) where
  YM := YML L hEven C
  vacuum_YM k := by
    change YML L hEven C (latVacuumGen L) k = _
    rw [YML_vacuum]
    push_cast
    rfl
  truncation := YML_truncation L hEven C
  support := fun j u hu k hk => YML_support L hEven C hPos j u hu k hk
  jacobi := twistedJacobi_YML L hEven C hPos
  weight := weightLT (rank L) (Space L hEven C)
  isInternal := weightLT_isInternal _ _
  L0_weight := fun α x hx => by
    change YML L hEven C (omegaLatGen L) ((2 : ℕ) : ℤ) x = α • x
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, YML_omega_two L hEven C hPos]
    exact L0T_rTensor_weightLT _ _ hx
  finrank := weightLT_finiteDimensional _ _
  boundedBelow := weightLT_boundedBelow _ _

@[simp] theorem latticeTwistedModule_YM :
    (latticeTwistedModule L hEven C hPos).YM = YML L hEven C := rfl

end VOA.Moonshine.LatticeTwistedGeneral
