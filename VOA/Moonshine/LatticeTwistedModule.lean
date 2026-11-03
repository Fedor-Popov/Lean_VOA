/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGrading

/-!
# The `θ`-twisted module `V_L^T` of a lattice VOA  (Moonshine step M6)

`latticeTwistedModule L hEven hU hPos : TwistedModule (thetaAut L hEven hPos) 2
  (FockT (rank L) ⊗ T_L)` — for every even positive-definite lattice `L` with unimodular Gram
matrix, `V_L^T = S[θ] ⊗ T_L` is a `θ`-twisted module of order `2` for the lattice VOA
`latticeVOAGen L hEven hPos`, in the sense of `Modularity/Twisted.lean` (the structure is used
unchanged).  The data:

* `YM := YML` — the twisted vertex operator `u ↦ (k ↦ u₍k/2₎)` (`LatticeTwistedFields`);
* `vacuum_YM`, `truncation`, `support` — `YML_vacuum`, `YML_truncation`, `YML_support`;
* `jacobi` — `twistedJacobi_YML` (`LatticeTwistedJacobi`), from the twisted product formula
  `PF_all` (`LatticeTwistedBaseCase`) for **all** pairs of states;
* `weight := weightLT` — `S[θ]_d ⊗ T`, with `L0_weight` from `YML_omega_two`
  (`Y^T(ω)₍₁₎ = L0T ⊗ 1`), finite-dimensional, bounded below by `rank L / 16`.

`leechTwistedModule : TwistedModule leechTheta 2 (FockT 24 ⊗ T_Λ)` — the Leech case
(`T_Λ` of dimension `2^{12}`), transported along `rank leech = 24`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
Unconditional: the only hypotheses are `L.Even`, `L.PosDef` and unimodularity of the Gram
matrix, all discharged for `Λ` (`leech_even`, `leech_posDef`, `leech_isUnit_det_gramMat`).
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

/-- **The `θ`-twisted module of the lattice VOA** `V_L^T = S[θ] ⊗ T_L`. -/
noncomputable def latticeTwistedModule :
    TwistedModule (thetaAut L hEven hPos) 2
      (FockT (rank L) ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) where
  YM := YML L hEven hU
  vacuum_YM k := by
    change YML L hEven hU (latVacuumGen L) k = _
    rw [YML_vacuum]
    push_cast
    rfl
  truncation := YML_truncation L hEven hU
  support := fun j u hu k hk => YML_support L hEven hU hPos j u hu k hk
  jacobi := twistedJacobi_YML L hEven hU hPos
  weight := weightLT (rank L) (Rep (cocMat L) (isUnit_det_cocMat L hEven hU))
  isInternal := weightLT_isInternal _ _
  L0_weight := fun α x hx => by
    change YML L hEven hU (omegaLatGen L) ((2 : ℕ) : ℤ) x = α • x
    rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, YML_omega_two L hEven hU hPos]
    exact L0T_rTensor_weightLT _ _ hx
  finrank := weightLT_finiteDimensional _ _
  boundedBelow := weightLT_boundedBelow _ _

@[simp] theorem latticeTwistedModule_YM :
    (latticeTwistedModule L hEven hU hPos).YM = YML L hEven hU := rfl

/-- **The `θ`-twisted Leech module** `V_Λ^T = S[θ] ⊗ T_Λ` (with `rank Λ = 24`). -/
noncomputable def leechTwistedModule :
    TwistedModule leechTheta 2
      (FockT 24 ⊗[ℂ] Rep (cocMat leech) (isUnit_det_cocMat leech leech_even
        leech_isUnit_det_gramMat)) :=
  leech_rank ▸ latticeTwistedModule leech leech_even leech_isUnit_det_gramMat leech_posDef

end VOA.Moonshine.LatticeTwisted
