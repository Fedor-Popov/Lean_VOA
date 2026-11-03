/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergVOA
import VOA.Modules.ZhuVermaAnArchDLM3AdjointBottom

/-!
# A nontrivial Heisenberg instance of the DLM3 PBW boundary

The generic adjoint construction specializes to the rank-one Heisenberg VOA.  This file names the
resulting `PBWFreeness` and `BottomProjection` terms and exhibits the polynomial vacuum `1` as a
nonzero vector of their bottom Zhu module.  Thus the instance is not merely a construction on a
possibly-zero carrier.  Its `A(W)`-module is the adjoint weight-zero bottom; it is not an instance
for the downstream `regularAMod W` projection.
-/

namespace VOA

open VertexOperatorAlgebra

namespace VHat
namespace DLM3

/-- The rank-one Heisenberg adjoint bottom satisfies the full `PBWFreeness` package. -/
def heisenbergAdjointPBWFreeness (k : ℂ) (hk : k ≠ 0) :
    PBWFreeness
      (parabolicRepOfAMod (heisenbergVOA k hk) (adjointBottomAMod (heisenbergVOA k hk))) :=
  adjointPBWFreeness (heisenbergVOA k hk)

/-- The corresponding Heisenberg bottom projection. -/
noncomputable def heisenbergAdjointBottomProjection (k : ℂ) (hk : k ≠ 0) :
    BottomProjection
      (parabolicRepOfAMod (heisenbergVOA k hk) (adjointBottomAMod (heisenbergVOA k hk))) :=
  adjointBottomProjection (heisenbergVOA k hk)

/-- The polynomial vacuum as a vector in the adjoint weight-zero bottom. -/
noncomputable def heisenbergAdjointBottomVacuum (k : ℂ) (hk : k ≠ 0) :
    (adjointBottomAMod (heisenbergVOA k hk)).carrier := by
  refine ⟨vacuum, ?_⟩
  change (heisenbergVOA k hk).vacuum ∈ adjWeight (heisenbergVOA k hk) 0
  rw [show (0 : ℂ) = ((0 : ℤ) : ℂ) by norm_num, adjWeight_cast]
  exact (heisenbergVOA k hk).vacuum_mem

/-- The displayed Heisenberg bottom vector is genuinely nonzero. -/
theorem heisenbergAdjointBottomVacuum_ne_zero (k : ℂ) (hk : k ≠ 0) :
    heisenbergAdjointBottomVacuum k hk ≠ 0 := by
  intro h
  have h' := congrArg (adjointBottomInclusion (heisenbergVOA k hk)) h
  rw [map_zero] at h'
  change (vacuum : Fock) = 0 at h'
  exact one_ne_zero (by simpa only [vacuum] using h')

/-- Consequently the canonical bottom image in the Heisenberg induced module is nonzero. -/
theorem heisenberg_indBottom_vacuum_ne_zero (k : ℂ) (hk : k ≠ 0) :
    indBottom
        (parabolicRepOfAMod (heisenbergVOA k hk) (adjointBottomAMod (heisenbergVOA k hk)))
        (heisenbergAdjointBottomVacuum k hk) ≠ 0 := by
  intro h
  apply heisenbergAdjointBottomVacuum_ne_zero k hk
  apply (adjoint_indBottom_injective (heisenbergVOA k hk))
  simpa using h

end DLM3
end VHat
end VOA
