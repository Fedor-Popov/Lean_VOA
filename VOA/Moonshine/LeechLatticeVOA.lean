/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenInstance
import VOA.LatticesAndCodes.Leech.Defs

/-!
# The Leech lattice VOA `V_Λ`  (Moonshine step M1)

The Leech lattice comes from the vendored files `VOA/LatticesAndCodes` (a formalization of
Ebeling, *Lattices and Codes*), where it is built from the extended binary Golay code and proved
even, unimodular, positive definite, rank `24` and rootless (`Leech.lattice_isEven`,
`Leech.lattice_isPosDef`, `Leech.lattice_isUnimodular`, `Leech.lattice_rank`,
`Leech.lattice_no_roots`).

The two libraries model an integral lattice the same way (a finite free `ℤ`-module with a
symmetric `ℤ`-valued bilinear form, definiteness as a predicate), so the bridge `ofEbeling` is a
field-for-field repackaging and all predicates transfer definitionally.

## Main declarations
* `VOA.IntegralLattice.ofEbeling` — transport a (vendored) `LatticesAndCodes` lattice.
* `VOA.Moonshine.leech` — the Leech lattice as a `VOA.IntegralLattice`.
* `VOA.Moonshine.leechVOA` — the lattice VOA `V_Λ`, via `LatGen.latticeVOAGen`.
* `VOA.Moonshine.leechVOA_centralCharge` — `c(V_Λ) = 24`.
-/

namespace VOA

namespace IntegralLattice

/-- Transport an integral lattice of the vendored `LatticesAndCodes` files
(Ebeling's convention S1) to a `VOA.IntegralLattice`. -/
noncomputable def ofEbeling (Γ : _root_.IntegralLattice) : VOA.IntegralLattice.{0} where
  carrier := Γ.carrier
  form := Γ.bilin
  isSymm := ⟨fun x y => Γ.bilin_symm x y⟩

variable (Γ : _root_.IntegralLattice)

@[simp] theorem ofEbeling_form (x y : Γ.carrier) : (ofEbeling Γ).form x y = Γ.bilin x y := rfl

theorem ofEbeling_even (h : Γ.IsEven) : (ofEbeling Γ).Even := fun v => h v

theorem ofEbeling_posDef (h : Γ.IsPosDef) : (ofEbeling Γ).PosDef := fun v hv => h v hv

theorem ofEbeling_rank : rank (ofEbeling Γ) = Γ.rank := rfl

end IntegralLattice

namespace LatGen

variable (L : IntegralLattice)

/-- For an even positive-definite lattice **without roots**, the weight-`1` space of `V_L` is the
Heisenberg weight-`1` space at charge `0`: no `e^α` contributes, since `½⟨α,α⟩ ≥ 2` for `α ≠ 0`. -/
theorem gradingLatGen_one_of_rootless (hEven : L.Even) (hPos : L.PosDef)
    (hR : ∀ v : L.carrier, L.form v v ≠ 2) :
    gradingLatGen L 1 = bigradα L (1, 0) := by
  apply le_antisymm
  · refine iSup_le (fun α => ?_)
    rcases eq_or_ne α 0 with hα | hα
    · subst hα; rw [halfNorm_zero L, sub_zero]
    · have hpos := halfNorm_pos L hEven hPos hα
      have h2 := two_halfNorm L hEven α
      have hne := hR α
      rw [bigradα_eq_bot_of_neg L α (by omega : 1 - halfNorm L α < 0)]
      exact bot_le
  · have : bigradα L (1, 0) = bigradα L ((1 : ℤ) - halfNorm L 0, 0) := by rw [halfNorm_zero L]; simp
    rw [this]
    exact le_iSup (fun α => bigradα L ((1 : ℤ) - halfNorm L α, α)) 0

end LatGen

namespace Moonshine

open IntegralLattice

/-- The **Leech lattice** `Λ`, as a `VOA.IntegralLattice`. -/
noncomputable abbrev leech : VOA.IntegralLattice.{0} := ofEbeling Leech.lattice

theorem leech_even : leech.Even := ofEbeling_even _ Leech.lattice_isEven

theorem leech_posDef : leech.PosDef := ofEbeling_posDef _ Leech.lattice_isPosDef

theorem leech_rank : rank leech = 24 := Leech.lattice_rank

/-- `Λ` has no roots: no vector of norm `2`. -/
theorem leech_no_roots (v : leech.carrier) : leech.form v v ≠ 2 := Leech.lattice_no_roots v

/-- **The Leech lattice VOA** `V_Λ`. -/
noncomputable def leechVOA : VertexOperatorAlgebra (LatGen.LatModuleGen leech) :=
  LatGen.latticeVOAGen leech leech_even leech_posDef

/-- `V_Λ` has central charge `24`. -/
theorem leechVOA_centralCharge : leechVOA.centralCharge = 24 := by
  rw [leechVOA, LatGen.latticeVOAGen_centralCharge, leech_rank]; norm_num

/-- The weight-`1` space of `V_Λ` is spanned by the Heisenberg states `h(-1)𝟙` alone: the Leech
lattice has no roots, so no `e^α` has weight `1`. -/
theorem leechVOA_grading_one :
    leechVOA.grading 1 = LatGen.bigradα leech (1, 0) :=
  LatGen.gradingLatGen_one_of_rootless leech leech_even leech_posDef leech_no_roots

end Moonshine

end VOA
