import VOA.Moonshine.MoonshineCNOscillators
import VOA.Examples.LatticeGenModule

/-!
# The target for an indefinite even-lattice vertex algebra

The existing `PreVertexAlgebra` requires finite-dimensional weight spaces and
`GradedVertexOperatorAlgebra` also requires a uniform lower weight bound.
Neither is appropriate for the hyperbolic lattice. This file specifies the
unbounded conformal structure, fixes its intended Fock/group-algebra carrier,
and proves the obstruction to a lower bound. It does not construct the fields.
-/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct
open Module (End)

universe u

/-- A conformal vertex algebra with an internal integer grading, without
finiteness or a uniform lower bound on its weight spaces. -/
structure UnboundedConformalVertexAlgebra (M : Type u) [AddCommGroup M] [Module ℂ M] where
  grading : ℤ → Submodule ℂ M
  isInternal : DirectSum.IsInternal grading
  Y : M →ₗ[ℂ] FormalDist (End ℂ M)
  vacuum : M
  vacuum_mem : vacuum ∈ grading 0
  grading_mode : ∀ (k l : ℤ) (u v : M), u ∈ grading k → v ∈ grading l →
    ∀ n : ℤ, mode (Y u) n v ∈ grading (k + l - n - 1)
  vacuum_Y : Y vacuum = 1
  creation : ∀ u : M, mode (Y u) (-1) vacuum = u ∧
    ∀ n : ℤ, 0 ≤ n → mode (Y u) n vacuum = 0
  locality : ∀ u v : M, Local (Y u) (Y v)
  regularity : ∀ u v : M, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Y u) n v = 0
  conformalVector : M
  conformal_mem : conformalVector ∈ grading 2
  centralCharge : ℂ
  virasoro : ∀ m n : ℤ,
    ⁅mode (Y conformalVector) (m + 1), mode (Y conformalVector) (n + 1)⁆ =
      ((m : ℂ) - n) • mode (Y conformalVector) (m + n + 1) +
        (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * centralCharge) • (1 : End ℂ M)
        else 0)
  L0_grading : ∀ (n : ℤ) (v : M), v ∈ grading n →
    mode (Y conformalVector) 1 v = (n : ℂ) • v
  translation : ∀ v : M, Y (mode (Y conformalVector) 0 v) = deriv (Y v)

/-- Target data for an even lattice, including the correct charge-state weights.
An inhabitant, not merely this structure declaration, is still required. -/
structure EvenLatticeVertexRealization (L : IntegralLattice) extends
    UnboundedConformalVertexAlgebra (LatGen.LatModuleGen L) where
  even : L.Even
  form_nondegenerate : L.form.Nondegenerate
  vacuum_eq : vacuum = LatGen.latVacuumGen L
  centralCharge_eq : centralCharge = (IntegralLattice.rank L : ℂ)
  charge_mem : ∀ x : L.carrier,
    LatGen.latChargeGen L x ∈ grading (L.form x x / 2)
  charge_leading : ∀ x y : L.carrier,
    mode (Y (LatGen.latChargeGen L x)) (-L.form x y - 1) (LatGen.latChargeGen L y) =
      IntegralLattice.latticeCocycle L x y • LatGen.latChargeGen L (x + y)
  charge_positive_modes : ∀ (x y : L.carrier) (n : ℤ), -L.form x y - 1 < n →
    mode (Y (LatGen.latChargeGen L x)) n (LatGen.latChargeGen L y) = 0

/-- The intended hyperbolic lattice state space, reusing the existing carrier. -/
noncomputable abbrev LorentzianFockSpace := LatGen.LatModuleGen lorentzianLattice

noncomputable def lorentzianVacuum : LorentzianFockSpace :=
  LatGen.latVacuumGen lorentzianLattice

noncomputable def lorentzianChargeState (x : lorentzianLattice.carrier) :
    LorentzianFockSpace := LatGen.latChargeGen lorentzianLattice x

/-- Extract the vacuum-oscillator coefficient at lattice charge `x`. -/
noncomputable def lorentzianChargeCoefficient (x : lorentzianLattice.carrier) :
    LorentzianFockSpace →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (MvPolynomial.aeval (fun _ :
      ℕ × Fin (IntegralLattice.rank lorentzianLattice) => (0 : ℂ))).toLinearMap
      (Finsupp.lapply x))

theorem lorentzianChargeCoefficient_charge (x : lorentzianLattice.carrier) :
    lorentzianChargeCoefficient x (lorentzianChargeState x) = 1 := by
  classical
  simp [lorentzianChargeCoefficient, lorentzianChargeState, LatGen.latChargeGen,
    LatGen.latStateGen, LatGen.eGen, HeisenbergN.vacuumN]

theorem lorentzianChargeState_ne_zero (x : lorentzianLattice.carrier) :
    lorentzianChargeState x ≠ 0 := by
  intro h
  have hc := lorentzianChargeCoefficient_charge x
  rw [h, map_zero] at hc
  exact zero_ne_one hc

/-- The exact remaining existence statement for the first lattice part of the no-ghost
construction of the Monster Lie algebra (the vertex algebra of the hyperbolic lattice). -/
def LorentzianVertexTarget : Prop := Nonempty (EvenLatticeVertexRealization lorentzianLattice)

/-- Any grading assigning the genuine ground-state energies is unbounded below.
This obstruction needs neither vertex fields nor a conjectural realization. -/
theorem lorentzian_grading_not_bounded_below
    (grading : ℤ → Submodule ℂ LorentzianFockSpace)
    (charge_mem : ∀ x : lorentzianLattice.carrier,
      lorentzianChargeState x ∈ grading (lorentzianEnergy x)) :
    ¬ ∃ N : ℤ, ∀ n : ℤ, n < N → grading n = ⊥ := by
  rintro ⟨N, hN⟩
  obtain ⟨x, hx⟩ := lorentzianEnergy_unbounded_below N
  have hmem := charge_mem x
  rw [hN _ hx, Submodule.mem_bot] at hmem
  exact lorentzianChargeState_ne_zero x hmem

end VOA.Moonshine.ConwayNorton
