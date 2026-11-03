/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.LatticeGenVertex

/-!
# The hyperbolic lattice datum underlying the inverse-DS free field `Pi`

The inverse Hamiltonian-reduction realization uses two bosons with a hyperbolic pairing and
lattice exponentials only along one null direction.  This file constructs that datum inside the
existing general-lattice state-space API:

* `piLattice` is the even rank-two lattice with Gram matrix `((0,1),(1,0))`;
* `eta` and `xi` are its two primitive null vectors, with pairing one;
* `etaCharge q = q eta` is the isotropic charge line used by `Pi`;
* `PiAmbientSpace` is the existing general-lattice state space for `piLattice`;
* `piExponential q` is the charge-line state;
* `piChargeOperatorShadow q` records how far the existing positive-lattice charge-operator
  formula can be specialized before its metric theorem is needed.

The last definitions are genuine uses of the current lattice state/operator API: creation and
charge-line closure are proved below.  The operator is deliberately called a `Shadow`: its
Euclidean-frame dressing has no proved hyperbolic commutator identity.  These definitions do
**not** create a vertex operator algebra.
That is an actual interface boundary, not missing bookkeeping.  The reconstructed general lattice
VOA requires `IntegralLattice.PosDef`, while `piLattice` contains the nonzero isotropic vector
`eta`; `piLattice_not_posDef` proves that the required hypothesis is impossible.  Moreover the
present general-lattice oscillators are made from a Euclidean orthonormal frame, and their
metric-carrying commutator theorem also assumes positive definiteness.  A hyperbolic-Heisenberg
constructor is therefore the next necessary library component.

No positivity, locality, tensor-product VOA, or Adamovic embedding is asserted here.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDSPi

open scoped Matrix TensorProduct
open VOA.IntegralLattice

noncomputable section

/-- The integral hyperbolic plane, with Gram matrix `((0,1),(1,0))`. -/
noncomputable def piLattice : IntegralLattice where
  carrier := Fin 2 → ℤ
  form := Matrix.toBilin' (!![(0 : ℤ), 1; 1, 0])
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    simp only [Matrix.toBilin'_apply']
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring

/-- The first primitive null vector, the lattice direction of the exponentials in `Pi`. -/
def eta : piLattice.carrier := ![(1 : ℤ), 0]

/-- The second primitive null vector, supplying the transverse Heisenberg direction. -/
def xi : piLattice.carrier := ![(0 : ℤ), 1]

/-- Coordinate formula for the hyperbolic pairing. -/
theorem piLattice_form (v w : piLattice.carrier) :
    piLattice.form v w = v 0 * w 1 + v 1 * w 0 := by
  change Matrix.toBilin' (!![(0 : ℤ), 1; 1, 0]) v w = _
  rw [Matrix.toBilin'_apply']
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]

@[simp] theorem form_eta_eta : piLattice.form eta eta = 0 := by
  rw [piLattice_form]
  simp [eta]

@[simp] theorem form_xi_xi : piLattice.form xi xi = 0 := by
  rw [piLattice_form]
  simp [xi]

@[simp] theorem form_eta_xi : piLattice.form eta xi = 1 := by
  rw [piLattice_form]
  simp [eta, xi]

@[simp] theorem form_xi_eta : piLattice.form xi eta = 1 := by
  rw [piLattice_form]
  simp [eta, xi]

theorem eta_ne_zero : eta ≠ 0 := by
  change (![(1 : ℤ), 0] : Fin 2 → ℤ) ≠ 0
  intro h
  have h0 := congrFun h 0
  norm_num at h0

theorem xi_ne_zero : xi ≠ 0 := by
  change (![(0 : ℤ), 1] : Fin 2 → ℤ) ≠ 0
  intro h
  have h1 := congrFun h 1
  norm_num at h1

/-- The hyperbolic plane is even: the norm of `(a,b)` is `2ab`. -/
theorem piLattice_even : piLattice.Even := by
  intro v
  refine ⟨v 0 * v 1, ?_⟩
  rw [piLattice_form]
  ring

/-- The exact obstruction to reusing the positive-definite lattice-VOA constructor. -/
theorem piLattice_not_posDef : ¬piLattice.PosDef := by
  intro h
  have heta := h eta eta_ne_zero
  rw [form_eta_eta] at heta
  omega

/-- The charge `q eta` along the isotropic lattice line. -/
def etaCharge (q : ℤ) : piLattice.carrier := q • eta

@[simp] theorem etaCharge_apply_zero (q : ℤ) : etaCharge q 0 = q := by
  change q • (1 : ℤ) = q
  simp

@[simp] theorem etaCharge_apply_one (q : ℤ) : etaCharge q 1 = 0 := by
  change q • (0 : ℤ) = 0
  simp

@[simp] theorem etaCharge_zero : etaCharge 0 = 0 := by
  exact zero_zsmul eta

@[simp] theorem etaCharge_add (q r : ℤ) : etaCharge (q + r) = etaCharge q + etaCharge r := by
  exact add_zsmul eta q r

/-- The isotropic charge-line parametrization is injective. -/
theorem etaCharge_injective : Function.Injective etaCharge := by
  intro q r h
  have h0 := congrFun h 0
  simpa using h0

/-- Every two charge-line vectors have zero pairing. -/
@[simp] theorem form_etaCharge_etaCharge (q r : ℤ) :
    piLattice.form (etaCharge q) (etaCharge r) = 0 := by
  rw [piLattice_form]
  simp

/-- Pairing with the transverse null vector reads off the lattice charge. -/
@[simp] theorem form_etaCharge_xi (q : ℤ) : piLattice.form (etaCharge q) xi = q := by
  rw [piLattice_form]
  simp [xi]

/-- The existing general-lattice state space for the hyperbolic plane.

This is an ambient vector space with charge operators, not yet a vertex algebra: the current
reconstruction theorem cannot be instantiated because `piLattice_not_posDef`. -/
abbrev PiAmbientSpace := LatGen.LatModuleGen piLattice

/-- The charge-line state customarily denoted `exp(q (delta + phi))`. -/
noncomputable def piExponential (q : ℤ) : PiAmbientSpace :=
  LatGen.latChargeGen piLattice (etaCharge q)

@[simp] theorem piExponential_zero : piExponential 0 = LatGen.latVacuumGen piLattice := by
  rw [piExponential, etaCharge_zero]
  exact LatGen.latChargeGen_zero piLattice

/-- The specialization of the existing charge operator to `q eta`.

Only its creation and charge-shift formulas are valid here.  The positive-lattice theorem that
identifies its oscillator commutator with the lattice pairing cannot be applied, so this is not
yet the hyperbolic `Pi` exponential field. -/
noncomputable def piChargeOperatorShadow (q : ℤ) :
    FormalDist (Module.End ℂ PiAmbientSpace) :=
  LatGen.Yeαvec piLattice (etaCharge q)

/-- The charge-operator shadow creates the corresponding charge-line state from the vacuum. -/
theorem piChargeOperatorShadow_mode_neg_one_vacuum (q : ℤ) :
    mode (piChargeOperatorShadow q) (-1) (LatGen.latVacuumGen piLattice) = piExponential q := by
  exact LatGen.Yeαvec_mode_neg_one_vacuum piLattice (etaCharge q)

/-- Acting on a pure charge-line state stays on the charge line.  The coefficient is the generic
boson dressing and the FLM cocycle; isotropy removes the momentum shift in its index. -/
theorem piChargeOperatorShadow_on_chargeLine (q r t : ℤ)
    (p : HeisenbergN.FockN (IntegralLattice.rank piLattice)) :
    piChargeOperatorShadow q t (LatGen.latStateGen piLattice p (etaCharge r))
      = latticeCocycle piLattice (etaCharge q) (etaCharge r) •
          LatGen.latStateGen piLattice
            (LatGen.EEVec piLattice (etaCharge q) t p) (etaCharge (q + r)) := by
  rw [piChargeOperatorShadow, LatGen.Yeαvec_tmul, form_etaCharge_etaCharge, sub_zero,
    etaCharge_add]

end
end InverseDSPi
end VOA
