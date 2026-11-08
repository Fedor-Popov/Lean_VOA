import VOA.Moonshine.MoonshineCNGradedFields

/-!
# The conformal vertex algebra of the hyperbolic plane

The construction inhabits the existing realization target on its prescribed
Fock tensor twisted-group-algebra carrier. It uses `NearVOA`, since the natural
weight grading is unbounded below and has infinite-dimensional pieces.
-/

namespace VOA.Moonshine.ConwayNorton

open IntegralLattice LatGen HeisenbergN

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

/-- Reconstruction agrees with the exponential field on every ground state. -/
theorem frameStateField_charge (hEven : L.Even) (α : L.carrier) :
    frameStateField F hEven (latChargeGen L α) = canonicalChargedField F α := by
  simpa only [frameWordState_nil, frameWordField_nil] using frameStateField_word F hEven [] α

theorem chargeState_mem_latticeWeight (L : IntegralLattice) (α : L.carrier) :
    latChargeGen L α ∈ gradingLatGen L (halfNorm L α) := by
  have h := bigradα_le_gradingLatGen L 0 α
    (show latChargeGen L α ∈ bigradα L (0, α) from
      ⟨vacuumN _, by simpa only [HeisenbergN.gradingZN_of_nonneg (le_refl 0)] using
        vacuumN_mem_gradingWN (rank L), rfl⟩)
  simpa only [zero_add] using h

/-- An even nondegenerate integral lattice with a complex bilinear frame has
an unbounded conformal vertex algebra on the genuine Fock/group carrier. -/
noncomputable def complexFrameLatticeRealization (hEven : L.Even)
    (hNondegenerate : L.form.Nondegenerate) : EvenLatticeVertexRealization L where
  grading := gradingLatGen L
  isInternal := latticeWeightGrading_isInternal L
  Y := frameStateField F hEven
  vacuum := latVacuumGen L
  vacuum_mem := by
    simpa only [halfNorm_zero, latChargeGen_zero] using chargeState_mem_latticeWeight L 0
  grading_mode := fun k l u v hu hv n => frameStateField_grading_mode F hEven u hu v hv n
  vacuum_Y := frameStateField_vacuum F hEven
  creation := frameStateField_creation F hEven
  locality := frameStateField_local F hEven
  regularity := frameStateField_regularity F hEven
  conformalVector := latticeConformalVector L
  conformal_mem := latticeConformalVector_mem L
  centralCharge := (rank L : ℂ)
  virasoro := frameStateField_virasoro F hEven
  L0_grading := fun n v hv => frameStateField_L0_grading F hEven v hv
  translation := frameStateField_translation_omega F hEven
  even := hEven
  form_nondegenerate := hNondegenerate
  vacuum_eq := rfl
  centralCharge_eq := rfl
  charge_mem := chargeState_mem_latticeWeight L
  charge_leading := by
    intro α β
    rw [frameStateField_charge]
    exact chargedField_charge_leading F (latticeCocycle L) α β
  charge_positive_modes := by
    intro α β n hn
    rw [frameStateField_charge]
    exact chargedField_charge_higher_modes F (latticeCocycle L) α β n hn

/-- The required Lorentzian lattice realization, with no unproved input data. -/
noncomputable def lorentzianVertexRealization : EvenLatticeVertexRealization lorentzianLattice :=
  complexFrameLatticeRealization lorentzianComplexFrame lorentzian_even lorentzian_form_nondegenerate

theorem lorentzianVertexTarget_inhabited : LorentzianVertexTarget :=
  ⟨lorentzianVertexRealization⟩

/-- The same constructed object in the repository's existing structure. -/
noncomputable def lorentzianNearVOA : NearVOA LorentzianFockSpace :=
  lorentzianVertexRealization.toUnboundedConformalVertexAlgebra.toNearVOA

theorem lorentzianNearVOA_centralCharge : lorentzianNearVOA.centralCharge = 2 := by
  change (rank lorentzianLattice : ℂ) = 2
  rw [lorentzian_rank]
  norm_num

theorem lorentzianNearVOA_charge_field (α : lorentzianLattice.carrier) :
    lorentzianNearVOA.Y (lorentzianChargeState α) = lorentzianTargetChargedField α :=
  frameStateField_charge lorentzianComplexFrame lorentzian_even α

theorem lorentzianNearVOA_energy (n : ℤ) (v : LorentzianFockSpace)
    (hv : v ∈ lorentzianWeightGrading n) :
    mode (lorentzianNearVOA.Y lorentzianNearVOA.conformalVector) 1 v = (n : ℂ) • v :=
  lorentzianNearVOA.L0_grading v hv

end VOA.Moonshine.ConwayNorton
