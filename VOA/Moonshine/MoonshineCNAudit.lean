import VOA.Moonshine.MoonshineCNTrace
import VOA.Moonshine.MoonshineCNLattice
import VOA.Moonshine.MoonshineCNOscillators
import VOA.Moonshine.MoonshineCNVertexTarget

/-! Axiom audit for all declarations introduced by the Conway–Norton foundation modules. -/

namespace VOA.Moonshine.ConwayNorton

#print axioms gradedAutAction
#print axioms gradedAutTrace
#print axioms gradedAutTrace_one
#print axioms gradedAutTrace_conjugate
#print axioms vnatAut_preserves_grading
#print axioms mckayThompson
#print axioms mckayThompson_coeff
#print axioms mckayThompson_coeff_zero
#print axioms mckayThompson_conjugate
#print axioms mckayThompson_one
#print axioms mckayThompsonShift
#print axioms mckayThompsonShift_one
#print axioms mckayThompson_one_ne_JShift

#print axioms hyperbolicGram
#print axioms lorentzianLattice
#print axioms lorentzian_form_apply
#print axioms lorentzian_even
#print axioms lorentzian_rank
#print axioms lorentzian_gram_det
#print axioms lorentzian_form_nondegenerate
#print axioms lorentzian_not_posDef
#print axioms lorentzianRealBasis
#print axioms lorentzianRealBasis_apply
#print axioms lorentzian_real_form_basis
#print axioms lorentzian_real_pairing_coordinate
#print axioms lorentzian_selfDual
#print axioms lorentzianEnergy
#print axioms lorentzianEnergy_half_norm
#print axioms lorentzianEnergy_add
#print axioms lorentzianEnergy_unbounded_below
#print axioms lorentzianCocycle
#print axioms lorentzianCocycle_law
#print axioms lorentzianCocycle_commutator
#print axioms lorentzianCocycle_normalized
#print axioms lorentzianTwistedProduct_assoc

#print axioms complexChargeOscillator
#print axioms complexChargeOscillator_vacuum
#print axioms complexChargeOscillator_commutator
#print axioms complexHyperbolicCoordinate
#print axioms complexHyperbolicCoordinate_pairing
#print axioms lorentzianOscillator
#print axioms lorentzianOscillator_commutator
#print axioms lorentzianOscillator_vacuum

#print axioms UnboundedConformalVertexAlgebra
#print axioms EvenLatticeVertexRealization
#print axioms LorentzianFockSpace
#print axioms lorentzianVacuum
#print axioms lorentzianChargeState
#print axioms lorentzianChargeCoefficient
#print axioms lorentzianChargeCoefficient_charge
#print axioms lorentzianChargeState_ne_zero
#print axioms LorentzianVertexTarget
#print axioms lorentzian_grading_not_bounded_below

end VOA.Moonshine.ConwayNorton
