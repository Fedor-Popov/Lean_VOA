import VOA.DeligneAudit.D4CharRound108Audit
import VOA.DeligneAudit.D4CharDemazureRealization
import VOA.DeligneAudit.LeviTypeA2CertGradedFinal
import VOA.DeligneAudit.LeviTypeA3GradedInductionFinal

/-!
# The graded Levi bound and hD: declaration and axiom audit

Axiom check: every theorem and linear equivalence of this layer depends exactly on
`[propext, Classical.choice, Quot.sound]`, with no proof escapes. This module imports
`D4CharRound108Audit` and both type-A chains.

Proved in namespace VOA.DeligneAudit.D4Char:
* RealizationSqueeze proves the exact-degree tensor-model total and the finite-total
  squeeze. Its conditional realization theorem is discharged below, using L4 and L3.
* BoxGaussian and BoxConvolution identify the original exact-degree mode boxes with
  Gaussian coefficients and convolution. GradedKeyCount proves their D4 degreewise
  sum is bounded by d4LeviHilb. No box data or degree interval was discarded.
* Sl2Graded and Sl2GradedAction prove the sharp graded GL2 estimate and all four
  node-two Levi actions. A2KeyGraded and A2GradedOrbit apply it inside the actual
  higher-key quotient, including the extra Cartan action.
* ProjectedStep, CurrentGrading, and QuotientGrading preserve exact degree under
  key filtrations and homogeneous quotients. The tagged current-module lift supplies
  genuine degree projections for arbitrary ambient modules without a grading hypothesis.
* TypeABoxCount identifies the original two-box and three-box degree multiplicities
  with the branching formulas of gl3Hilb and gl4Hilb. A2ProjectedSteps, A2GradedCount,
  and A2GradedBound give a2_all_weight_graded_bound for all p,q,N. A3GradedOrbit,
  A3ProjectedSteps, A3GradedCount, and A3GradedBound give a3_all_weight_graded_bound
  for all a,b,c,N. Both bounds hold with no hypotheses and use the original key quotients.
* GradedAssembly eliminates unsupported keys and keys above the requested degree.
  KeyOrbitGraded projects the D4 quotient basis-orbit decomposition. Its
  universal_key_orbit_graded_bound supplies the sharp GL4 rank of every supported key.
* DemazureRealization discharges SupportedGradedKeyBound and then GradedLeviBound.
  d4_finrank_cycDeg_le is L1 for every Sat module, every n, and every N.
  d4_demazureRealization is the all-n hD with no remaining hypotheses.

L1 and hD are proved, using L4 and L3. The model attains d4LeviHilb in every degree by
the squeeze.

**Not proved here:** the fusion total bound hF; no unconditional classically-free capstone
is claimed. The modules of this layer are imported through this audit or
`D4CharDemazureRealization`.
-/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4 DeligneCharacter

example : GradedLeviBound := d4_gradedLeviBound

example : ∀ n,
    DemazureRealizationG D4sector (ravFam D4sector) D4Wp.hilbSeriesZ n :=
  d4_demazureRealization

example (n N : ℕ) :
    Module.finrank ℂ (cycDeg (D1TensorG.Gr.D4Check.modelRep n)
      (D1TensorG.Gr.D4Check.modelGenerator n) N) = d4LeviHilb n N :=
  d4_model_degree_eq_levi d4_gradedLeviBound n N

example (n N : ℕ) : D4K.hilbInt n N = (d4LeviHilb n N : ℤ) :=
  d4_hilbInt_eq_levi n N

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.sl2_local_weyl_graded_bound
#print axioms VOA.DeligneAudit.D4Char.a2_all_weight_graded_bound
#print axioms VOA.DeligneAudit.D4Char.a3_all_weight_graded_bound
#print axioms VOA.DeligneAudit.D4Char.universal_key_orbit_graded_bound
#print axioms VOA.DeligneAudit.D4Char.d4_supported_graded_keys
#print axioms VOA.DeligneAudit.D4Char.d4_finrank_cycDeg_le
#print axioms VOA.DeligneAudit.D4Char.d4_gradedLeviBound
#print axioms VOA.DeligneAudit.D4Char.d4_demazureRealization
