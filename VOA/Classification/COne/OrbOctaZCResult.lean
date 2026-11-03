import VOA.Classification.COne.OrbOctaZCWitness
import VOA.Classification.COne.OrbOctaZVacuum

/-! Consequences of the certified intrinsic octahedral conformal polynomial.
The conformal identity is unconditional. The four positive-polynomial seed
identities, equivalently the vacuum fiber, remain the input to vacuum uniqueness.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA OrbOctaZ OrbZhu Polynomial OrbB5

/-- P25 annihilates left multiplication by the conformal class on the whole Zhu algebra. -/
theorem conformal_annihilator : aeval (omegaL W) candidatePolynomial = 0 :=
  candidate_annihilates OctahedralConformalZhuRelation_holds

/-- Every realized lowest weight is zero or one of the 24 positive rational roots. -/
theorem octa_lowestWeight_table
    {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ}
    (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    h = 0 ∨ ∃ i, h = (positiveWeightQ i : ℂ) :=
  lowestWeight_table OctahedralConformalZhuRelation_holds N hl hne

/-- The conformal-weight gap, unconditionally. -/
theorem octa_lowestWeight_zero_or_gap
    {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) {h : ℂ}
    (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    h = 0 ∨ (1 : ℝ) / 64 ≤ h.re :=
  lowestWeight_zero_or_gap OctahedralConformalZhuRelation_holds N hl hne

/-- Exact residual: the four Q24 seed identities are equivalent to the vacuum fiber. -/
theorem vacuumFiber_iff_Q24 :
    OctahedralVacuumFiber ↔ ∀ i : Fin 4,
      aeval (omegaL W) positivePolynomial (mk W (OrbOcta.octaSeeds i.succ)) = 0 :=
  vacuumFiber_iff_positive_annihilators OctahedralConformalZhuRelation_holds

/-- No rationality assumption is needed once the four seed identities are supplied. -/
theorem octa_pseudoUnitary_of_vacuumFiber (hF : OctahedralVacuumFiber) :
    PseudoUnitary (orbifoldVOA OrbC2b.octa) :=
  octa_pseudoUnitary_of_zhu_fiber OctahedralConformalZhuRelation_holds hF

/-- The sharper dimension bound retains precisely the same four-seed residual. -/
theorem finrank_le_121_of_vacuumFiber (hF : OctahedralVacuumFiber) :
    Module.finrank ℂ (A W) ≤ 121 :=
  finrank_le_121_of_zhu_fiber OctahedralConformalZhuRelation_holds hF

end VOA.Classification.COne.OrbOctaZC
