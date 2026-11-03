/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2RelationsPresentation
import VOA.DeligneAudit.A2Carrier
import VOA.DeligneAudit.A2CharacterInterface

/-!
# A₂ Deligne classical freeness: assembly of the pieces

The A₂ case of the higher-rank capstone, for the actual simple VOA `L_{-3/2}(sl₃)`, with the
explicit presentation by the eight quadrics `I₂ⁿˢ`.  Everything except three named inputs is
proved:

* relations: `A2.explicitPresentation` (`I2ns_le_ker`, via the weight-2 singular vector);
* jet surjectivity: `A2.explicitCurrentJetSurjectivity`;
* geometric carrier embedding: `A2.geometricCarrierEmbedding`, with no residual input;
* the character equality reduces to the inequality `Σ_p dim Carrier p N ≤ dim V_N`
  (`ordinaryCarrierCharacter_of_le`), split at the Demazure sum `demazureCoeff`.

The remaining inputs are hypotheses of the final theorem:

* `hcar`: carrier ≤ Demazure sum (paper: B1, U4, U5, U6);
* `StarIdentity`: Demazure sum = `∏(1+q^r)^8` (combinatorics);
* `KacWakimotoLowerBound`: `∏(1+q^r)^8 ≤ dim V_N` (the Kac–Wakimoto character; literature).
-/

namespace VOA.DeligneAudit.A2

open VOA.DeligneHigherRankConditionalCapstone

/-- **A₂ Deligne classical freeness from the named residual inputs.** The conclusion also
identifies the explicit ideal `I₂ⁿˢ` with the full `C₂` kernel. -/
theorem classicallyFree_of_residualInputs
    (hcar : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) ≤
      demazureCoeff N)
    (hstar : StarIdentity) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns := by
  have hgeom := geometricCarrierEmbedding explicitPresentation rfl
  have hlow := carrierCharacterLowerBound_A2Carrier hcar
    (demazureCharacterBound_of_inputs hstar hkw)
  exact caseClassicallyFree_of_explicit_inputs .A2 W explicitPresentation Carrier
    explicitCurrentJetSurjectivity hgeom
    (ordinaryCarrierCharacter_of_le explicitPresentation Carrier
      explicitCurrentJetSurjectivity hgeom hlow)

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_residualInputs
end AxiomAudit
