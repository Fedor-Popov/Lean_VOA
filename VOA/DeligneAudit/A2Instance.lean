/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.DeligneHigherRankConditionalCapstone
import VOA.Examples.AffineSl3Simple

/-!
# The A₂ Deligne case on the actual simple affine `sl₃` VOA

The higher-rank capstone is stated for an arbitrary VOA carrying the right number of weight-one
currents.  For A₂ the library already has the genuine VOA: `VOA.AffineSl3.simpleVOA k hk` is the
simple quotient of the universal affine `sl₃` VOA at any noncritical level.  This file
specializes the capstone to the Deligne level `k = -3/2`.

The `C₂` presentation package is discharged outright, by taking the ideal to be the full kernel
of the current-coordinate map; only containment is required.  The three remaining packages
(`CurrentJetSurjectivity`, `GeometricCarrierEmbedding`, `OrdinaryCarrierCharacter`) are left
as explicit hypotheses about this one VOA.
-/

namespace VOA.DeligneAudit.A2

open VOA.AffineSl3 VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- The A₂ Deligne level is noncritical. -/
theorem level_add_three_ne_zero : (-3 / 2 : ℂ) + 3 ≠ 0 := by norm_num

/-- The Deligne level recorded in the capstone is `-3/2`. -/
theorem level_eq : (HigherRankDeligneCase.level .A2 : ℂ) = -3 / 2 := by
  norm_num [HigherRankDeligneCase.level]

/-- The actual simple affine `sl₃` VOA at the Deligne level. -/
abbrev W := simpleVOA (-3 / 2) level_add_three_ne_zero

/-- The eight Chevalley current states. -/
def gen (a : Fin 8) : SimpleSpace (-3 / 2) level_add_three_ne_zero :=
  simpleCurrentState _ _ (generator a)

theorem gen_weight_one (a : Fin 8) : gen a ∈ W.grading (1 : ℤ) := by
  rw [simple_grading_one_eq_range]
  exact ⟨generator a, rfl⟩

/-- The current-coordinate presentation of the actual `C₂` algebra of `L_{-3/2}(sl₃)`, by the
full kernel. -/
def presentation : CurrentC2Presentation .A2 W where
  gen := gen
  gen_weight_one := gen_weight_one
  ideal := RingHom.ker
    (MvPolynomial.aeval fun i =>
      liDegreeZeroClass W 1 ⟨gen i, gen_weight_one i⟩).toRingHom
  relations := le_rfl

/-- **A₂ Deligne case, conditional on the three remaining packages.** -/
theorem classicallyFree_of_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : CurrentJetSurjectivity .A2 W presentation)
    (hgeom : GeometricCarrierEmbedding .A2 W presentation Carrier)
    (hchar : OrdinaryCarrierCharacter W Carrier) :
    CaseClassicallyFree .A2 W presentation :=
  (caseClassicallyFree_of_explicit_inputs .A2 W presentation Carrier hsurj hgeom hchar).1

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.presentation
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_inputs
end AxiomAudit
