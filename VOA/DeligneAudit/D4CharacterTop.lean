/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Final
import VOA.DeligneAudit.D4FiniteStatementProof

/-!
# The D₄ character side with the finite identity discharged

`D4FiniteIdentity` (the paper's finite polynomial identity (F)/(P)) is proved
(`d4FiniteIdentity_holds`). So the D₄ star identity "Demazure sum = Schur index" rests only on
`D4DemazurePositivity`, and the character bound needs, in addition, Arakawa's class-S theorem
`D4ClassS`.  Status of `D4DemazurePositivity` (`DeligneCharacterD4Positivity.lean`): its `energy`
half is proved (`D4Wp.energy_holds`); its `coeff` half follows from U5
(`D4Wp.d4DemazurePositivity_of_U5Z`), which remains open.
-/

namespace VOA.DeligneAudit.DeligneCharacter

open VertexOperatorAlgebra D4K

/-- D₄: Demazure sum = Schur index, from Demazure positivity alone. -/
theorem d4DemazureEqSchur_of_positivity (hpos : D4DemazurePositivity) : D4DemazureEqSchur :=
  d4DemazureEqSchur_holds D4Finite.d4FiniteIdentity_holds hpos

/-- D₄ character bound from Demazure positivity and class S. -/
theorem d4DemazureBound_of_literature {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (hpos : D4DemazurePositivity) (hS : D4ClassS W) :
    DemazureBoundFor W d4DemazureHilb :=
  d4DemazureBound W D4Finite.d4FiniteIdentity_holds hpos hS

end VOA.DeligneAudit.DeligneCharacter

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.d4DemazureEqSchur_of_positivity
#print axioms VOA.DeligneAudit.DeligneCharacter.d4DemazureBound_of_literature
end AxiomAudit
