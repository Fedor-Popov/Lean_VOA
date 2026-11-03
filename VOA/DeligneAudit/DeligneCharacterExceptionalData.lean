/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterTypes
import VOA.DeligneAudit.DeligneCharacterExceptionalParameters

/-! Unchanged named exceptional character inputs and target aliases. -/
namespace VOA.DeligneAudit.DeligneCharacter

open VertexOperatorAlgebra

/-! ## Named inputs -/

abbrev G2StarIdentity : Prop := StarIdentityQ g2DemazureHilb (mldeCoeff 4)
abbrev F4StarIdentity : Prop := StarIdentityQ f4DemazureHilb (mldeCoeff 9)
abbrev E6StarIdentity : Prop := StarIdentityQ e6DemazureHilb (mldeCoeff 12)
abbrev E7StarIdentity : Prop := StarIdentityQ e7DemazureHilb (mldeCoeff 18)
abbrev E8StarIdentity : Prop := StarIdentityQ e8DemazureHilb (mldeCoeff 30)

section
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)
abbrev G2TargetLowerBound : Prop := TargetLowerBoundQ W (mldeCoeff 4)
abbrev F4TargetLowerBound : Prop := TargetLowerBoundQ W (mldeCoeff 9)
abbrev E6TargetLowerBound : Prop := TargetLowerBoundQ W (mldeCoeff 12)
abbrev E7TargetLowerBound : Prop := TargetLowerBoundQ W (mldeCoeff 18)
abbrev E8TargetLowerBound : Prop := TargetLowerBoundQ W (mldeCoeff 30)
end


end VOA.DeligneAudit.DeligneCharacter
