/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.CommutativityAnalytic
import VOA.Huang.PzTensorDecomp

/-!
# Half commutativity from the library citations (corollary)

Combining `CommutativityTarget.commutativityHalfReal_of_assoc` with the V4 result
`PzTensorDecomp.associativityInput_of_DLM` / `associativityInput_of_citations`:
`CommutativityHalfReal W` holds for every strongly rational `W`, conditional on exactly the
library citations that `AssociativityInput` rests on (ABD Prop. 5.7 and DLM Thm. 8.1(b),(c), resp.
ABD Cor. 5.8 + finiteness of `Φ`).  The full `CommutativityInputReal W` additionally needs
`AssociativityConverse W` (open, V4).

## Status
No `sorry`, no new axioms.  `#print axioms`-clean, **conditional on** the named citations.
-/

namespace VOA.Huang.CommutativityTarget

open VOA VOA.Huang.AssocTarget VOA.Huang.PzTensorDecomp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- `CommutativityHalfReal` from ABD Prop. 5.7 and DLM Thm. 8.1(b), (c). -/
theorem commutativityHalfReal_of_DLM (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hDLMc : DLMSimpleAdmissibleOrdinary W) (hDLMb : DLMFinitelyManyIrredAdmissible W) :
    CommutativityHalfReal W :=
  commutativityHalfReal_of_assoc hV (associativityInput_of_DLM hV hABD hDLMc hDLMb)

/-- `CommutativityInputReal` from the same citations and the (open) converse associativity. -/
theorem commutativityInputReal_of_DLM (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hDLMc : DLMSimpleAdmissibleOrdinary W) (hDLMb : DLMFinitelyManyIrredAdmissible W)
    (hC : AssociativityConverse W) : CommutativityInputReal W :=
  commutativityInputReal_of_assoc hV (associativityInput_of_DLM hV hABD hDLMc hDLMb) hC

/-- `CommutativityHalf` (analytic form) from ABD Prop. 5.7 and DLM Thm. 8.1(b), (c). -/
theorem commutativityHalf_of_DLM (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hDLMc : DLMSimpleAdmissibleOrdinary W) (hDLMb : DLMFinitelyManyIrredAdmissible W) :
    CommutativityHalf W :=
  commutativityHalf_of_assoc hV (associativityInput_of_DLM hV hABD hDLMc hDLMb)

/-- `CommutativityInput` (analytic form) from the same citations and the (open) converse. -/
theorem commutativityInput_of_DLM (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hDLMc : DLMSimpleAdmissibleOrdinary W) (hDLMb : DLMFinitelyManyIrredAdmissible W)
    (hC : AssociativityConverse W) : CommutativityInput W :=
  commutativityInput_of_assoc hV (associativityInput_of_DLM hV hABD hDLMc hDLMb) hC

end VOA.Huang.CommutativityTarget
