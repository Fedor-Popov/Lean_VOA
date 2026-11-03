/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorDecomp
import VOA.Huang.ZhuFiniteIrr
import VOA.Huang.ZhuSemisimple
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom

/-!
# `CoefSpanDecomp` from the PBW theorem `VOA.pbw`

`PzTensorDecomp.coefSpanDecomp_of_citations` carries `Finite (Φ W)` as an explicit hypothesis.
For a strongly rational `W` this finiteness is a theorem of the library, **using the PBW theorem
`VOA.pbw`**: `A(V)` is finite-dimensional (`C₂`), semisimple
(rationality, `ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational`), and Zhu's
correspondence makes `Φ(V)` inject into its simple modules (`ZhuFiniteIrr.finite_Φ_of_C2Cofinite`);
the PBW datum `Pr` is `voaPBWBottomProjection`, which specializes `VOA.pbw`.

* `finite_Φ_of_stronglyRational_voaPBW : StronglyRational W → Finite (Φ W)`;
* `coefSpanDecomp_of_ABD_voaPBW : StronglyRational W → ABDWeakIsAdmissible W →
  ABDIrreducibleWeakIsOrdinary W → CoefSpanDecomp W`;
* `associativityInput_of_ABD_voaPBW : … → AssociativityInput W`.

These declarations use the theorem `VOA.pbw`; they are kept in this separate file so that
`PzTensorDecomp` does not depend on it.  They are
conditional on the two Abe–Buhl–Dong citations; they are not unconditional.

## Status
No `sorry`; no non-Lean axiom (the proofs use the theorem `VOA.pbw`).
-/

namespace VOA.Huang.PzTensorDecompPBW

open VOA VOA.VHat VOA.VHat.DLM3 VOA.Huang.AssocTarget VOA.Huang.PzTensorHL6
open VOA.Huang.PzTensorDecomp

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Finitely many irreducible modules** for strongly rational `W` (PBW datum from the theorem
`VOA.pbw`). -/
theorem finite_Φ_of_stronglyRational_voaPBW (hV : StronglyRational W) : Finite (Φ W) :=
  VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hV.c2Cofinite
    (VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational
      (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hV.rational)

/-- **`CoefSpanDecomp` from the two Abe–Buhl–Dong citations** (PBW datum from the theorem
`VOA.pbw`). -/
theorem coefSpanDecomp_of_ABD_voaPBW (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hOrd : ABDIrreducibleWeakIsOrdinary W) : CoefSpanDecomp W :=
  coefSpanDecomp_of_citations hV hABD hOrd (finite_Φ_of_stronglyRational_voaPBW hV)

/-- **`AssociativityInput` from the two Abe–Buhl–Dong citations** (relative to
`VOA.pbw`). -/
theorem associativityInput_of_ABD_voaPBW (hV : StronglyRational W)
    (hABD : ABDWeakIsAdmissible W) (hOrd : ABDIrreducibleWeakIsOrdinary W) :
    AssociativityInput W :=
  associativityInput_of_citations hV hABD hOrd (finite_Φ_of_stronglyRational_voaPBW hV)

end VOA.Huang.PzTensorDecompPBW
