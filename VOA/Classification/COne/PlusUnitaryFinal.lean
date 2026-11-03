/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryM1
import VOA.Classification.COne.PlusUnitaryVac
import VOA.Classification.COne.PlusUnitaryERel
import VOA.Classification.COne.PlusUnitaryEE

/-!
# `V_{2m}⁺` is pseudo-unitary

`v2mPlusPseudoUnitaryFactGe2_holds : V2mPlusPseudoUnitaryFactGe2` — **the cited fact
(Dong–Nagatomo, Comm. Math. Phys. 202 (1999), Thm 5.13, with the listed lowest weights) is a
theorem**: every irreducible ordinary `V_{2m}⁺`-module other than `V_{2m}⁺` itself has lowest
weight of positive real part.

The proof never classifies the irreducible modules.  On a top vector `x` (weight `h`, `o(W⁴)`
eigenvalue `w`) four statements are proved (`PlusUnitaryReduce.lean` assembles them):

* **H1** `plusM1Dichotomy_holds` (`PlusUnitaryM1`): `w = 2h` or `h ∈ {1/16, 9/16, 1}` — two
  kernel-checked relations of weights 8 and 10 in `A(M(1)⁺)`;
* **H2** `plusERelation_holds` (`PlusUnitaryERel`): `(h − m/4)(h − 1/16)(h − 9/16)·o(E)x = 0` — a
  kernel-checked relation in `A(V⁺)`, uniform in `m` (charge coordinate `c` symbolic);
* **H3** `plusEESquare_holds` (`PlusUnitaryEE`): on the curve, `o(E)x = 0` forces `4mh = j²`,
  `0 ≤ j < m` — interpolation of the degree-`≤ m` polynomial `o(E ∗ E)` on the lattice modules
  `V_{L+λ_j}`;
* **H4** `plusVacuumTop_holds` (`PlusUnitaryVac`): a top vector with the vacuum's eigenvalues
  generates `V⁺`.

Consequently the `.plus` clause of Gannon–Rayhaun Prop. 3.2 rests only on Abe's rationality theorem
(`nice_of_hasCOneLabel_plus_of_rational`).
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open PlusUnitary

/-- **`V_{2m}⁺` is pseudo-unitary for every `m ≥ 2`.** -/
theorem V2mPlus_pseudoUnitary_ge2 (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) : PseudoUnitary (V2mPlus m hm) :=
  pseudoUnitary_of_tops m hm (plusM1Dichotomy_holds m hm) (plusERelation_holds m hm hm2)
    (plusEESquare_holds m hm) (plusVacuumTop_holds m hm hm2)

/-- **The cited fact of Dong–Nagatomo (1999), Thm 5.13, is a theorem.** -/
theorem v2mPlusPseudoUnitaryFactGe2_holds : V2mPlusPseudoUnitaryFactGe2 :=
  fun m hm hm2 => V2mPlus_pseudoUnitary_ge2 m hm hm2

/-- The cited fact of `PlusNice.lean`, for all `m ≥ 1`. -/
theorem v2mPlusPseudoUnitaryFact_holds : V2mPlusPseudoUnitaryFact :=
  v2mPlusPseudoUnitaryFact_iff.mpr v2mPlusPseudoUnitaryFactGe2_holds

/-- **`V_{2m}⁺` is pseudo-unitary for every `m ≥ 1`.** -/
theorem V2mPlus_pseudoUnitary (m : ℕ) (hm : 1 ≤ m) : PseudoUnitary (V2mPlus m hm) :=
  v2mPlusPseudoUnitaryFact_holds m hm

/-- **`V_{2m}⁺` is nice**, conditional only on Abe's rationality theorem. -/
theorem nice_V2mPlus_of_rational (hRat : V2mPlusRationalFactGe2) (m : ℕ) (hm : 1 ≤ m) :
    Nice (V2mPlus m hm) :=
  nice_V2mPlus_of_rational_pseudoUnitary hRat v2mPlusPseudoUnitaryFactGe2_holds m hm

/-- **The `.plus` clause of Gannon–Rayhaun Prop. 3.2**, conditional only on Abe's rationality
theorem (`V2mPlusRationalFactGe2`; T. Abe, Math. Z. 249 (2005)). -/
theorem nice_of_hasCOneLabel_plus_of_rational (hRat : V2mPlusRationalFactGe2)
    {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (m : ℕ)
    (h : HasCOneLabel V (.plus m)) : Nice V ∧ V.centralCharge = 1 :=
  nice_of_hasCOneLabel_plus_of_rational_pseudoUnitary hRat v2mPlusPseudoUnitaryFactGe2_holds V m h

end VOA.Classification.COne

section AxiomAudit
#print axioms VOA.Classification.COne.PlusUnitary.plusM1Dichotomy_holds
#print axioms VOA.Classification.COne.PlusUnitary.plusERelation_holds
#print axioms VOA.Classification.COne.PlusUnitary.plusEESquare_holds
#print axioms VOA.Classification.COne.PlusUnitary.plusVacuumTop_holds
#print axioms VOA.Classification.COne.PlusUnitary.pseudoUnitary_of_tops
#print axioms VOA.Classification.COne.v2mPlusPseudoUnitaryFactGe2_holds
#print axioms VOA.Classification.COne.V2mPlus_pseudoUnitary
#print axioms VOA.Classification.COne.nice_V2mPlus_of_rational
#print axioms VOA.Classification.COne.nice_of_hasCOneLabel_plus_of_rational
end AxiomAudit
