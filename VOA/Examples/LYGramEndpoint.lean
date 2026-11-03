/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.RRLowerEndpoint
import VOA.Examples.LYGramRank
import VOA.Examples.LYGramRankCharacter

/-!
# The Lee–Yang endpoint with the Rocha-Caridi character discharged

`RRLower.LeeYangGramRankBound` is proved (`RRLower.leeYangGramRankBound_holds`,
`LYGramRank.lean`), so the character input disappears from the endpoint.

* `leeYang_gradedUnitary_of_affine_wordSymbols_final` — `#print axioms`-clean, conditional on
  `hA` (affine GU), `desc : ∀ r, WordSymbolDescends (r + 2)` (constructed:
  `Desc.wordSymbolDescends`, `AdamovicDescCyclic.lean`) and `chi : JetProductBound` (proved:
  `JetProduct.jetProductBound_of_lower JetFermionic.jetFermionicLower`).
-/

namespace VOA.AdamovicSymbol

open VOA.SymbolModel VOA.ConcreteHodge VOA.LeeYangTransferAssembly Sl2CosetConcrete
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR VOA.VertexOperatorAlgebra
open AffineSl2GeneralRigidity MvPolynomial

/-- **Affine GU ⇒ Lee–Yang GU**, with the whole character input (Rocha-Caridi lower bound and
the second Rogers–Ramanujan identity) proved. -/
theorem leeYang_gradedUnitary_of_affine_wordSymbols_final
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (desc : ∀ r : ℕ, WordSymbolDescends (r + 2)) (chi : JetProductBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_wordSymbols_gram hA desc chi RRLower.leeYangGramRankBound_holds

end VOA.AdamovicSymbol
