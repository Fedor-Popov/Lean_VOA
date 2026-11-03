/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.AdamovicSymbolDegreeOne
import VOA.Examples.RRLowerGram
import VOA.Examples.RRLowerGramBound

/-!
# The Lee–Yang endpoint with the Rogers–Ramanujan combinatorics discharged

`leeYang_gradedUnitary_of_affine_wordSymbols_two` takes `lower : LeeYangRRLowerBound`, which
bundles the Rocha-Caridi character lower bound with the second Rogers–Ramanujan identity.  The
latter is proved (`RRLower.sum_gapTwoCoefficient_eq_rc`), so the endpoint is restated with
the purely representation-theoretic hypothesis `RRLower.LeeYangRochaCaridiLowerBound`.

* `leeYang_gradedUnitary_of_affine_wordSymbols_rc` — `#print axioms`-clean, conditional on
  `hA`, `desc`, `chi`, `lowerRC` (Rocha-Caridi / Feigin–Fuchs lower bound). All three are since
  proved: `Desc.wordSymbolDescends`, `JetProduct.jetProductBound_of_lower
  JetFermionic.jetFermionicLower`, `RRLower.leeYangRochaCaridiLowerBound_holds`.
* `leeYang_gradedUnitary_of_affine_wordSymbols_gram` — the same with the residual stated as the
  rank bound `rc N ≤ rank (vermaGramMatrix (-22/5) 0 N)` on the explicit Shapovalov matrix.
-/

namespace VOA.AdamovicSymbol

open VOA.SymbolModel VOA.ConcreteHodge VOA.LeeYangTransferAssembly Sl2CosetConcrete
open VOA.AffineVOA VOA.AffineVOA.Inst VOA.AffineVOA.CorrectedR VOA.VertexOperatorAlgebra
open AffineSl2GeneralRigidity MvPolynomial

/-- **Affine GU ⇒ Lee–Yang GU**, with the Rogers–Ramanujan identity discharged: the only
character input left is the Rocha-Caridi lower bound
`Σ_k (-1)^k p(N - k(5k+3)/2) ≤ dim L(-22/5,0)_N`. -/
theorem leeYang_gradedUnitary_of_affine_wordSymbols_rc
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (desc : ∀ r : ℕ, WordSymbolDescends (r + 2)) (chi : JetProductBound)
    (lowerRC : RRLower.LeeYangRochaCaridiLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_wordSymbols_two hA desc chi
    (RRLower.leeYangRRLowerBound_iff_rochaCaridi.mpr lowerRC)

/-- The endpoint with the character input stated as a rank bound on the explicit `p(N) × p(N)`
Shapovalov matrix of the Verma module `M(-22/5, 0)`. -/
theorem leeYang_gradedUnitary_of_affine_wordSymbols_gram
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (desc : ∀ r : ℕ, WordSymbolDescends (r + 2)) (chi : JetProductBound)
    (gram : RRLower.LeeYangGramRankBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_wordSymbols_rc hA desc chi (RRLower.rochaCaridi_of_gramRank gram)

end VOA.AdamovicSymbol
