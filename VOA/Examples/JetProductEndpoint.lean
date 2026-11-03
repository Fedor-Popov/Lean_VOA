/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetProductCount
import VOA.Examples.LYGramEndpoint

/-!
# The jet-ring character bound reduced to a pure q-series identity

`JetProductBound` (`[q^N] ((q³;q³)_∞/(q;q)_∞)³ ≤ Σ_{r ≤ N} dim A_{r,N}`) follows from
the proved lower bound `coeff_jetSeries_le` (`[q^N] jetSeries ≤ Σ_r dim A_{r,N}`) and the
q-series identity

  `Σ_{r ≥ 0} q^r (Σ_{k=0}^{2r} [2r, k]_q) / (q)_r = ((q³;q³)_∞ / (q;q)_∞)³`

(`JetFermionicIdentity`; proved in `JetFermionicIdentity.lean` as `jetFermionicIdentity`; the `n = 1` case of Chern–Tran–Wakhare, Theorem 1.2,
combined with Jacobi's cube identity, which the repository has as `jacobi_cube`).  Only the
inequality `JetFermionicLower` is needed.

* `jetProductBound_of_lower` / `jetProductBound_of_identity`;
* `leeYang_gradedUnitary_of_affine_jetFermionic` — **Affine GU ⇒ Lee–Yang GU**,
  `#print axioms`-clean, conditional on `hA`, `desc`, and the q-series inequality.
-/

namespace VOA.JetProduct

open VOA.SymbolModel

/-- **The fermionic q-series identity** (proved downstream: `JetFermionicIdentity.jetFermionicIdentity`): the `n = 1` case of Chern–Tran–Wakhare,
Theorem 1.2, together with Jacobi's cube identity. -/
def JetFermionicIdentity : Prop := jetSeries = AffineSl2BoundaryCharacter.product 1

/-- The coefficientwise inequality that is actually used. -/
def JetFermionicLower : Prop :=
  ∀ N : ℕ, PowerSeries.coeff N (AffineSl2BoundaryCharacter.product 1) ≤
    PowerSeries.coeff N jetSeries

theorem jetFermionicLower_of_identity (h : JetFermionicIdentity) : JetFermionicLower :=
  fun N => by rw [h]

/-- The jet-ring character bound from the q-series inequality. -/
theorem jetProductBound_of_lower (h : JetFermionicLower) : JetProductBound :=
  fun N => (h N).trans (coeff_jetSeries_le N)

/-- The jet-ring character bound from the q-series identity. -/
theorem jetProductBound_of_identity (h : JetFermionicIdentity) : JetProductBound :=
  jetProductBound_of_lower (jetFermionicLower_of_identity h)

end VOA.JetProduct

namespace VOA.AdamovicSymbol

open VOA.SymbolModel VOA.LeeYangTransferAssembly Sl2CosetConcrete

/-- **Affine GU ⇒ Lee–Yang GU**, with the jet-ring character bound reduced to the
q-series inequality `JetFermionicLower`. -/
theorem leeYang_gradedUnitary_of_affine_jetFermionic
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (desc : ∀ r : ℕ, WordSymbolDescends (r + 2)) (hq : VOA.JetProduct.JetFermionicLower) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_wordSymbols_final hA desc
    (VOA.JetProduct.jetProductBound_of_lower hq)

end VOA.AdamovicSymbol
