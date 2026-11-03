/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetStrictSqueeze
import VOA.Examples.AffineSl2BoundaryMainTheorems
import VOA.Examples.KoszulResidualSymbolMaps

/-!
# The endpoint with strictness split into a leading-symbol map and a jet-ring character bound

* `JetProductBound` — a statement purely about the jet ring `ℂ[u_j, v_j]`: the `q^N` coefficient
  of the boundary product `((q³;q³)_∞ / (q;q)_∞)³` is at most `Σ_{r ≤ N} dim A_{r,N}`
  (proved: `JetProduct.jetProductBound_of_lower JetFermionic.jetFermionicLower`, files
  `JetProductEndpoint.lean`, `JetFermionicIdentity.lean`; first checked numerically, exact
  equality, for `N ≤ 9` by random-point rank computation);
* `jetCharacterBound_of_product` — via the proved Arakawa–Dai character theorem
  `character_eq_product 1`, it gives the VOA-side `JetCharacterBound` (proved);
* `grJetStrict_of_leadingSymbol_product` — `strict : ∀ r, GrJetStrict (r+1)` from the
  leading-symbol maps (`r ≥ 1`) and `JetProductBound`;
* `leeYang_gradedUnitary_of_affine_leadingSymbol` — **Affine GU ⇒ Lee–Yang GU**,
  `#print axioms`-clean, conditional on `hA` (the hypothesis), `sym` (the filtered Adamović
  leading-symbol maps, surjective, `r ≥ 1`), `chi` (the jet-ring character bound),
  `lower` (classical Rogers–Ramanujan).
-/

namespace VOA.SymbolModel

open VOA.LeeYangTransferAssembly Sl2CosetConcrete
open scoped BigOperators

noncomputable section

/-- **The jet-ring character bound**: a statement about `ℂ[u_j, v_j]` and a `q`-product
only. Proved: `VOA.JetProduct.jetProductBound_of_lower VOA.JetFermionic.jetFermionicLower`
(`JetProductEndpoint.lean`, `JetFermionicIdentity.lean`). -/
def JetProductBound : Prop :=
  ∀ N : ℕ, PowerSeries.coeff N (AffineSl2BoundaryCharacter.product 1) ≤
    ∑ r ∈ Finset.range (N + 1), (Module.finrank ℂ (jetDeg r (N : ℤ)) : ℚ)

/-- The jet-ring bound gives the VOA-side character bound, through the proved boundary
character theorem. -/
theorem jetCharacterBound_of_product (h : JetProductBound) : JetCharacterBound := by
  intro N
  have h1 := h N
  rw [← AffineSl2BoundaryCharacter.character_eq_product 1 le_rfl,
    AffineSl2BoundaryCharacter.coeff_character] at h1
  exact_mod_cast h1

/-- Strictness for `r ≥ 1` from the leading-symbol maps and the jet-ring character bound. -/
def grJetStrict_of_leadingSymbol_product (sym : ∀ r, JetLeadingSymbol (r + 1))
    (chi : JetProductBound) (r : ℕ) : GrJetStrict (r + 1) :=
  grJetStrict_succ_of_leadingSymbol sym (jetCharacterBound_of_product chi) r

end

end VOA.SymbolModel

namespace VOA.KoszulResidual

open VOA.SymbolModel VOA.LeeYangTransferAssembly

/-- **Affine GU ⇒ Lee–Yang GU**, with strictness split into the filtered leading-symbol maps
and the jet-ring character bound. `#print axioms`-clean, conditional on `hA` (the hypothesis),
`sym`, `chi`, `lower`. -/
theorem leeYang_gradedUnitary_of_affine_leadingSymbol
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (sym : ∀ r : ℕ, JetLeadingSymbol (r + 1)) (chi : JetProductBound)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_strict hA (grJetStrict_of_leadingSymbol_product sym chi) lower

end VOA.KoszulResidual
