/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuInduced

/-!
# The Zhu lifting `InducedAssignment` from *pointwise* realizability

`Modules.ZhuInduced` reduced Theorem 5.3.4's lifting direction to one object `InducedAssignment W`
(a global `realize : AMod W → LWModule W` + bottom-iso + iso-class-invariance). This file weakens the
carrier-existence input to the more natural **pointwise** form — *every* `A(𝒱)`-module is realizable
(`∀ U, HasInducedModule W U`) — plus the single universal-property gap **`BottomIsoLifts`** (an
`A(𝒱)`-iso of bottoms lifts to a `𝒱`-module iso), and assembles a full `InducedAssignment W` from
exactly these two inputs.

* **`BottomIsoLifts W`** — the universal property: `Nonempty (AModEquiv P.toAMod Q.toAMod) → P.Iso Q`.
* **`realizeOfPointwise`** — the `realize` function chosen (`Classical.choice`) from pointwise
  realizability; **`isoInvariantOfPointwise`** — its iso-invariance via `BottomIsoLifts`.
* **`inducedAssignmentOfPointwise`** — the full `InducedAssignment W` term, hence (via the proved
  `InducedAssignment.forwardMap_invFun`) **`forwardMap_invFun_ofPointwise`**: the Theorem-5.3.4
  round-trip `forwardMap ∘ invFun = id` from the two pointwise inputs.

## Status
Axiom-clean as *conditional* results. The lifting half is expressed through two inputs:
`HasInducedModule` (the Frenkel–Zhu carrier, not constructed here) and `BottomIsoLifts`.

⚠ **Honest caveat (verified).** `BottomIsoLifts W` as stated — *every* pair of lowest-weight modules
with `A(𝒱)`-isomorphic bottoms is isomorphic — is **too strong (false)**: the generalized-Verma
`M(U)` and its irreducible quotient `L(U)` both have bottom `U` yet are non-isomorphic `LWModule`s.
Bottoms determine modules only for **irreducible** modules (the Zhu correspondence), which is itself
the theorem. So this `BottomIsoLifts` cannot be discharged; the genuine lifting requires restricting
to irreducibles (where `isoInvariant` holds) — equivalent in strength to Theorem 5.3.4's bijection.
These results are kept as honest conditional infrastructure, not a dischargeable reduction.

## References
* Gannon §5.3.2, Thm 5.3.4; Frenkel–Zhu; Dong–Li–Mason.
-/

namespace VOA

open scoped BigOperators
open Classical
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`BottomIsoLifts W`** — the universal property: an `A(𝒱)`-iso of bottoms lifts to a
`𝒱`-module iso. -/
def BottomIsoLifts (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ P Q : LWModule W, Nonempty (AModEquiv W P.toAMod Q.toAMod) → LWModule.Iso W P Q

/-- **The `realize` function from pointwise realizability.** -/
noncomputable def realizeOfPointwise (W : VertexOperatorAlgebra 𝒱)
    (hreal : ∀ U : AMod W, HasInducedModule W U) (U : AMod W) : LWModule W :=
  (hreal U).some.N

/-- The chosen realization's bottom is `U`. -/
noncomputable def realizesOfPointwise (W : VertexOperatorAlgebra 𝒱)
    (hreal : ∀ U : AMod W, HasInducedModule W U) (U : AMod W) :
    AModEquiv W (realizeOfPointwise W hreal U).toAMod U :=
  (hreal U).some.bottomEquiv

/-- **Iso-invariance of the chosen realization**, via `BottomIsoLifts`. -/
theorem isoInvariantOfPointwise (W : VertexOperatorAlgebra 𝒱)
    (hreal : ∀ U : AMod W, HasInducedModule W U) (hlift : BottomIsoLifts W)
    (U U' : AMod W) (h : Nonempty (AModEquiv W U U')) :
    LWModule.Iso W (realizeOfPointwise W hreal U) (realizeOfPointwise W hreal U') := by
  obtain ⟨e⟩ := h
  refine hlift (realizeOfPointwise W hreal U) (realizeOfPointwise W hreal U') ⟨?_⟩
  exact AModEquiv.trans W (realizesOfPointwise W hreal U)
    (AModEquiv.trans W e (AModEquiv.symm W (realizesOfPointwise W hreal U')))

/-- **The full `InducedAssignment W` from pointwise realizability + bottom-lifting.** -/
noncomputable def inducedAssignmentOfPointwise (W : VertexOperatorAlgebra 𝒱)
    (hreal : ∀ U : AMod W, HasInducedModule W U) (hlift : BottomIsoLifts W) :
    InducedAssignment W where
  realize := realizeOfPointwise W hreal
  realizes := realizesOfPointwise W hreal
  isoInvariant := isoInvariantOfPointwise W hreal hlift

/-- **The Theorem-5.3.4 round-trip from pointwise realizability + bottom-lifting.** -/
theorem forwardMap_invFun_ofPointwise (W : VertexOperatorAlgebra 𝒱)
    (hreal : ∀ U : AMod W, HasInducedModule W U) (hlift : BottomIsoLifts W)
    (x : AModIsoClass W) :
    forwardMap W ((inducedAssignmentOfPointwise W hreal hlift).invFun x) = x :=
  (inducedAssignmentOfPointwise W hreal hlift).forwardMap_invFun x

/-- The forward map of the chosen realization is `[U]`: `forwardMap [realize U] = [U]`. -/
theorem forwardMap_realizeOfPointwise (W : VertexOperatorAlgebra 𝒱)
    (hreal : ∀ U : AMod W, HasInducedModule W U) (U : AMod W) :
    forwardMap W (Quotient.mk (LWModule.setoid W) (realizeOfPointwise W hreal U))
      = Quotient.mk (AMod.setoid W) U := by
  rw [forwardMap_mk]
  exact Quotient.sound ⟨realizesOfPointwise W hreal U⟩

end VOA
