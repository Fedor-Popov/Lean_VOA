/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SuperBorcherds
import VOA.Modules.SuperWeakModule

/-!
# The adjoint super weak module — the first inhabitant of `SuperWeakModule`

Apart from this file, `Modules.SuperWeakModule` has exactly one instance: `WeakModule.toSuper`,
the *trivial-parity* embedding of a bosonic weak module, in which every Koszul sign is `1`.  It is
not otherwise inhabited by anything with genuinely odd states, because its `jacobi` field has no
other proof in the repository.

`Core.SuperBorcherds.superJacobi` supplies it.  This file records the consequence: **every
super near-VOA is a weak module over itself**, with its own parity grading and the honest
Koszul sign.

## Why this is also the shape certificate for `superJacobi`

The `jacobi` field below is discharged by `superJacobi` *definitionally* — `mode (YM u) n x`
unfolds to `V.smul u n x` for `YM := V.Y`, and no rewriting is needed.  So the fact that this
definition typechecks is a machine-checked statement that `superJacobi` is **exactly** the
`SuperWeakModule.jacobi` identity, with the exchanged-term coefficient the single scalar
`koszul p q * negOnePow ℓ`, and not a weaker relative of it.

## Downstream (recorded, not built)

`Core.ScreeningKernel.IsSuperScreening` carries two hypotheses that the missing super-Borcherds
machinery forced (`ScreeningKernel.lean`, Status block).  One of them, `leibniz`
(`a₍₀₎(u₍ₙ₎v) = (a₍₀₎u)₍ₙ₎v + u₍ₙ₎(a₍₀₎v)` for even `a`), is dischargeable: it is
`SuperNearVOA.commBoundε` at `a`-mode `0`, where `C(0,j) = δ_{j0}` collapses the sum and
`koszul 0 q = 1` makes the twisted bracket the ordinary commutator.  The other, `conformal`
(`a₍₀₎ω = 0`), runs bosonically through skew-symmetry.  Super skew-symmetry is available
unconditionally (`superSmul_eq_skew_Lpow`, `Modularity/SuperZhuCommutator.lean`), so the gate
`SuperWeakAssoc.SkewVacLocal₀` is not an obstruction; `conformal` is nevertheless not
discharged, and this file does *not* touch it.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Every super near-VOA is a weak module over itself.**  All the module data is the
algebra's own; the Jacobi field is `Core.SuperBorcherds.superJacobi`.

This is the first inhabitant of `SuperWeakModule` with a nontrivial parity grading. -/
def SuperNearVOA.adjointSuperWeakModule (V : SuperNearVOA 𝒱) :
    SuperWeakModule V.toSuperVertexAlgebra 𝒱 where
  YM := V.Y
  parity := V.parity
  parity_isInternal := V.parity_isInternal
  parity_mode := V.parity_mode
  vacuum_YM := V.vacuum_Y
  truncation := V.regularity
  jacobi := by
    intro p q u hu v hv x ℓ m n
    exact SuperNearVOA.superJacobi V hu hv x ℓ m n

@[simp] theorem SuperNearVOA.adjointSuperWeakModule_act (V : SuperNearVOA 𝒱) (u : 𝒱) (n : ℤ)
    (x : 𝒱) : V.adjointSuperWeakModule.act u n x = V.smul u n x := rfl

end VOA
