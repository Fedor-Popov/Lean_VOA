/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.LieAlgebraV1

/-!
# `Core.V1LieAlgebra` — absorbed into `Core.LieAlgebraV1`

The unconditional `𝒱₁` Lie-algebra development (the skew-driven
antisymmetry `bracketV1_antisymm`, the `LieRing`/`LieAlgebra ℂ (𝒱₁)` instances
`instLieRingGradingOne`/`instLieAlgebraGradingOne`, and the bracket bilinearity lemmas) is
in **`Core.LieAlgebraV1`**, using skew-symmetry
(`Core.SkewSymmetry`/`Core.WeakAssoc`).  This module is only a
re-export so that the import path `VOA.Core.V1LieAlgebra` resolves; all the declarations are exported from
`VOA.Core.LieAlgebraV1`.

## Status
Re-export stub.  All declarations are exported from `Core.LieAlgebraV1`, which is
`sorry`-free / axiom-free.
-/
