/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Automorphism

/-!
# `Core.InnerAutomorphism` — absorbed into `Core.Automorphism`

The locally-nilpotent-exponential machinery (`expSum`, `expFun`, `expEquiv`, `expFun_smul`,
the iterated Leibniz/binomial identity, the `exp(D)∘exp(−D)=id` convolution) and the inner
automorphisms (`inner = exp(u₍₀₎)`, the inner set, the normal subgroup `Inn`, and the
conjugation/normality core `isExpInner_conj`) are proved in **`Core.Automorphism`**.  This module is only a re-export
so that the import path `VOA.Core.InnerAutomorphism` resolves; all declarations are exported from
`VOA.Core.Automorphism`.

## Status
Re-export stub.  All declarations are exported from `Core.Automorphism`, which is
`sorry`-free / axiom-free.
-/
