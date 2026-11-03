/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Commutativity

/-!
# `Core.CommutativeRing` — absorbed into `Core.Commutativity`

The Theorem 5.1.4 (1) ⇒ (2) packaging — commutativity and associativity
of the `(−1)`-product `cmul` on a commutative vertex algebra (`cmul_comm_of_comm`,
`cmul_assoc_of_comm`), the `CommRing` bundle `commRing_of_comm`, and its derivation law — is
proved in **`Core.Commutativity`**, from skew-symmetry
(`Core.SkewSymmetry`) and the `n<0` duality (`Core.Reconstruction.assoc_neg`).
The full biconditional `comm_iff_assoc_alg` (1 ⇔ 2) lives there too.  This module is
only a re-export so existing import paths keep resolving.

## Status
Re-export stub.  All declarations are exported from `Core.Commutativity`, which is
`sorry`-free / axiom-free.
-/
