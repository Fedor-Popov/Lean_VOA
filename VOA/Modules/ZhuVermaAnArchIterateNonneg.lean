/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUjacobi

/-!
# The module Borcherds identity for `ℓ ≥ 0` is **free** — no `ModuleIterate` needed

`module_borcherds` derives `MBL = MBR` for all `(ℓ, m, n)` from the residual `ModuleIterate`
(the `m = 0` slice) together with the locality slice `MBL_zero_ell` (`ℓ = 0`, which is free for a
`V̂`-representation, coming from `actMode_bracket`).

This file records a sharpening that materially narrows what `ModuleIterate` actually has to supply.
Inverting the recursion `MBL_rec`/`MBR_rec`,

  `MBL ℓ (m+1) n = MBL ℓ m (n+1) + MBL (ℓ+1) m n`   ⟹   `D (ℓ+1) m n = D ℓ (m+1) n − D ℓ m (n+1)`

for the discrepancy `D ℓ m n = MBL − MBR`, the `ℓ = 0` locality column propagates **upward in `ℓ`
for every `m` and `n` at once**.  Hence:

* **`module_borcherds_nonneg`** — `MBL = MBR` for every `ℓ ≥ 0` and every `m, n`, with NO
  `ModuleIterate` hypothesis;
* **`moduleIterate_nonneg`** — in particular the `ℓ ≥ 0` part of `ModuleIterate` is automatic.

So the entire genuine content of `ModuleIterate` sits at **`ℓ < 0`** — which is exactly Dong–Jiang's
Lemma 4.9 (the `Res_{z₀} z₀^{−L}` half of weak associativity); their Lemma 4.8 (`z₀`-powers `≥ 0`)
corresponds to the `ℓ ≥ 0` half proved here for free.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemmas 4.8, 4.9); `ZhuVermaAnArchMUjacobi` (`MBL`, `MBR`, `MBL_rec`,
`MBR_rec`, `MBL_zero_ell`, `ModuleIterate`, `module_borcherds`).
-/

namespace VOA

open VertexOperatorAlgebra
open VHat VHat.VHatRep
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {W : VertexOperatorAlgebra 𝒱}

/-- **The module Borcherds identity for every `ℓ ≥ 0`, unconditionally.**

Induction on `j : ℕ` with `ℓ = j`, generalizing over `m` and `n`: the base `j = 0` is the locality
slice `MBL_zero_ell`, and the step is the inverted recursion
`D (ℓ+1) m n = D ℓ (m+1) n − D ℓ m (n+1)` (`MBL_rec` minus `MBR_rec`).  **No `ModuleIterate`.** -/
theorem module_borcherds_nonneg (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (u v : 𝒱) (x : M) :
    ∀ (j : ℕ) (m n : ℤ), MBL ρ u v x (j : ℤ) m n = MBR ρ u v x (j : ℤ) m n := by
  intro j
  induction j with
  | zero =>
    intro m n
    simpa using MBL_zero_ell ρ htr u v x m n
  | succ j ih =>
    intro m n
    have hbl := MBL_rec ρ htr u v x (j : ℤ) m n
    have hbr := MBR_rec ρ u v x (j : ℤ) m n
    have h1 := ih (m + 1) n
    have h2 := ih m (n + 1)
    have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
    rw [hcast]
    -- `MBL (ℓ+1) m n = MBL ℓ (m+1) n − MBL ℓ m (n+1)`, and likewise for `MBR`
    have hL : MBL ρ u v x ((j : ℤ) + 1) m n
        = MBL ρ u v x (j : ℤ) (m + 1) n - MBL ρ u v x (j : ℤ) m (n + 1) := by
      rw [hbl]; abel
    have hR : MBR ρ u v x ((j : ℤ) + 1) m n
        = MBR ρ u v x (j : ℤ) (m + 1) n - MBR ρ u v x (j : ℤ) m (n + 1) := by
      rw [hbr]; abel
    rw [hL, hR, h1, h2]

/-- **The `ℓ ≥ 0` part of `ModuleIterate` is automatic** — it is the `m = 0` slice of
`module_borcherds_nonneg`.  Consequently the entire genuine content of `ModuleIterate` is the
regime `ℓ < 0` (Dong–Jiang's Lemma 4.9). -/
theorem moduleIterate_nonneg (ρ : VHatRep W M) (htr : ActModeTruncated ρ)
    (u v : 𝒱) (x : M) (j : ℕ) (N : ℤ) :
    ρ.actMode (W.smul u (j : ℤ) v) N x
      = ∑ᶠ i : ℤ, (negOnePow i * cbz (j : ℤ) i) •
          (ρ.actMode u ((j : ℤ) - i) (ρ.actMode v (N + i) x)
            - negOnePow (j : ℤ) • ρ.actMode v ((j : ℤ) + N - i) (ρ.actMode u i x)) := by
  have h := module_borcherds_nonneg ρ htr u v x j 0 N
  rw [MBR_zero_m, MBL_as_finsum ρ htr] at h
  rw [← h]
  exact finsum_congr fun i => by
    rw [show (j : ℤ) + (0 : ℤ) - i = (j : ℤ) - i from by ring,
      show (0 : ℤ) + i = i from by ring]

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.module_borcherds_nonneg
  #print axioms VOA.moduleIterate_nonneg
-/
