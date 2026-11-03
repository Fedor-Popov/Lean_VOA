/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaAssemble
import VOA.Moonshine.FZBimoduleKey
import VOA.Moonshine.FZGenBridge

/-!
# The Moonshine module from one finite top-level identity  (step M9, sharpest conditional form)

Composes three separately proved ingredients:

* the explicit triality data `SigmaAssemble.mkData c ε` with its isometry properties
  (`PhiTop`/`ThetaTop` discharged inside `SigmaAssemble.moonshine_of_keySkew`);
* bimodule generation of `A(V₃⁺)` by its weight-2 top (`FZGen.fzGenerated_MV3`, unconditional);
* the Frenkel–Zhu reduction `FZKey.keySkew_of_FZ : BimodGenV3 → TopPairs D → KeySkew D t`.

What is left is `FZKey.TopPairs` for the explicit data: a FINITE identity on the weight-2 top levels
(`V₃⁺₂`, dimension 49152), `Θ (o(v) Φb) = o(b) Φv` for all top vectors `v, b`.  It is checked
numerically on samples and proved in Lean as
`TopPairs.top_pairs0` (`TopPairsCore.lean`), packaged for the explicit data as
`Moonshine.topPairs_one`.

## Status
`#print axioms moonshine_of_topPairs = [propext, Classical.choice, Quot.sound]`. Its hypothesis is
discharged (for `ε = 1`) by `Moonshine.topPairs_one` (TopPairs.lean), giving the unconditional
`Moonshine.moonshine`.
-/

namespace VOA.Moonshine

open SigmaAssemble

/-- **The Moonshine module, conditional only on the finite top-level identity `TopPairs`** for the
explicit triality data with one sign `ε = ±1`. -/
theorem moonshine_of_topPairs {ε : ℂ} (hε : ε * ε = 1)
    (htop : FZKey.TopPairs (mkData cStar0 ε (c_ne_of_norm cStar0_norm) hε)) :
    ∃ V : VertexOperatorAlgebra Vnat,
      V.Y = Ynat VnatAxioms.wbarL ∧ V.vacuum = vacNat ∧ V.conformalVector = omegaNat ∧
      V.centralCharge = 24 ∧
      V.grading 1 = ⊥ ∧
      Module.finrank ℂ (V.grading 2) = 196884 ∧
      (∀ n : ℕ, (Module.finrank ℂ (V.grading (n : ℤ)) : ℂ) = PowerSeries.coeff n JShift) ∧
      V.IsSimple :=
  moonshine_of_keySkew cStar0_norm hε
    (FZKey.keySkew_of_FZ _ tF_mem tF_ne FZGen.fzGenerated_MV3 htop)

end VOA.Moonshine
