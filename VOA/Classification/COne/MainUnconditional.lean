/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.DLNSmallMain
import VOA.Huang.DLNSchur6Relations

/-!
# The forward Gannon–Rayhaun classification, with no open hypothesis

Gannon–Rayhaun, arXiv:2609.00122, Theorem 3.1, forward direction: every nice (strongly rational,
pseudo-unitary) vertex operator algebra of central charge `1` is isomorphic to one of `V_{2m}`,
`V_{2m}⁺`, `V₂^{A₄}`, `V₂^{S₄}`, `V₂^{A₅}` (`GannonRayhaunStatement`).

All inputs of the conditional forms (`gannonRayhaun_main` and its refinements) are theorems:
* Huang's modular tensor category, Verlinde formula, rigidity and modularity;
* the Huang–Kirillov–Lepowsky extension, its locality and rationality (`hklRationalInput_holds`);
* the weight-two `q`-expansion principle (`SSHecke.qExpPrinciple24Away_two`);
* Dong–Lin–Ng Theorem 3.10 (`zhuModularRepresentationInput_holds`), Ng–Schauenburg's congruence
  theorem (`nsProjectiveKernelAll_holds`) and the Galois twist law;
* Beyl's Schur-multiplier facts for `SL₂(ℤ/p^k)`: `p = 3` (`threePowerSchur`), the `2`-adic
  inflation (`twoPowerInflationFromTwo_holds`) and `p ≥ 5` (`largePrimeGaussLowerRelations`).

The theorem below therefore has no hypotheses and is unconditional: its `#print axioms` is
Lean's three standard axioms.  (Its proof uses `VOA.pbw`, the PBW theorem for affine Lie
algebras, which is a theorem of the library.)  The
converse direction (`GannonRayhaunConverse`: each
listed VOA is nice) is a separate statement and is not proved here.
-/

namespace VOA.Classification.COne

universe u

/-- **Forward Gannon–Rayhaun classification of nice `c = 1` VOAs** (Theorem 3.1, forward
direction), with no hypotheses; uses the theorem `VOA.pbw`. -/
theorem gannonRayhaun_forward : GannonRayhaunStatement.{u} :=
  gannonRayhaun_beyl_large VOA.Huang.DLNSchur.largePrimeGaussLowerRelations

end VOA.Classification.COne
