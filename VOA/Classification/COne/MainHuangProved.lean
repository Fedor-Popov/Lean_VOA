/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainVerlindeProved
import VOA.Huang.HuangModularityQDim

/-!
# Gannon–Rayhaun Theorem 3.1 (forward) with Huang's modular tensor category proved

Huang's theorems — the braided tensor category, rigidity, the Verlinde formula and modularity
(`VOA.Huang.HuangModularity.huangRepInput_holds`) — are proved for every nice VOA, using
the theorem `VOA.pbw` and no further hypothesis.  The Huang half
of `HuangHKLInterface` is discharged (`huangHKLInterface_of_hklRep`); only the
Huang–Kirillov–Lepowsky extension theorem (`HKLRepInput`) remains on that side.

## Status
No `sorry`, no new axioms.  `#print axioms`: Lean's three standard axioms only (`VOA.pbw` is a
theorem).  The forward theorem
`gannonRayhaun_huang` is conditional on `DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`,
`QExpPrinciple24Away 2` and `HKLRepInput`.
-/

namespace VOA.Classification.COne

open VOA.Huang.CongruenceGaloisSplit

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), strongest form.** `#print axioms`: Lean's three
standard axioms only (the proof uses the theorem `VOA.pbw`).
Conditional on `DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`,
`QExpPrinciple24Away 2` and the HKL extension theorem `HKLRepInput`; all of Huang's theory
(Verlinde, rigidity, modularity) is discharged. -/
theorem gannonRayhaun_huang
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2)
    (hR : VOA.Huang.TensorCat.BraidRibbon.HKLRepInput.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_verlinde hC hG hQ (VOA.Huang.HuangModularity.huangHKLInterface_of_hklRep hR)

end VOA.Classification.COne
