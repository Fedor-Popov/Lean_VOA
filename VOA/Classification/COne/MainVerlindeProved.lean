/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainVerlindeEigen
import VOA.Huang.GenusOneG1fSeparation

/-!
# Gannon–Rayhaun Theorem 3.1 (forward) with Huang's Verlinde theorem proved

`VOA.Huang.GenusOneG1f.fusionEigenInput_holds` proves Huang's Theorem 5.2 (Huang 2008, "Vertex
operator algebras and the Verlinde conjecture": the modular S-matrix diagonalizes the fusion
matrices) for every nice VOA; the proof uses the theorem `VOA.pbw`, so no hypothesis beyond niceness
remains.  Here it is
plugged into the forward headline, and Huang's Verlinde fusion input is recorded as a theorem.

## Status
No `sorry`, no new axioms.  `#print axioms`: Lean's three standard axioms only (`VOA.pbw` is a
theorem).  The forward theorem
`gannonRayhaun_verlinde` is conditional on `DLNCongruenceInput`,
`GaloisSymmetryNontrivialInput`, `QExpPrinciple24Away 2` and `HuangHKLInterface`.
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian
  VOA.Huang.VerlindeEigen

universe u

/-- **Huang's Verlinde formula (fusion form), proved.** Uses the theorem `VOA.pbw`; no further
hypothesis. -/
theorem huangVerlindeFusionInput_holds : VOA.Huang.VerlindeFusion.HuangVerlindeFusionInput.{u, u + 1} :=
  VOA.Huang.VerlindeVacuum.huangVerlindeFusionInput_of_eigen_rho
    VOA.Huang.GenusOneG1f.fusionEigenInput_holds VOA.Huang.VerlindeRho.rhoNegOneInput_pbw

/-- **Gannon–Rayhaun Theorem 3.1 (forward), strongest form.** `#print axioms`: Lean's three
standard axioms only (the proof uses the theorem `VOA.pbw`).
Conditional on `DLNCongruenceInput`,
`GaloisSymmetryNontrivialInput`, `QExpPrinciple24Away 2` (Katz) and `HuangHKLInterface`;
Huang's Verlinde theorem is discharged. -/
theorem gannonRayhaun_verlinde
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_eigen VOA.Huang.GenusOneG1f.fusionEigenInput_holds hC hG hQ hHK

end VOA.Classification.COne
