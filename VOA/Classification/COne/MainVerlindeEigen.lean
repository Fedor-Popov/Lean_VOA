/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkQExpAwayHeadline
import VOA.Huang.VerlindeRhoComplete
import VOA.Huang.VerlindeVacuumFusion

/-!
# Gannon–Rayhaun Theorem 3.1 (forward) with Huang's Verlinde input reduced to Thm 5.2

`HuangVerlindeFusionInput` is replaced by `FusionEigenInput` (Huang 2008, Thm 5.2: the S-matrix
diagonalizes the fusion matrices) using the proved
`VerlindeVacuum.huangVerlindeFusionInput_of_eigen_rho` with the proved
`VerlindeVacuum.vacuumFusionInput` (FHL A-transform) and `VerlindeRho.rhoNegOneInput_pbw`
(Huang Prop. 5.3).
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian
  VOA.Huang.VerlindeEigen

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** `#print axioms`: Lean's
three standard axioms only (the proof uses the theorem `VOA.pbw`); conditional on `FusionEigenInput`
(Huang Thm 5.2),
`DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`, `QExpPrinciple24Away 2` (Katz) and
`HuangHKLInterface`. -/
theorem gannonRayhaun_eigen
    (hE : FusionEigenInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_qExpAway zhuPBWBottomInput_of_pbw
    (VOA.Huang.VerlindeVacuum.huangVerlindeFusionInput_of_eigen_rho hE
      VOA.Huang.VerlindeRho.rhoNegOneInput_pbw) hC hG hQ hHK

end VOA.Classification.COne
