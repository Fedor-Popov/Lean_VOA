/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainSerreStark
import VOA.Classification.COne.SerreStarkLevelTheoremA

/-!
# Gannon–Rayhaun Theorem 3.1 with the Serre–Stark level-box residual

`SerreStarkSquareClass24` is replaced by the narrower `SerreStarkLevelBox24` (S4:
`squareClass_of_boundedCoeff_of_levelBox`), which is itself a proved consequence of Theorem A
(`levelBox_of_theoremA`).
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion
  VOA.Huang.HuangTierReduced

universe u

/-- **Current strongest form, S4.** Serre–Stark enters only through
`SerreStarkBoundedCoeff24` (bounded denominators) and `SerreStarkLevelBox24` (Serre–Stark's level
analysis for class forms whose coefficients vanish on the finite level box). -/
theorem gannonRayhaun_current_levelBox
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hB : SSHecke.SerreStarkBoundedCoeff24) (hL : SSHecke.SerreStarkLevelBox24)
    (hFib : SymmetricFiberFunctorExists.{0, 0}) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_recon hPBW hAM hV hC hG hB
    (SSHecke.squareClass_of_boundedCoeff_of_levelBox hB hL) hFib hHK

end VOA.Classification.COne
