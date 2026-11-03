/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelMain
import VOA.Classification.COne.SerreStarkFrickeBeta

/-!
# Gannon–Rayhaun Theorem 3.1 with the Serre–Stark level box discharged

`SerreStarkLevelBox24` is a theorem (`SSHecke.serreStarkLevelBox24`, by
Hecke's functional equation for θ-type forms, the resolvent of the `U(p²)` on the finite-dimensional
class-form space, the Dirichlet functional equation, uniqueness of Dirichlet coefficients, and the
mean-square bound `|c|² < p`). Serre–Stark enters only through `SerreStarkBoundedCoeff24`.
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion
  VOA.Huang.HuangTierReduced

universe u

/-- `SerreStarkSquareClass24` from bounded denominators alone. -/
theorem SSHecke.squareClass_of_boundedCoeff (hB : SSHecke.SerreStarkBoundedCoeff24) :
    SSHecke.SerreStarkSquareClass24 :=
  SSHecke.squareClass_of_boundedCoeff_of_levelBox hB SSHecke.serreStarkLevelBox24

/-- `ISerreStark24` (the needed case of Serre–Stark's Theorem A) from bounded denominators alone. -/
theorem SSHecke.iSerreStark24_of_boundedCoeff (hB : SSHecke.SerreStarkBoundedCoeff24) :
    ISerreStark24 :=
  SSHecke.iSerreStark24_of_boundedCoeff_of_levelBox hB SSHecke.serreStarkLevelBox24

/-- **Current strongest form, S5.** Serre–Stark enters only through
`SerreStarkBoundedCoeff24` (bounded denominators / q-expansion principle). -/
theorem gannonRayhaun_current_boundedCoeff
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hB : SSHecke.SerreStarkBoundedCoeff24)
    (hFib : SymmetricFiberFunctorExists.{0, 0}) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_levelBox hPBW hAM hV hC hG hB SSHecke.serreStarkLevelBox24 hFib hHK

end VOA.Classification.COne
