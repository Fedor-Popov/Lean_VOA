/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainDeligne
import VOA.Classification.COne.SerreStarkLevelBoxHeadline

/-!
# Gannon–Rayhaun Theorem 3.1 (forward): the current strongest form

Proved since the conditional statement `gannonRayhaun_of_inputs`: Deligne's theorem
(`deligneTannakian_holds`) and Serre–Stark's level analysis (`SSHecke.serreStarkLevelBox24`).
The only Serre–Stark residual is `SerreStarkBoundedCoeff24` (bounded denominators; proved to follow
from Theorem A by `boundedCoeff_of_theoremA`).
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** `#print axioms`-clean,
conditional on: `ZhuPBWBottomInput` (⇐ the theorem `VOA.pbw`),
`AndersonMooreInput`, `HuangVerlindeFusionInput`, `DLNCongruenceInput`,
`GaloisSymmetryNontrivialInput`, `SerreStarkBoundedCoeff24`, `HuangHKLInterface`. -/
theorem gannonRayhaun_latest
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hB : SSHecke.SerreStarkBoundedCoeff24) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_deligne hPBW hAM hV hC hG hB SSHecke.serreStarkLevelBox24 hHK

end VOA.Classification.COne
