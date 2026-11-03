/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkLevelMain
import VOA.Huang.DeligneFiberMain

/-!
# Gannon–Rayhaun Theorem 3.1 with Deligne's theorem discharged

Deligne's theorem on symmetric fusion categories with positive dimensions
(`VOA.Huang.TensorCat.DeligneFiber.deligneTannakian_holds`, via the fiber functor
`symmetricFiberFunctorExists_holds` and Tannaka reconstruction `fiberFunctorReconstruction`) is
proved, so the Tannakian half of GR Prop. 2.17 / 2.13 rests only on `HuangHKLInterface`.
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), current strongest form.** `#print axioms`-clean,
conditional on: `ZhuPBWBottomInput` (⇐ `VOA.pbw`), `AndersonMooreInput`, `HuangVerlindeFusionInput`,
`DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`, the two Serre–Stark residuals
`SerreStarkBoundedCoeff24`, `SerreStarkLevelBox24` (both ⇐ Serre–Stark Thm A), and
`HuangHKLInterface`. -/
theorem gannonRayhaun_current_deligne
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hB : SSHecke.SerreStarkBoundedCoeff24) (hL : SSHecke.SerreStarkLevelBox24)
    (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_levelBox hPBW hAM hV hC hG hB hL
    DeligneFiber.symmetricFiberFunctorExists_holds hHK

end VOA.Classification.COne
