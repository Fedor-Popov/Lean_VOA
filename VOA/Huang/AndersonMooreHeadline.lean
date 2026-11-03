/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMooreMain
import VOA.Classification.COne.MainCurrent

/-!
# The Gannon–Rayhaun headline with the Anderson–Moore input discharged

`gannonRayhaun_latest` (`VOA/Classification/COne/MainCurrent.lean`) takes `AndersonMooreInput` as
a hypothesis; `andersonMooreInput_holds` proves it, so it drops out:

* `gannonRayhaun_latest_am : ZhuPBWBottomInput → HuangVerlindeFusionInput →
  DLNCongruenceInput → GaloisSymmetryNontrivialInput → SerreStarkBoundedCoeff24 →
  HuangHKLInterface → GannonRayhaunStatement`.

## Status
No `sorry`, no new axioms.  The remaining hypotheses are exactly those of `gannonRayhaun_latest`
other than `AndersonMooreInput`.
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion

universe u

/-- **`gannonRayhaun_latest` without the Anderson–Moore hypothesis.** -/
theorem gannonRayhaun_latest_am
    (hPBW : ZhuPBWBottomInput.{u})
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hB : SSHecke.SerreStarkBoundedCoeff24) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_latest hPBW andersonMooreInput_holds hV hC hG hB hHK

end VOA.Classification.COne
