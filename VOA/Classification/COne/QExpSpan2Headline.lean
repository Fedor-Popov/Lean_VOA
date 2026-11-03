/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpSpan2Frame
import VOA.Huang.HKLFrobDimMain

/-!
# Consequences of `QExpPrinciple24Away 2`

* `SSHecke.serreStarkBoundedCoeff24_holds`: Serre–Stark bounded coefficients, unconditionally;
* `gannonRayhaun_hkl_qexp`: the forward Gannon–Rayhaun headline with the q-expansion input
  discharged; it rests on `DLNCongruenceInput` and `GaloisSymmetryNontrivialInput` only.
-/

namespace VOA.Classification.COne

universe u

/-- Serre–Stark bounded coefficients (`24 ∣ N`), unconditionally. -/
theorem SSHecke.serreStarkBoundedCoeff24_holds : SSHecke.SerreStarkBoundedCoeff24 :=
  SSHecke.boundedCoeff24_of_qExpPrinciple24Away_two SSHecke.qExpPrinciple24Away_two

/-- **Gannon–Rayhaun Theorem 3.1 (forward)**, conditional only on `DLNCongruenceInput` and
`GaloisSymmetryNontrivialInput`. -/
theorem gannonRayhaun_hkl_qexp
    (hC : VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u})
    (hG : VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_hkl_final hC hG SSHecke.qExpPrinciple24Away_two

end VOA.Classification.COne
