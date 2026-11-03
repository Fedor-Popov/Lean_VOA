/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMooreHeadline
import VOA.Classification.COne.SerreStarkQExpAway

/-!
# Gannon–Rayhaun Theorem 3.1 (forward) with the Serre–Stark input weakened to the `q`-expansion
principle away from the tower primes (S7)

`gannonRayhaun_latest_am` needs `SSHecke.SerreStarkBoundedCoeff24`. By
`SSHecke.boundedCoeff24_of_away` it follows from the weaker `SSHecke.SerreStarkBoundedCoeffAway24`
(no control at the primes dividing the level), and by
`SSHecke.boundedCoeff24_of_qExpPrinciple24Away` from the integral-weight `q`-expansion principle
away from each `p ∤ N` (`SSHecke.QExpPrinciple24Away`, Katz over `ℤ[1/N]`).
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward)**, Serre–Stark input = bounded coefficients away
from the tower primes. `#print axioms`-clean, conditional on: `ZhuPBWBottomInput`,
`HuangVerlindeFusionInput`, `DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`,
`SSHecke.SerreStarkBoundedCoeffAway24`, `HuangHKLInterface`. -/
theorem gannonRayhaun_latest_away
    (hPBW : ZhuPBWBottomInput.{u})
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hB : SSHecke.SerreStarkBoundedCoeffAway24) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_latest_am hPBW hV hC hG (SSHecke.boundedCoeff24_of_away hB) hHK

/-- **Gannon–Rayhaun Theorem 3.1 (forward)**, Serre–Stark input = the weight-two
`q`-expansion principle for `Γ₁(N)` away from each `p ∤ N` (`SSHecke.QExpPrinciple24Away 2`). -/
theorem gannonRayhaun_qExpAway
    (hPBW : ZhuPBWBottomInput.{u})
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_latest_am hPBW hV hC hG (SSHecke.boundedCoeff24_of_qExpPrinciple24Away_two hQ) hHK

end VOA.Classification.COne
