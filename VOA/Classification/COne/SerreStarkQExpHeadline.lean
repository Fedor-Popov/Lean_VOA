/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainCurrent
import VOA.Classification.COne.SerreStarkQExp

/-!
# Gannon–Rayhaun Theorem 3.1 (forward) with the Serre–Stark residual replaced by the standard
integral-weight `q`-expansion principle

`gannonRayhaun_latest` needs `SSHecke.SerreStarkBoundedCoeff24`; by
`SSHecke.boundedCoeff24_of_qExpPrinciple24` it follows from the `q`-expansion principle with
bounded denominators for `M_k(Γ₁(N))` in any single weight `k ≥ 1` (`SSHecke.QExpPrinciple24`).
We record the weight-two form (Shimura, Thm 3.52, plus the Eisenstein basis), the most
classical one.
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward)**, with the last Serre–Stark input stated as the
standard weight-two `q`-expansion principle for `Γ₁(N)` (`24 ∣ N`). `#print axioms`-clean,
conditional on: `ZhuPBWBottomInput` (⇐ the theorem `VOA.pbw`),
`AndersonMooreInput`, `HuangVerlindeFusionInput`, `DLNCongruenceInput`,
`GaloisSymmetryNontrivialInput`, `SSHecke.QExpPrinciple24 2`, `HuangHKLInterface`. -/
theorem gannonRayhaun_qExp
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24 2) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_latest hPBW hAM hV hC hG (SSHecke.boundedCoeff24_of_qExpPrinciple24_two hQ) hHK

end VOA.Classification.COne
