/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainHuang
import VOA.Huang.HuangTierReduced

/-!
# Gannon–Rayhaun Theorem 3.1 with the Huang-tier inputs narrowed (H2)

`gannonRayhaun_current_huang` with

* `DLMRationalityInput` replaced by `AndersonMooreInput` (integral `q`-series with `S`-invariant
  span have rational exponents; no VOA content);
* `HuangSInput` replaced by `VerlindeInput` (Huang's Verlinde formula, eigenvalue form; `d_a ≥ 1`
  and Gannon's bound are proved);
* `ICongruenceGalois` replaced by `DLNCongruenceInput` and `GaloisSymmetryNontrivialInput`
  (the Galois cases `ℓ ≡ ±1` are proved from congruence).

Imported by the `VOA.Classification` umbrella.
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.HuangTierReduced

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), Huang tier narrowed.** `#print axioms`-clean,
conditional on `ZhuPBWBottomInput`, `AndersonMooreInput`, `VerlindeInput`, `DLNCongruenceInput`,
`GaloisSymmetryNontrivialInput`, Serre–Stark's Theorem A and `ITannakian`. -/
theorem gannonRayhaun_current_verlinde
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput) (hV : VerlindeInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hSS : SerreStarkTheoremA) (hTan : ITannakian.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_vir_free (iModData_of_verlinde_inputs hPBW hAM hV)
    (iCongruenceGalois_of_split hC hG) hSS hTan

/-- The same with the PBW datum supplied by the theorem `VOA.pbw`. -/
theorem gannonRayhaun_current_verlinde_pbw
    (hAM : AndersonMooreInput) (hV : VerlindeInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hSS : SerreStarkTheoremA) (hTan : ITannakian.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_verlinde zhuPBWBottomInput_of_pbw hAM hV hC hG hSS hTan

end VOA.Classification.COne
