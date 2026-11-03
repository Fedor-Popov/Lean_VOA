/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Main
import VOA.Huang.IModDataReduced

/-!
# Gannon–Rayhaun Theorem 3.1 with `IModData` reduced

`IModData` is replaced by the reduction `VOA.Huang.IModDataReduced.iModData_of_reduced_inputs`:
Zhu's correspondence, finiteness of the irreducibles, convergence of characters, Zhu's
`S`-transformation law and the reality/positivity of the vacuum column are proved; what remains is

* `ZhuPBWBottomInput` (the PBW bottom projection of the regular `A(V)`-module; it follows from the
  theorem `VOA.pbw`, see `gannonRayhaun_current_huang_pbw`);
* `DLMRationalityInput` (`c` and `h_a` rational: Dong–Li–Mason 2000, Thm 11.3);
* `HuangSInput` (`S₀₀ ≠ 0`, symmetric vacuum row, `d_a ≥ 1`, Gannon's bound: Huang 2008, ENO 2005,
  Gannon 2005).
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.IModDataReduced

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), `IModData` reduced.** `#print axioms`-clean,
conditional on `ZhuPBWBottomInput`, `DLMRationalityInput`, `HuangSInput`, `ICongruenceGalois`,
Serre–Stark's Theorem A and `ITannakian`. -/
theorem gannonRayhaun_current_huang
    (hPBW : ZhuPBWBottomInput.{u}) (hRat : DLMRationalityInput.{u})
    (hS : HuangSInput.{u, u + 1}) (hCG : ICongruenceGalois.{u}) (hSS : SerreStarkTheoremA)
    (hTan : ITannakian.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_vir_free (iModData_of_reduced_inputs hPBW hRat hS) hCG hSS hTan

/-- The same with the PBW datum supplied by the theorem `VOA.pbw`. -/
theorem gannonRayhaun_current_huang_pbw
    (hRat : DLMRationalityInput.{u}) (hS : HuangSInput.{u, u + 1})
    (hCG : ICongruenceGalois.{u}) (hSS : SerreStarkTheoremA) (hTan : ITannakian.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_vir_free (iModData_of_reduced_pbw_inputs hRat hS) hCG hSS hTan

end VOA.Classification.COne
