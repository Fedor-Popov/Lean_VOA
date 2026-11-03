/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMoore
import VOA.Huang.VerlindeReduction
import VOA.Huang.CongruenceGaloisSplit

/-!
# `IModData` from the narrowed Huang-tier inputs

Assembly of `Huang/AndersonMoore.lean` and `Huang/VerlindeReduction.lean`:

* `DLMRationalityInput` ⟸ `ZhuPBWBottomInput` + `AndersonMooreInput` (a statement about integral
  `q`-series only);
* `HuangSInput` ⟸ `DLMRationalityInput` + `VerlindeInput` (`d_a ≥ 1` and Gannon's bound proved).

## Main results

* `iModData_of_verlinde_inputs` : `ZhuPBWBottomInput → AndersonMooreInput → VerlindeInput →
  IModData`;
* `iModData_of_verlinde_pbw_inputs` : the PBW datum from `VOA.pbw`.
-/

namespace VOA.Huang.HuangTierReduced

open VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.IModDataReduced
  VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction

universe u

/-- `HuangSInput` from the Anderson–Moore and Verlinde inputs (and the PBW datum). -/
theorem huangSInput_of_am_verlinde (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : VerlindeInput.{u, u + 1}) : HuangSInput.{u, u + 1} :=
  huangSInput_of_verlinde (dlmRationalityInput_of_andersonMoore hPBW hAM) hV

/-- **`IModData` from the PBW datum, Anderson–Moore and Huang's Verlinde theorem.** -/
theorem iModData_of_verlinde_inputs (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : VerlindeInput.{u, u + 1}) : IModData.{u} :=
  iModData_of_reduced_inputs hPBW (dlmRationalityInput_of_andersonMoore hPBW hAM)
    (huangSInput_of_am_verlinde hPBW hAM hV)

/-- The same with the PBW datum supplied by the theorem `VOA.pbw`. -/
theorem iModData_of_verlinde_pbw_inputs (hAM : AndersonMooreInput)
    (hV : VerlindeInput.{u, u + 1}) : IModData.{u} :=
  iModData_of_verlinde_inputs zhuPBWBottomInput_of_pbw hAM hV

end VOA.Huang.HuangTierReduced
