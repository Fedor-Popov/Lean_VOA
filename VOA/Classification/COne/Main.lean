/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.GapsClassical
import VOA.Classification.COne.GapsPaper
import VOA.Classification.COne.ThetaGalois
import VOA.Classification.COne.AutV2Bridge
import VOA.Classification.COne.VirasoroCOne
import VOA.Classification.COne.FeiginFuchsCOne
import VOA.Classification.COne.WeilGalois
import VOA.Classification.COne.VirComposition
import VOA.Classification.COne.DongMasonCOne
import VOA.Classification.COne.WeilKernel
import VOA.Classification.COne.SerreStark
import VOA.Classification.COne.LatticeReconstruction
import VOA.Classification.COne.CommutantTrivial
import VOA.Classification.COne.FeiginFuchsLower

/-!
# The Gannon–Rayhaun classification of `c = 1` VOAs: the conditional forms

`gannonRayhaun_main` is the forward direction of Gannon–Rayhaun Theorem 3.1 (arXiv:2609.00122).
It is `#print axioms`-clean and **conditional on** exactly:

* the seven external inputs of `Inputs.lean` (`IModData`, `ICongruenceGalois`, `ISerreStark`,
  `IVirasoro`, `ITannakian`, `IDongMason`, `IEnumeration`), each a published theorem or a GR
  proposition assembled from published theorems;
* the classical `ThetaGaloisLaw` (GR Prop. 3.8, eq. (3.18); Shimura's theta multiplier).

The four internal gaps of `Conditional.lean` are discharged: `GapQExpansion` and
`GapThetaReduction` unconditionally (`GapsClassical.lean`), and `GapLemma37` and `GapGaloisBound`
from `ThetaGaloisLaw` (`GapsPaper.lean`).
-/

namespace VOA.Classification.COne

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward direction)**, conditional on the seven external
inputs and the classical theta Galois law. -/
theorem gannonRayhaun_main
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hVir : IVirasoro.{u}) (hTan : ITannakian.{u}) (hDM : IDongMason.{u})
    (hEn : IEnumeration) (hθ : ThetaGaloisLaw) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_of_inputs hMod hCG hSS hVir hTan hDM hEn
    (paperGaps_of_thetaGaloisLaw.{u} hθ).1 gapThetaReduction gapQExpansion
    (paperGaps_of_thetaGaloisLaw.{u} hθ).2

/-- **Gannon–Rayhaun Theorem 3.1 (forward)**, with the theta Galois law reduced to the finite,
purely algebraic `WeilGaloisLaw` (the Weil representation on `SL₂(ℤ/M)` and a quadratic Gauss
sum; `ThetaGalois.lean`). -/
theorem gannonRayhaun_main_weil
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hVir : IVirasoro.{u}) (hTan : ITannakian.{u}) (hDM : IDongMason.{u})
    (hEn : IEnumeration) (hW : WeilGaloisLaw) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_main hMod hCG hSS hVir hTan hDM hEn (thetaGaloisLaw_of_weilGaloisLaw hW)

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The enumeration input is
discharged (`iEnumeration`, `AutV2Bridge.lean`: finite subgroups of `Aut V₂` via `SO(3,ℂ)`, the
unitary trick and the classification of finite rotation groups; `Aut V_{2m}` for `m ≥ 2`).
Conditional on six external inputs and the finite `WeilGaloisLaw`. -/
theorem gannonRayhaun_current
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hVir : IVirasoro.{u}) (hTan : ITannakian.{u}) (hDM : IDongMason.{u})
    (hW : WeilGaloisLaw) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_main_weil hMod hCG hSS hVir hTan hDM iEnumeration hW

/-- **Gannon–Rayhaun Theorem 3.1 (forward), with `IVirasoro` refined** into the two narrower
published Virasoro facts of `VirasoroCOne.lean`: local composition series (Deodhar–Gabber–Kac) and
the `c = 1` degenerate characters (Feigin–Fuchs). The non-degenerate `c = 1` characters and the
Kac determinant are proved there. -/
theorem gannonRayhaun_current_vir
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hJH : VirLocalCompositionSeries.{u}) (hFF : VirC1DegenerateCharacters)
    (hTan : ITannakian.{u}) (hDM : IDongMason.{u}) (hW : WeilGaloisLaw) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current hMod hCG hSS (iVirasoro_of_composition hJH hFF) hTan hDM hW

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The Feigin–Fuchs input is
narrowed to the radical-dimension bound `VirC1RadicalLevelBound` (the upper bound on
`dim L(1, μ²)_n`, the level-`(2μ+1)` singular vector and the `m = 0` case are proved in
`FeiginFuchsCOne.lean`). -/
theorem gannonRayhaun_current_ff
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hJH : VirLocalCompositionSeries.{u}) (hRad : VirC1RadicalLevelBound)
    (hTan : ITannakian.{u}) (hDM : IDongMason.{u}) (hW : WeilGaloisLaw) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_vir hMod hCG hSS hJH (virC1DegenerateCharacters_iff.mpr hRad) hTan hDM hW

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The theta Galois law is
narrowed to `WeilKernelLaw`, the scalar congruence property "`Γ(M)` acts trivially on `Θ/η`"
(`WeilGalois.lean`); the Jacobi-symbol / quadratic Gauss-sum part is proved there
(`WeilGalois.gaussRatioLaw`). -/
theorem gannonRayhaun_current_kernel
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hJH : VirLocalCompositionSeries.{u}) (hRad : VirC1RadicalLevelBound)
    (hTan : ITannakian.{u}) (hDM : IDongMason.{u}) (hK : WeilGalois.WeilKernelLaw) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_ff hMod hCG hSS hJH hRad hTan hDM
    (WeilGalois.weilGaloisLaw_iff_weilKernelLaw.mpr hK)

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The local composition
series input is discharged (`virLocalCompositionSeries`, `VirComposition.lean`). Conditional on
five external inputs, the Feigin–Fuchs lower bound `VirC1RadicalLevelBound`, and the scalar
congruence law `WeilKernelLaw`. -/
theorem gannonRayhaun_current_best
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hRad : VirC1RadicalLevelBound) (hTan : ITannakian.{u}) (hDM : IDongMason.{u})
    (hK : WeilGalois.WeilKernelLaw) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_kernel hMod hCG hSS virLocalCompositionSeries hRad hTan hDM hK

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** `IDongMason` is refined
into DM-1 `HeisCommutantTrivial` (analytic: the Heisenberg commutant of a nice `c = 1` VOA is `ℂ𝟙`)
and DM-2 `HeisLatticeReconstruction` (algebraic: `ω = ½ h₍₋₁₎h` ⟹ `W ≅ V_{2m}`)
(`DongMasonCOne.lean`). -/
theorem gannonRayhaun_current_dm
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hRad : VirC1RadicalLevelBound) (hTan : ITannakian.{u})
    (hC : HeisCommutantTrivial.{u}) (hR : HeisLatticeReconstruction.{u})
    (hK : WeilGalois.WeilKernelLaw) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_best hMod hCG hSS hRad hTan (iDongMason_of_facts hC hR) hK

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The theta Galois law is
proved (`WeilGalois.weilKernelLaw`, with Gauss's sign theorem `WeilGalois.gaussG_one`;
`WeilKernel.lean`). Conditional on four Huang/Dong–Mason-tier inputs (`IModData`,
`ICongruenceGalois`, `ITannakian`, `HeisCommutantTrivial`), `ISerreStark`, the Feigin–Fuchs bound
`VirC1RadicalLevelBound` and the lattice reconstruction `HeisLatticeReconstruction`. -/
theorem gannonRayhaun_current_gauss
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : ISerreStark24)
    (hRad : VirC1RadicalLevelBound) (hTan : ITannakian.{u})
    (hC : HeisCommutantTrivial.{u}) (hR : HeisLatticeReconstruction.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_dm hMod hCG hSS hRad hTan hC hR WeilGalois.weilKernelLaw

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The Serre–Stark input is
the published statement, Theorem A of Serre–Stark (LNM 627) in character form; the passage to
the residue-class form (θ² law on `Γ₁(N)`, weight-one bridge) is proved in `SerreStark.lean`. -/
theorem gannonRayhaun_current_ssA
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : SerreStarkTheoremA)
    (hRad : VirC1RadicalLevelBound) (hTan : ITannakian.{u})
    (hC : HeisCommutantTrivial.{u}) (hR : HeisLatticeReconstruction.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_gauss hMod hCG (iSerreStark24_of_iSerreStark (iSerreStark_of_theoremA hSS)) hRad hTan hC hR

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The Dong–Mason lattice
reconstruction (DM-2) is proved (`heisLatticeReconstruction`, `LatticeReconstruction.lean`).
Conditional on: `IModData`, `ICongruenceGalois`, `ITannakian`, `HeisCommutantTrivial` (DM-1),
Serre–Stark's Theorem A, and the Feigin–Fuchs bound `VirC1RadicalLevelBound`. -/
theorem gannonRayhaun_current_dm2
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : SerreStarkTheoremA)
    (hRad : VirC1RadicalLevelBound) (hTan : ITannakian.{u})
    (hC : HeisCommutantTrivial.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_ssA hMod hCG hSS hRad hTan hC heisLatticeReconstruction

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The Dong–Mason input is
discharged: DM-1 follows from `IModData` by the effective-central-charge argument
(`heisCommutantTrivial_of_modData`, `CommutantTrivial.lean`) and DM-2 is unconditional. Conditional
on exactly: the three Huang-tier inputs `IModData`, `ICongruenceGalois`, `ITannakian`; Serre–Stark's
published Theorem A; and the Feigin–Fuchs bound `VirC1RadicalLevelBound`. -/
theorem gannonRayhaun_current_final
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : SerreStarkTheoremA)
    (hRad : VirC1RadicalLevelBound) (hTan : ITannakian.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_dm2 hMod hCG hSS hRad hTan (heisCommutantTrivial_of_modData hMod)

/-- **Gannon–Rayhaun Theorem 3.1 (forward).** The Feigin–Fuchs bound
is proved (`virC1RadicalLevelBound_holds`, `FeiginFuchsLower.lean`), so every `c = 1` Virasoro input
is discharged. Conditional on exactly: the three Huang-tier inputs `IModData`, `ICongruenceGalois`,
`ITannakian`, and Serre–Stark's published Theorem A. -/
theorem gannonRayhaun_current_vir_free
    (hMod : IModData.{u}) (hCG : ICongruenceGalois.{u}) (hSS : SerreStarkTheoremA)
    (hTan : ITannakian.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_final hMod hCG hSS virC1RadicalLevelBound_holds hTan

end VOA.Classification.COne
