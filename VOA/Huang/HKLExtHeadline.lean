/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtRigid
import VOA.Classification.COne.MainHuangProved

/-!
# Gannon–Rayhaun Theorem 3.1 (forward) from the REPAIRED HKL input

`gannonRayhaun_huang` is conditional on `HKLRepInput`, which is false as stated (square-zero
extensions; `VOA/Huang/HKLExtRigid.lean`).  This file re-routes the same proof through the repaired
input `HKLRepInputRigid` (HKL for nondegenerate/Frobenius algebras, which is all the Tannakian step
uses):

* `gannonRayhaun_of_iTannakian` — the forward theorem from `ITannakian` and the three remaining
  non-Huang inputs; it is the chain `gannonRayhaun_huang → … → gannonRayhaun_current_ss24` with
  every proved input filled in and the single `iTannakian_of_inputs` step left open;
* `gannonRayhaun_huang_rigid` — conditional on `DLNCongruenceInput`,
  `GaloisSymmetryNontrivialInput`, `QExpPrinciple24Away 2` and `HKLRepInputRigid`.

No `sorry`, no new axioms.
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion
  VOA.Huang.HuangTierReduced

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward) from `ITannakian`**, with every other Huang-side input
proved (`zhuPBWBottomInput_of_pbw`, `andersonMooreInput_holds`, `fusionEigenInput_holds`,
`rhoNegOneInput_pbw`) and Serre–Stark reduced to `QExpPrinciple24Away 2`. -/
theorem gannonRayhaun_of_iTannakian
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2) (hT : ITannakian.{u}) :
    GannonRayhaunStatement.{u} :=
  let hV := VOA.Huang.VerlindeVacuum.huangVerlindeFusionInput_of_eigen_rho
    VOA.Huang.GenusOneG1f.fusionEigenInput_holds VOA.Huang.VerlindeRho.rhoNegOneInput_pbw
  let hB := SSHecke.boundedCoeff24_of_qExpPrinciple24Away_two hQ
  let hSS := SSHecke.iSerreStark24_of_boundedCoeff_of_squareClass hB
    (SSHecke.squareClass_of_boundedCoeff_of_levelBox hB SSHecke.serreStarkLevelBox24)
  let hMod := iModData_of_verlinde_inputs zhuPBWBottomInput_of_pbw andersonMooreInput_holds
    (verlindeInput_of_fusion hV)
  gannonRayhaun_current_gauss hMod (iCongruenceGalois_of_split hC hG) hSS
    virC1RadicalLevelBound_holds hT (heisCommutantTrivial_of_modData hMod)
    heisLatticeReconstruction

/-- **Gannon–Rayhaun Theorem 3.1 (forward) from the repaired HKL input.**  Conditional on
`DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`, `QExpPrinciple24Away 2` and
`HKLRepInputRigid` (HKL 2015 + KO 2002 for Frobenius algebras on `Rep V`); Deligne's theorem
(`symmetricFiberFunctorExists_holds`, `fiberFunctorReconstruction`) and all of Huang's theory
(`huangRepInput_holds`) are discharged. -/
theorem gannonRayhaun_huang_rigid
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2)
    (hR : VOA.Huang.HKLExt.HKLRepInputRigid.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_of_iTannakian hC hG hQ
    (VOA.Huang.HKLExt.iTannakian_of_rigid
      (deligneTannakian_of_fiberFunctor DeligneFiber.symmetricFiberFunctorExists_holds
        fiberFunctorReconstruction)
      (VOA.Huang.HKLExt.huangHKLInterfaceRigid_of_hklRepRigid hR))

end VOA.Classification.COne
