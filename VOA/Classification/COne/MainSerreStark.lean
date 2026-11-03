/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainTannakian
import VOA.Classification.COne.SerreStarkIntegral
import VOA.Huang.ReconstructionFunctor

/-!
# Gannon–Rayhaun Theorem 3.1: current strongest form

The forward classification consumes Serre–Stark only at levels `24 ∣ N` (`ISerreStark24`). That
input is reduced (`SSHecke.iSerreStark24_of_boundedCoeff_of_squareClass`, Shimura's `T(p²)`,
eigenvalue lemma by integrality, no Jordan blocks) to two named consequences of Serre–Stark's
Theorem A (`boundedCoeff_of_theoremA`, `squareClass_of_theoremA`).
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion
  VOA.Huang.HuangTierReduced

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), with `ISerreStark24` explicit.** -/
theorem gannonRayhaun_current_ss24
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hSS : ISerreStark24) (hFib : SymmetricFiberFunctorExists.{0, 0})
    (hRec : FiberFunctorReconstruction.{0, 0}) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  let hMod := iModData_of_verlinde_inputs hPBW hAM (verlindeInput_of_fusion hV)
  gannonRayhaun_current_gauss hMod (iCongruenceGalois_of_split hC hG) hSS
    virC1RadicalLevelBound_holds
    (iTannakian_of_inputs (deligneTannakian_of_fiberFunctor hFib hRec) hHK)
    (heisCommutantTrivial_of_modData hMod) heisLatticeReconstruction

/-- **Current strongest form.** Serre–Stark replaced by its two Hecke-theoretic residuals
`SerreStarkBoundedCoeff24` (bounded denominators) and `SerreStarkSquareClass24` (level analysis of
square-class eigenforms), both proved to follow from Theorem A. -/
theorem gannonRayhaun_current_hecke
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hB : SSHecke.SerreStarkBoundedCoeff24) (hSq : SSHecke.SerreStarkSquareClass24)
    (hFib : SymmetricFiberFunctorExists.{0, 0})
    (hRec : FiberFunctorReconstruction.{0, 0}) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_ss24 hPBW hAM hV hC hG
    (SSHecke.iSerreStark24_of_boundedCoeff_of_squareClass hB hSq) hFib hRec hHK

/-- **Tannaka reconstruction discharged.** Tannaka reconstruction is proved
(`fiberFunctorReconstruction`, `VOA/Huang/Reconstruction*.lean`), so Deligne's theorem rests only on
the existence of a symmetric fiber functor (Deligne 1990 Thm 7.1). -/
theorem gannonRayhaun_current_recon
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hB : SSHecke.SerreStarkBoundedCoeff24) (hSq : SSHecke.SerreStarkSquareClass24)
    (hFib : SymmetricFiberFunctorExists.{0, 0}) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_hecke hPBW hAM hV hC hG hB hSq hFib fiberFunctorReconstruction hHK

end VOA.Classification.COne
