/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.MainVerlinde
import VOA.Huang.TannakianInterface
import VOA.Huang.VerlindeFusion
import VOA.Huang.DeligneReduction

/-!
# Gannon–Rayhaun Theorem 3.1 with `ITannakian` assembled

`ITannakian` is replaced by `VOA.Huang.Tannakian.iTannakian_of_inputs`: the categorical half of
GR Prop. 2.17 (Müger's criterion, the trivial-twist part is a symmetric fusion category, the regular
algebra `Fun(G)` with its left-translation action and `Fun(G)^G = 𝟙`) is proved; what remains is
Deligne's theorem (`DeligneTannakian`) and the combined Huang–HKL interface (`HuangHKLInterface`:
a ribbon realization of the modular data of `V` in which commutative haploid trivial-twist algebras
give nice VOA extensions, Huang 2008 + Huang–Kirillov–Lepowsky 2015 + GR Prop. 2.7).
-/

namespace VOA.Classification.COne

open VOA.Huang.ZhuModData VOA.Huang.AndersonMoore VOA.Huang.VerlindeReduction
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.Tannakian VOA.Huang.TensorCat VOA.Huang.VerlindeFusion

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), current strongest form.** `#print axioms`-clean,
conditional on: `ZhuPBWBottomInput`, `AndersonMooreInput`, `VerlindeInput`, `DLNCongruenceInput`,
`GaloisSymmetryNontrivialInput`, Serre–Stark's Theorem A, `DeligneTannakian`, `HuangHKLInterface`. -/
theorem gannonRayhaun_current_tannakian
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput) (hV : VerlindeInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hSS : SerreStarkTheoremA) (hDel : DeligneTannakian.{0, 0})
    (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_verlinde hPBW hAM hV hC hG hSS (iTannakian_of_inputs hDel hHK)

/-- The same with the PBW datum supplied by the theorem `VOA.pbw`. -/
theorem gannonRayhaun_current_tannakian_pbw
    (hAM : AndersonMooreInput) (hV : VerlindeInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hSS : SerreStarkTheoremA) (hDel : DeligneTannakian.{0, 0})
    (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_verlinde_pbw hAM hV hC hG hSS (iTannakian_of_inputs hDel hHK)

/-- The same, with `VerlindeInput` sharpened to `HuangVerlindeFusionInput` (Huang 2008: the
Verlinde formula with `N_ab^c` the library's own fusion rules, `dim` of the space of intertwining
operators; `verlindeInput_of_fusion`). -/
theorem gannonRayhaun_current_fusion
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hSS : SerreStarkTheoremA) (hDel : DeligneTannakian.{0, 0})
    (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_tannakian hPBW hAM (verlindeInput_of_fusion hV) hC hG hSS hDel hHK

/-- **Current strongest form.** Deligne's theorem split as `SymmetricFiberFunctorExists`
(Deligne 1990 Thm 7.1 / EGNO §9.9; its categorical inputs `Λ^{d+1} X = 0` and `det X` invertible are
proved in `DeligneIntegral`/`DeligneDeterminant`) and `FiberFunctorReconstruction`
(Deligne–Milne Thm 2.11, finite semisimple symmetric case). -/
theorem gannonRayhaun_current_fiber
    (hPBW : ZhuPBWBottomInput.{u}) (hAM : AndersonMooreInput)
    (hV : HuangVerlindeFusionInput.{u, u + 1})
    (hC : DLNCongruenceInput.{u}) (hG : GaloisSymmetryNontrivialInput.{u})
    (hSS : SerreStarkTheoremA) (hFib : SymmetricFiberFunctorExists.{0, 0})
    (hRec : FiberFunctorReconstruction.{0, 0}) (hHK : HuangHKLInterface.{u, 0, 0}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_current_fusion hPBW hAM hV hC hG hSS (deligneTannakian_of_fiberFunctor hFib hRec) hHK

end VOA.Classification.COne
