/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLLocMain
import VOA.Huang.HKLExtCFT

/-!
# `HKLLocalityInput` holds; Gannon–Rayhaun with HKL reduced to `HKLNiceInput`

`hklLocalityInput_holds : HKLLocalityInput` — the commutative-monoid axioms of `A` in the
braided category `Ordinary V` (`IsCommMonObj.mul_comm`, `MonObj.mul_assoc`, whose whiskerings and
associator are the library's `tensorHom` and analytic `evalAssoc`) are exactly the hypotheses
`hcomm`, `hassoc` of `local_extField`.

`VOA.Classification.COne.gannonRayhaun_hkl_nice (hC hG hQ hN)` — the forward Gannon–Rayhaun
theorem, conditional on `DLNCongruenceInput`, `GaloisSymmetryNontrivialInput`,
`QExpPrinciple24Away 2` and the single HKL input `HKLNiceInput`.

No `sorry`, no new axioms.
-/

noncomputable section

namespace VOA.Huang.HKLLoc

open CategoryTheory MonoidalCategory
open VOA VOA.Huang.TensorCat VOA.Huang.HKLExt

universe u

/-- **HKL 2015 Thm 3.2 (locality) holds**: the extension vertex operator of a commutative
monoid with trivial twist in the braided category of ordinary modules of a nice VOA is local. -/
theorem hklLocalityInput_holds : HKLLocalityInput.{u} := by
  intro 𝒱 _ _ V hV F
  letI := monoidalCategoryOfStronglyRational_pbw F hV.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hV.1
  intro A _ hcomm htw a b
  exact local_extField hV.1 htw (IsCommMonObj.mul_comm A) (MonObj.mul_assoc A) a b

end VOA.Huang.HKLLoc

namespace VOA.Classification.COne

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward) with HKL reduced to `HKLNiceInput`.** -/
theorem gannonRayhaun_hkl_nice
    (hC : VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u})
    (hG : VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2) (hN : VOA.Huang.HKLExt.HKLNiceInput.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_hkl_two hC hG hQ VOA.Huang.HKLLoc.hklLocalityInput_holds hN

end VOA.Classification.COne
