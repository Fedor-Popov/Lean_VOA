/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtFixed
import VOA.Huang.HKLExtHeadline

/-!
# Gannon–Rayhaun Theorem 3.1 (forward) with HKL reduced to three named inputs

`gannonRayhaun_hkl` — the forward classification, conditional on `DLNCongruenceInput`,
`GaloisSymmetryNontrivialInput`, `QExpPrinciple24Away 2` and the three HKL inputs
`HKLLocalityInput` (HKL Thm 3.2's analytic core), `HKLCFTTypeInput` (CFT type of a haploid
algebra), `HKLNiceInput` (KO/HKL/CKM/GR Prop. 2.7).  Everything else on the extension side — the
vertex operator algebra `extVOA` on the algebra object, the automorphism action, `V ≅ W^Γ`, the
graded dimensions, the transport from a pinned realization, and the Frobenius property of the
regular algebra — is proved.

No `sorry`, no new axioms.
-/

namespace VOA.Classification.COne

universe u

/-- **Gannon–Rayhaun Theorem 3.1 (forward), HKL reduced to its three analytic/representation
theoretic cores.** -/
theorem gannonRayhaun_hkl
    (hC : VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u})
    (hG : VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u})
    (hQ : SSHecke.QExpPrinciple24Away 2)
    (hL : VOA.Huang.HKLExt.HKLLocalityInput.{u}) (hCFT : VOA.Huang.HKLExt.HKLCFTTypeInput.{u})
    (hN : VOA.Huang.HKLExt.HKLNiceInput.{u}) :
    GannonRayhaunStatement.{u} :=
  gannonRayhaun_huang_rigid hC hG hQ
    (VOA.Huang.HKLExt.hklRepInputRigid_of_ordinary
      (VOA.Huang.HKLExt.hklOrdinaryInput_of_inputs hL hCFT hN))

end VOA.Classification.COne
