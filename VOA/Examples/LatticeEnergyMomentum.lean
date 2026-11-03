/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeTranslation
import VOA.Examples.HeisenbergNVOA
import VOA.Core.ReconstructionExistence

/-!
# The lattice reconstruction translation operator `Trec` and the boson covariance gate

The operator-first reconstruction theorem `Core.ReconstructionExistence.reconstruct` needs a
translation operator `T` with `T |0⟩ = 0` under which every generator field is covariant
(`DCovariant T f`, i.e. `[T, f(s)] = (s+1)·f(s+1)`).  Rather than route through the abstract
Sugawara `Ltrans = mode (sugField) 0`, we use the explicit closed form
`Trec = rTensor(L₋₁^Heis) + Mom`, where `Mom = ½·rTensor(α₋₁)·zGradeOp` is the momentum coupling
that the lattice zero mode `α₀ = zGradeOp` contributes.  This file proves:

* `Trec_vacuum : Trec latVacuum = 0`;
* `Trec_alphaLat_DCovariant : DCovariant Trec alphaLat` — the **boson generator covariance**,
  lifted from the Heisenberg `currentN_DCovariant` plus the `s=-2` momentum bracket.

All `pbw`-free / axiom-clean.  Algebra in `End ℂ LatModule` routes additive/subtractive identities
through `abel` and term-mode lemmas (the `Module.End`-instance keying defeats `rw`/`simp` on
`sub_mul`, `smul_add`, `sub_self`), and the multiplicative distribution through `noncomm_ring`.
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators

namespace VOA.LatExp

/-- Scaling a commutator: `[c•M, X] = c•[M, X]`. -/
theorem smul_bracket (c : ℂ) (M X : End ℂ LatModule) :
    (c • M) * X - X * (c • M) = c • (M * X - X * M) := by
  rw [smul_mul_assoc, mul_smul_comm]
  exact (smul_sub c (M * X) (X * M)).symm

/-- The lattice momentum operator `Mom = ½·rTensor(α₋₁)·zGradeOp`. -/
noncomputable def momOp : End ℂ LatModule :=
  (1 / 2 : ℂ) • ((LinearMap.rTensor LatGrp (α (-1))) * zGradeOp)

/-- The reconstruction translation operator `Trec = rTensor(LvirN 1 2 (-1)) + Mom` (the lattice
`L₋₁` with the momentum coupling). -/
noncomputable def Trec : End ℂ LatModule :=
  LinearMap.rTensor LatGrp (HeisenbergN.LvirN 1 2 (-1)) + momOp

/-- `Trec |0⟩ = 0`. -/
theorem Trec_vacuum : Trec latVacuum = 0 := by
  rw [Trec, LinearMap.add_apply]
  have h1 : LinearMap.rTensor LatGrp (HeisenbergN.LvirN 1 2 (-1)) latVacuum = 0 := by
    change LinearMap.rTensor LatGrp (HeisenbergN.LvirN 1 2 (-1))
      ((1 : HeisenbergN.FockN 1) ⊗ₜ[ℂ] eVec 0) = 0
    rw [LinearMap.rTensor_tmul,
      show HeisenbergN.LvirN 1 2 (-1) (1 : HeisenbergN.FockN 1) = 0 from
        HeisenbergN.LvirN_vacuum 1 2 (by norm_num : (-1 : ℤ) ≤ -1),
      TensorProduct.zero_tmul]
  have h2 : momOp latVacuum = 0 := by
    rw [momOp, LinearMap.smul_apply, Module.End.mul_apply, zGradeOp_vacuum, map_zero, smul_zero]
  rw [h1, h2, add_zero]

/-- The boson commutator of the lifted currents: `[rTensor(α(-1)), rTensor(α(-s-1))]
= (s=-2 ? -2 : 0)•id`. -/
theorem rTensor_alpha_comm (s : ℤ) :
    (LinearMap.rTensor LatGrp (α (-1))) * (LinearMap.rTensor LatGrp (α (-s - 1)))
      - (LinearMap.rTensor LatGrp (α (-s - 1))) * (LinearMap.rTensor LatGrp (α (-1)))
      = (if s = -2 then (-2 : ℂ) else 0) • (1 : End ℂ LatModule) := by
  rw [← rTensor_mul, ← rTensor_mul, ← LinearMap.rTensor_sub,
    show α (-1) * α (-s - 1) - α (-s - 1) * α (-1)
        = (if s = -2 then (-2 : ℂ) else 0) • LinearMap.id from by
      have h := HeisenbergN.oscN_comm 1 2 0 0 (-1) (-s - 1)
      rw [α, α, h]
      by_cases hs : s = -2
      · rw [if_pos (by exact ⟨rfl, by omega⟩), if_pos hs]; norm_num
      · rw [if_neg (by rintro ⟨_, h2⟩; omega), if_neg hs]]
  rw [LinearMap.rTensor_smul, LinearMap.rTensor_id]; rfl

/-- The momentum bracket: `[Mom, rTensor(αField s)] = (s=-2 ? -1 : 0)•zGradeOp`. -/
theorem momOp_comm_rTensor (s : ℤ) :
    momOp * (LinearMap.rTensor LatGrp (alphaField s))
      - (LinearMap.rTensor LatGrp (alphaField s)) * momOp
      = (if s = -2 then (-1 : ℂ) else 0) • zGradeOp := by
  set A := LinearMap.rTensor LatGrp (α (-1)) with hA
  set B := LinearMap.rTensor LatGrp (α (-s - 1)) with hB
  have hZB : zGradeOp * B = B * zGradeOp := zGradeOp_comm_rTensor (α (-s - 1))
  have hAB := rTensor_alpha_comm s
  rw [← hA, ← hB] at hAB
  have e1 : (A * zGradeOp) * B - B * (A * zGradeOp) = (A * B - B * A) * zGradeOp := by
    rw [mul_assoc, hZB, ← mul_assoc, ← mul_assoc]
    exact (sub_mul (A * B) (B * A) zGradeOp).symm
  have hbr : (A * zGradeOp) * B - B * (A * zGradeOp)
      = (if s = -2 then (-2 : ℂ) else 0) • zGradeOp := by
    rw [e1, hAB, smul_mul_assoc, one_mul]
  rw [alphaField_apply, ← hB, momOp, ← hA, smul_bracket, hbr, smul_smul]
  by_cases hs : s = -2
  · rw [if_pos hs, if_pos hs]; norm_num
  · rw [if_neg hs, if_neg hs, mul_zero, zero_smul]

/-- `[Mom, zGradeOp] = 0`. -/
theorem momOp_comm_zG : momOp * zGradeOp - zGradeOp * momOp = 0 := by
  have hcomm : Commute (LinearMap.rTensor LatGrp (α (-1)) * zGradeOp) zGradeOp :=
    (Commute.mul_left (zGradeOp_comm_rTensor (α (-1))).symm (Commute.refl zGradeOp))
  rw [momOp, smul_bracket, show (LinearMap.rTensor LatGrp (α (-1)) * zGradeOp) * zGradeOp
        - zGradeOp * (LinearMap.rTensor LatGrp (α (-1)) * zGradeOp) = 0 from
      sub_eq_zero_of_eq hcomm.eq, smul_zero]

/-- **The boson generator covariance** `DCovariant Trec alphaLat` (`[L₋₁, α(s)] = (s+1)•α(s+1)`):
the boson half lifts from `currentN_DCovariant`; the momentum bracket supplies the `s=-2` term. -/
theorem Trec_alphaLat_DCovariant : Reconstruction.DCovariant Trec alphaLat := by
  intro s
  change Trec * alphaLat s - alphaLat s * Trec = ((s + 1 : ℤ)) • alphaLat (s + 1)
  set L := LinearMap.rTensor LatGrp (HeisenbergN.LvirN 1 2 (-1)) with hLdef
  have hL : L * (LinearMap.rTensor LatGrp (alphaField s))
      - (LinearMap.rTensor LatGrp (alphaField s)) * L
      = ((s + 1 : ℤ)) • LinearMap.rTensor LatGrp (alphaField (s + 1)) := by
    have hc := HeisenbergN.currentN_DCovariant 1 2 (by norm_num : (2 : ℂ) ≠ 0) 0 s
    rw [hLdef, ← rTensor_mul, ← rTensor_mul, ← LinearMap.rTensor_sub,
      show HeisenbergN.LvirN 1 2 (-1) * alphaField s - alphaField s * HeisenbergN.LvirN 1 2 (-1)
          = ((s + 1 : ℤ)) • alphaField (s + 1) from hc,
      ← Int.cast_smul_eq_zsmul ℂ (s + 1) (alphaField (s + 1)),
      LinearMap.rTensor_smul]
    exact Int.cast_smul_eq_zsmul ℂ (s + 1) (LinearMap.rTensor LatGrp (alphaField (s + 1)))
  have hLc : L * (if s = -1 then zGradeOp else 0) - (if s = -1 then zGradeOp else 0) * L = 0 := by
    by_cases hs : s = -1
    · rw [if_pos hs, hLdef]
      exact sub_eq_zero_of_eq (zGradeOp_comm_rTensor (HeisenbergN.LvirN 1 2 (-1))).symm
    · rw [if_neg hs, mul_zero, zero_mul]; abel
  have hMc : momOp * (if s = -1 then zGradeOp else 0)
      - (if s = -1 then zGradeOp else 0) * momOp = 0 := by
    by_cases hs : s = -1
    · rw [if_pos hs]; exact momOp_comm_zG
    · rw [if_neg hs, mul_zero, zero_mul]; abel
  have hM := momOp_comm_rTensor s
  have key : Trec * alphaLat s - alphaLat s * Trec
      = ((s + 1 : ℤ)) • (LinearMap.rTensor LatGrp (alphaField (s + 1)))
        + (if s = -2 then (-1 : ℂ) else 0) • zGradeOp := by
    have expand : Trec * alphaLat s - alphaLat s * Trec
        = (L * (LinearMap.rTensor LatGrp (alphaField s))
            - (LinearMap.rTensor LatGrp (alphaField s)) * L)
          + (L * (if s = -1 then zGradeOp else 0) - (if s = -1 then zGradeOp else 0) * L)
          + (momOp * (LinearMap.rTensor LatGrp (alphaField s))
            - (LinearMap.rTensor LatGrp (alphaField s)) * momOp)
          + (momOp * (if s = -1 then zGradeOp else 0)
            - (if s = -1 then zGradeOp else 0) * momOp) := by
      rw [Trec, hLdef]
      change (LinearMap.rTensor LatGrp (HeisenbergN.LvirN 1 2 (-1)) + momOp)
            * (LinearMap.rTensor LatGrp (alphaField s) + (if s = -1 then zGradeOp else 0))
          - (LinearMap.rTensor LatGrp (alphaField s) + (if s = -1 then zGradeOp else 0))
            * (LinearMap.rTensor LatGrp (HeisenbergN.LvirN 1 2 (-1)) + momOp) = _
      noncomm_ring
    rw [expand, hL, hLc, hM, hMc]
    simp only [add_zero]
  rw [key]
  change ((s + 1 : ℤ)) • (LinearMap.rTensor LatGrp (alphaField (s + 1)))
      + (if s = -2 then (-1 : ℂ) else 0) • zGradeOp
    = ((s + 1 : ℤ)) • (LinearMap.rTensor LatGrp (alphaField (s + 1))
        + (if s + 1 = -1 then zGradeOp else 0))
  rw [show ((s + 1 : ℤ)) • (LinearMap.rTensor LatGrp (alphaField (s + 1))
          + (if s + 1 = -1 then zGradeOp else 0))
        = ((s + 1 : ℤ)) • (LinearMap.rTensor LatGrp (alphaField (s + 1)))
          + ((s + 1 : ℤ)) • (if s + 1 = -1 then zGradeOp else 0) from smul_add _ _ _]
  congr 1
  by_cases hs : s = -2
  · rw [if_pos hs, if_pos (by omega : s + 1 = -1), hs, show ((-2 : ℤ) + 1) = -1 from by ring]
    exact (neg_one_smul ℂ zGradeOp).trans (neg_one_smul ℤ zGradeOp).symm
  · rw [if_neg hs, if_neg (by omega : ¬ s + 1 = -1), zero_smul]
    exact (smul_zero _).symm

end VOA.LatExp
