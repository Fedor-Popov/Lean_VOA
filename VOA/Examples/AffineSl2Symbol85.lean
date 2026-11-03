/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2Symbol
import VOA.Examples.AffineSl2Singular85
import VOA.Modules.PoissonQuotient

/-!
# The `C₂` symbol of the weight-five singular vector at `k = -8/5`

This file is the `p = 5` counterpart of `Examples.AffineSl2Symbol`.  It computes the image of the
explicit twenty-one-term vector `Sl2Sing85.sl2Singular85` in the `C₂` algebra of the universal
affine vertex algebra.  The eighteen monomials containing a current mode of index at most `-2`
vanish.  The three pure mode-`-1` monomials give

```text
[sl2Singular85] = 625 e h^4 + 5000 e^2 f h^2 + 10000 e^3 f^2
                  = 625 e (h^2 + 4 e f)^2.
```

The result is an identity in the quotient `A₂(V^{-8/5}(sl₂))`; it does not assert that the class
is nonzero, identify the full `C₂` algebra of the simple quotient, or prove classical freeness.

## Main results

* `mk₂_sl2Singular85_expanded` computes the three surviving monomials.
* `mk₂_sl2Singular85_casimir_sq` proves the exact factorization `625 e Omega^2`.

Both statements are independent of a PBW basis.
-/

namespace VOA.Sl2Symbol85

open VOA
open VOA.AffineVOA
open VOA.AffineVOA.Inst
open VOA.Sl2Sing85
open VOA.Sl2Symbol
open VertexOperatorAlgebra

/-! ## The level and its current classes -/

theorem level85_noncritical : (-8 / 5 : ℂ) + 2 ≠ 0 := by norm_num

noncomputable abbrev W85 : VertexOperatorAlgebra (WakModule (-8 / 5 : ℂ)) :=
  affineSl2VOA_closed (-8 / 5 : ℂ) level85_noncritical

noncomputable abbrev e85 : A₂ W85 := eCl (-8 / 5 : ℂ) level85_noncritical
noncomputable abbrev f85 : A₂ W85 := fCl (-8 / 5 : ℂ) level85_noncritical
noncomputable abbrev h85 : A₂ W85 := hCl (-8 / 5 : ℂ) level85_noncritical
noncomputable abbrev casimir85 : A₂ W85 := casimirCl (-8 / 5 : ℂ) level85_noncritical

/-! ## The three pure mode-minus-one monomials -/

theorem N01_eq_poissonMul :
    N01 (-8 / 5 : ℂ) =
      poissonMul W85 (currentState (-8 / 5 : ℂ) colE)
        (poissonMul W85 (currentState (-8 / 5 : ℂ) colH)
          (poissonMul W85 (currentState (-8 / 5 : ℂ) colH)
            (poissonMul W85 (currentState (-8 / 5 : ℂ) colH)
              (currentState (-8 / 5 : ℂ) colH)))) := by
  simp only [poissonMul_def, smul_currentState_eq_J]
  simp only [currentState_def, N01_eq]

theorem N02_eq_poissonMul :
    N02 (-8 / 5 : ℂ) =
      poissonMul W85 (currentState (-8 / 5 : ℂ) colE)
        (poissonMul W85 (currentState (-8 / 5 : ℂ) colE)
          (poissonMul W85 (currentState (-8 / 5 : ℂ) colF)
            (poissonMul W85 (currentState (-8 / 5 : ℂ) colH)
              (currentState (-8 / 5 : ℂ) colH)))) := by
  simp only [poissonMul_def, smul_currentState_eq_J]
  simp only [currentState_def, N02_eq]

theorem N03_eq_poissonMul :
    N03 (-8 / 5 : ℂ) =
      poissonMul W85 (currentState (-8 / 5 : ℂ) colE)
        (poissonMul W85 (currentState (-8 / 5 : ℂ) colE)
          (poissonMul W85 (currentState (-8 / 5 : ℂ) colE)
            (poissonMul W85 (currentState (-8 / 5 : ℂ) colF)
              (currentState (-8 / 5 : ℂ) colF)))) := by
  simp only [poissonMul_def, smul_currentState_eq_J]
  simp only [currentState_def, N03_eq]

theorem mk₂_N01 : mk₂ W85 (N01 (-8 / 5 : ℂ)) = e85 * (h85 * (h85 * (h85 * h85))) := by
  rw [e85, h85, eCl, hCl, A₂_mul_mk, A₂_mul_mk, A₂_mul_mk, A₂_mul_mk,
    N01_eq_poissonMul]

theorem mk₂_N02 : mk₂ W85 (N02 (-8 / 5 : ℂ)) = e85 * (e85 * (f85 * (h85 * h85))) := by
  rw [e85, f85, h85, eCl, fCl, hCl, A₂_mul_mk, A₂_mul_mk, A₂_mul_mk, A₂_mul_mk,
    N02_eq_poissonMul]

theorem mk₂_N03 : mk₂ W85 (N03 (-8 / 5 : ℂ)) = e85 * (e85 * (e85 * (f85 * f85))) := by
  rw [e85, f85, eCl, fCl, A₂_mul_mk, A₂_mul_mk, A₂_mul_mk, A₂_mul_mk,
    N03_eq_poissonMul]

/-! ## Every remaining monomial dies in `C₂` -/

theorem mk₂_N04 : mk₂ W85 (N04 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N04_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colH (by norm_num) _)

theorem mk₂_N05 : mk₂ W85 (N05 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N05_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colH (by norm_num) _)

theorem mk₂_N06 : mk₂ W85 (N06 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N06_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colH (by norm_num) _)

theorem mk₂_N07 : mk₂ W85 (N07 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N07_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colF (by norm_num) _)

theorem mk₂_N08 : mk₂ W85 (N08 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N08_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N09 : mk₂ W85 (N09 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N09_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N10 : mk₂ W85 (N10 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N10_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N11 : mk₂ W85 (N11 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N11_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N12 : mk₂ W85 (N12 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N12_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N13 : mk₂ W85 (N13 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N13_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colH (by norm_num) _)

theorem mk₂_N14 : mk₂ W85 (N14 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N14_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colH (by norm_num) _)

theorem mk₂_N15 : mk₂ W85 (N15 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N15_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colF (by norm_num) _)

theorem mk₂_N16 : mk₂ W85 (N16 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N16_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N17 : mk₂ W85 (N17 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N17_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N18 : mk₂ W85 (N18 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N18_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N19 : mk₂ W85 (N19 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N19_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colH (by norm_num) _)

theorem mk₂_N20 : mk₂ W85 (N20 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N20_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

theorem mk₂_N21 : mk₂ W85 (N21 (-8 / 5 : ℂ)) = 0 := (mk₂_eq_zero_iff W85).mpr (by
  rw [N21_eq]
  exact J_mem_O₂ (-8 / 5 : ℂ) level85_noncritical colE (by norm_num) _)

/-! ## The exact symbol and its Casimir factorization -/

theorem mk₂_sl2Singular85_expanded :
    mk₂ W85 sl2Singular85 =
      (625 : ℂ) • (e85 * (h85 * (h85 * (h85 * h85))))
        + (5000 : ℂ) • (e85 * (e85 * (f85 * (h85 * h85))))
        + (10000 : ℂ) • (e85 * (e85 * (e85 * (f85 * f85))) ) := by
  rw [sl2Singular85_def]
  simp only [map_add, map_smul, mk₂_N01, mk₂_N02, mk₂_N03, mk₂_N04, mk₂_N05,
    mk₂_N06, mk₂_N07, mk₂_N08, mk₂_N09, mk₂_N10, mk₂_N11, mk₂_N12, mk₂_N13,
    mk₂_N14, mk₂_N15, mk₂_N16, mk₂_N17, mk₂_N18, mk₂_N19, mk₂_N20, mk₂_N21,
    smul_zero, add_zero]

theorem mk₂_sl2Singular85_casimir_sq :
    mk₂ W85 sl2Singular85 = (625 : ℂ) • (e85 * casimir85 ^ 2) := by
  rw [mk₂_sl2Singular85_expanded]
  change _ = (625 : ℂ) •
    (e85 * (((4 : ℂ) • (e85 * f85) + h85 * h85) ^ 2))
  simp only [Algebra.smul_def]
  simp only [map_ofNat]
  ring

end VOA.Sl2Symbol85

section AxiomAudit
#print axioms VOA.Sl2Symbol85.mk₂_sl2Singular85_expanded
#print axioms VOA.Sl2Symbol85.mk₂_sl2Singular85_casimir_sq
end AxiomAudit
