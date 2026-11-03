/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeChargeMContraction

/-!
# Diagonal mutual locality of the charge-`±1` lattice vertex operators

Packages the charge-`±1` boson factors into `EEData` bundles (`LatticeLocalityCore`) and derives
the **diagonal self-locality** `Local (Yemα 1) (Yemα 1)` and `Local (Yemα (-1)) (Yemα (-1))`
(self-pairing `⟨±α,±α⟩ = 2`, so the lattice operators commute exactly).  These are two of the
four pairwise-locality data for the `A₁` lattice VOA's generating fields.  All `sorry`-free,
`pbw`-free.
-/

namespace VOA
namespace LatExp

open scoped BigOperators TensorProduct
open Module (End)
open HeisenbergN (vacuumN)
open LatticeVOA (LatModule LatGrp eVec latState latVacuum)

/-! ## §1  The charge-`1` contraction in `EplusC`/`EminusC` form -/

/-- The charge-`1` FLM contraction (the charge-`1` companion of `EplusCm1_comp_EminusCm1`), via
`EminusC 1 = Eminus`, `EplusC 1 = Eplus`, and `Eplus_comp_Eminus`. -/
theorem EplusC1_comp_EminusC1 (a b : ℤ) :
    (EplusC 1 a).comp (EminusC 1 b)
      = (EminusC 1 b).comp (EplusC 1 a)
        - (2 : ℂ) • ((EminusC 1 (b - 1)).comp (EplusC 1 (a + 1)))
        + (EminusC 1 (b - 2)).comp (EplusC 1 (a + 2)) := by
  simp only [EminusC_one_eq, EplusC_one_eq]
  exact Eplus_comp_Eminus a b

/-! ## §2  The charge-`±1` `EEData` bundles -/

/-- The charge-`1` boson-factor reordering data. -/
noncomputable def eeData1 : EEData where
  Em := EminusC 1
  Ep := EplusC 1
  EEop := EEC 1
  Em_neg := fun t ht => EminusC_neg 1 ht
  Ep_field := EplusC_isField 1
  Ep_pos := fun t ht => EplusC_pos 1 ht
  Em_comm := EminusC_comm 1
  Ep_comm := EplusC_comm 1
  contr := EplusC1_comp_EminusC1
  EE_conv := EEC_apply_conv 1

/-- The charge-`(-1)` boson-factor reordering data. -/
noncomputable def eeDataM1 : EEData where
  Em := EminusC (-1)
  Ep := EplusC (-1)
  EEop := EEC (-1)
  Em_neg := fun t ht => EminusC_neg (-1) ht
  Ep_field := EplusC_isField (-1)
  Ep_pos := fun t ht => EplusC_pos (-1) ht
  Em_comm := EminusC_comm (-1)
  Ep_comm := EplusC_comm (-1)
  contr := EplusCm1_comp_EminusCm1
  EE_conv := EEC_apply_conv (-1)

/-! ## §3  The diagonal bracket vanishes on every basis state -/

/-- **The pointwise self-locality identity** for the charge-`m` lattice vertex operator (`m² = 1`,
self-pairing `⟨mα,mα⟩ = 2`): on every basis state `p ⊗ e^{nα}`, `[Y(e^{mα},z₁), Y(e^{mα},z₂)]`
vanishes (the even-lattice operators commute exactly).  Reduced to `EEData.shift_comm` via the
sector-shift bookkeeping. -/
theorem Yemα_self_bracket_on_state (D : EEData) (m : ℤ) (hEE : D.EEop = EEC (m : ℂ))
    (hm2 : m * m = 1) (j k n : ℤ) (p : B) :
    bracketDist (Yemα m) (Yemα m) j k (p ⊗ₜ[ℂ] eVec n) = 0 := by
  rw [bracketDist_apply, LinearMap.sub_apply]
  simp only [Module.End.mul_apply, Yemα_tmul, ← hEE]
  rw [show j - 2 * m * (n + m) = (j - 2 * m * n) - 2 from by linear_combination (-2 : ℤ) * hm2,
    show k - 2 * m * (n + m) = (k - 2 * m * n) - 2 from by linear_combination (-2 : ℤ) * hm2,
    D.shift_comm (j - 2 * m * n) (k - 2 * m * n) p, sub_self]

/-- **The diagonal bracket is zero** for the charge-`m` lattice operator (`m² = 1`). -/
theorem Yemα_self_bracket_zero (D : EEData) (m : ℤ) (hEE : D.EEop = EEC (m : ℂ)) (hm2 : m * m = 1) :
    bracketDist (Yemα m) (Yemα m) = 0 := by
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change bracketDist (Yemα m) (Yemα m) j k y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single n a =>
          rw [(Finsupp.smul_single_one n a).symm]
          erw [TensorProduct.tmul_smul, map_smul, Yemα_self_bracket_on_state D m hEE hm2,
            smul_zero]

/-! ## §4  The main diagonal localities -/

/-- **`Local (Yemα 1) (Yemα 1)`** — the charge-`1` lattice operator commutes with itself
(bound `N = 0`), `pbw`-free. -/
theorem Yemα_one_local : Local (Yemα 1) (Yemα 1) :=
  local_of_bracketDist_eq_zero (Yemα_self_bracket_zero eeData1 1 (by norm_num [eeData1]) (by ring))

/-- **`Local (Yemα (-1)) (Yemα (-1))`** — the charge-`(-1)` lattice operator commutes with itself
(bound `N = 0`), `pbw`-free.  The new charge-`(-1)` diagonal locality. -/
theorem Yemα_negOne_local : Local (Yemα (-1)) (Yemα (-1)) :=
  local_of_bracketDist_eq_zero
    (Yemα_self_bracket_zero eeDataM1 (-1) (by norm_num [eeDataM1]) (by ring))

end LatExp
end VOA
