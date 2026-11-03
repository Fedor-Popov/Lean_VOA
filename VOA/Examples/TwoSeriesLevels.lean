/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BoundarySingularFamily
import VOA.Examples.VirasoroBoundaryRealStructure

/-!
# Level data for the coset transfer `GU(L_k(sl₂)) ⇒ GU(M(2,2n+3))`

The coset construction `(L_k ⊗ L_1) // L_{k+1}`, with the auxiliary universal factor
`V^{k_U}` cancelling the total level to `-4`, depends on four numbers: the boundary level
`k_A`, the auxiliary level `k_U = -5 - k_A`, the target central charge `c`, and the index `m`
of `c = c_{2,2m+1}` in the boundary family.  `CosetLevels` bundles them together with every
arithmetic fact the construction uses.

* `boundaryFamilyLevels n` — the boundary family `k_A = -2 + 2/(2n+1)`, `k_U = -3 - 2/(2n+1)`,
  target `c_{2,2n+3} = boundaryCharge (n+1)`.  The coset central-charge identity
  `3k/(k+2) + 1 - 3(k+1)/(k+3) = c_{2,2n+3}` is proved for every `n` (`twoSeries_charge`).
* `leeYangLevels` — the same data written with the literal numbers `-4/3`, `-11/3`,
  `leeYangC` of the existing Lee–Yang chain, so that every generic object specializes
  *definitionally* to the existing concrete one.  `boundaryFamilyLevels_one_*` record that the two
  instances at `n = 1` agree field by field.
* `twoSeriesLevels n` — `boundaryFamilyLevels n`, with `leeYangLevels` substituted at `n = 1`
  (`twoSeriesLevels_one : twoSeriesLevels 1 = leeYangLevels` is `rfl`), so the general theorem
  at `n = 1` is literally a statement about the existing Lee–Yang objects.

Two level fields are kept for the boundary factor: `kA` is the level of the carrier, `kAct` the
(provably equal) index of its current action.  At Lee–Yang the existing carrier is built from
`level 1` while its action is indexed by the literal `-4/3`; keeping both makes the generic
construction reproduce that choice on the nose.
-/

namespace VOA.TwoSeries

open VirGradedUnitarity

noncomputable section

/-- The numerical data of one coset transfer, with all arithmetic facts used downstream. -/
structure CosetLevels where
  /-- Level of the boundary affine carrier. -/
  kA : ℂ
  /-- Index of the boundary current action (equal to `kA`). -/
  kAct : ℂ
  /-- Level of the auxiliary universal factor. -/
  kU : ℂ
  /-- The auxiliary level as a real number. -/
  kUr : ℝ
  /-- Target central charge. -/
  c : ℂ
  /-- Index of `c` in the boundary family `c_{2,2m+1}`. -/
  m : ℕ
  kAct_eq : kAct = kA
  aNoncritical : kA + 2 ≠ 0
  aReal : (starRingEnd ℂ) kA = kA
  kU_eq : kU = (kUr : ℂ)
  kUr_lt : kUr < -2
  uNoncritical : kU + 2 ≠ 0
  diagNoncritical : kAct + 1 + 2 ≠ 0
  /-- The total matter level cancels the ghost level `-4`. -/
  sum : kAct + 1 + kU = -4
  /-- Coset central charge `c(k) + c(1) - c(k+1)`. -/
  charge : 3 * kA / (kA + 2) + 1 - 3 * (kAct + 1) / (kAct + 1 + 2) = c
  /-- The target is the `m`th boundary minimal model. -/
  boundary : boundaryCharge m = c

namespace CosetLevels

variable (L : CosetLevels)

theorem uReal : (starRingEnd ℂ) L.kU = L.kU := by
  rw [L.kU_eq]; exact Complex.conj_ofReal _

/-- The Feigin–Fuchs parametrization of the target charge. -/
theorem lam_spec : 1 - 12 * boundaryBackgroundCharge L.m ^ 2 = L.c :=
  (boundaryBackgroundCharge_spec L.m).trans L.boundary

end CosetLevels

/-! ### The boundary family -/

open AffineSl2BoundarySingularFamily

/-- `q = 2n+1` as a complex number is nonzero. -/
theorem den_ne_zero (n : ℕ) : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.succ_ne_zero (2 * n))

theorem level_eq (n : ℕ) : level n = -2 + 2 / ((2 * n + 1 : ℕ) : ℂ) := rfl

/-- The real auxiliary level `-3 - 2/(2n+1)`. -/
def uLevelReal (n : ℕ) : ℝ := -3 - 2 / ((2 * n + 1 : ℕ) : ℝ)

theorem uLevelReal_lt (n : ℕ) : uLevelReal n < -2 := by
  unfold uLevelReal
  have : (0 : ℝ) < 2 / ((2 * n + 1 : ℕ) : ℝ) := by positivity
  linarith

theorem level_real (n : ℕ) : (starRingEnd ℂ) (level n) = level n := by
  rw [level_eq]
  simp only [map_add, map_neg, map_div₀, map_ofNat, map_natCast]

theorem uLevel_cast (n : ℕ) : (-5 - level n : ℂ) = ((uLevelReal n : ℝ) : ℂ) := by
  rw [level_eq, uLevelReal]
  push_cast
  ring

theorem uLevel_noncritical (n : ℕ) : (-5 - level n : ℂ) + 2 ≠ 0 := by
  rw [uLevel_cast]
  have h := uLevelReal_lt n
  intro h0
  have : ((uLevelReal n : ℝ) : ℂ) = ((-2 : ℝ) : ℂ) := by
    rw [show ((-2 : ℝ) : ℂ) = -2 by push_cast; ring]; linear_combination h0
  have := Complex.ofReal_injective this
  linarith

theorem diag_noncritical (n : ℕ) : level n + 1 + 2 ≠ 0 := by
  rw [level_eq]
  have hq := den_ne_zero n
  intro h
  have h' : ((2 * n + 1 : ℕ) : ℂ) + 2 = 0 := by
    field_simp at h
    linear_combination h
  have : ((2 * n + 3 : ℕ) : ℂ) = 0 := by push_cast at h' ⊢; linear_combination h'
  exact absurd (by exact_mod_cast this : (2 * n + 3 : ℕ) = 0) (by omega)

/-- The coset central charge of `(L_k ⊗ L_1)//L_{k+1}` at `k = -2 + 2/(2n+1)` is
`c_{2,2n+3} = 1 - 3(2n+1)²/(2n+3)`. -/
theorem twoSeries_charge (n : ℕ) :
    3 * level n / (level n + 2) + 1 - 3 * (level n + 1) / (level n + 1 + 2) =
      boundaryCharge (n + 1) := by
  have h1 := diag_noncritical n
  rw [level_eq] at h1 ⊢
  have hq := den_ne_zero n
  have h3 : ((2 * n + 3 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (2 * n + 2))
  have hA : (-2 + 2 / ((2 * n + 1 : ℕ) : ℂ) + 2) = 2 / ((2 * n + 1 : ℕ) : ℂ) := by ring
  have hD : (-2 + 2 / ((2 * n + 1 : ℕ) : ℂ) + 1 + 2) =
      ((2 * n + 3 : ℕ) : ℂ) / ((2 * n + 1 : ℕ) : ℂ) := by
    field_simp; push_cast; ring
  have hB : boundaryCharge (n + 1) =
      1 - 3 * ((2 * n + 1 : ℕ) : ℂ) ^ 2 / ((2 * n + 3 : ℕ) : ℂ) := by
    simp only [boundaryCharge, boundaryMinimalCentralCharge]
    push_cast
    ring_nf
  rw [hA, hD, hB]
  field_simp
  push_cast
  ring

/-- The uniform level data of the `n`th member of the `(2, 2n+3)` series. -/
def boundaryFamilyLevels (n : ℕ) : CosetLevels where
  kA := level n
  kAct := level n
  kU := -5 - level n
  kUr := uLevelReal n
  c := boundaryCharge (n + 1)
  m := n + 1
  kAct_eq := rfl
  aNoncritical := level_noncritical n
  aReal := level_real n
  kU_eq := uLevel_cast n
  kUr_lt := uLevelReal_lt n
  uNoncritical := uLevel_noncritical n
  diagNoncritical := diag_noncritical n
  sum := by ring
  charge := twoSeries_charge n
  boundary := rfl

/-- The Lee–Yang level data, written with the literal numbers of the existing chain. -/
def leeYangLevels : CosetLevels where
  kA := level 1
  kAct := -4 / 3
  kU := -11 / 3
  kUr := -11 / 3
  c := LeeYang.leeYangC
  m := 2
  kAct_eq := level_one.symm
  aNoncritical := level_noncritical 1
  aReal := level_real 1
  kU_eq := by push_cast; ring
  kUr_lt := by norm_num
  uNoncritical := by norm_num
  diagNoncritical := by norm_num
  sum := by norm_num
  charge := by rw [level_one]; norm_num [LeeYang.leeYangC]
  boundary := boundaryCharge_two_eq_leeYangC

/-! ### The two descriptions agree at `n = 1` -/

theorem boundaryFamilyLevels_one_kA : (boundaryFamilyLevels 1).kA = leeYangLevels.kA := rfl

theorem boundaryFamilyLevels_one_kAct :
    (boundaryFamilyLevels 1).kAct = leeYangLevels.kAct := level_one

theorem boundaryFamilyLevels_one_kU : (boundaryFamilyLevels 1).kU = leeYangLevels.kU := by
  change -5 - level 1 = -11 / 3
  rw [level_one]; norm_num

theorem boundaryFamilyLevels_one_kUr : (boundaryFamilyLevels 1).kUr = leeYangLevels.kUr := by
  change -3 - 2 / ((2 * 1 + 1 : ℕ) : ℝ) = -11 / 3
  norm_num

theorem boundaryFamilyLevels_one_c : (boundaryFamilyLevels 1).c = leeYangLevels.c :=
  boundaryCharge_two_eq_leeYangC

theorem boundaryFamilyLevels_one_m : (boundaryFamilyLevels 1).m = leeYangLevels.m := rfl

/-- The level data of the `(2, 2n+3)` series.  It is `boundaryFamilyLevels n`, except that at
`n = 1` the numerically equal literal Lee–Yang presentation `leeYangLevels` is used, so that
every downstream object at `n = 1` is *definitionally* the existing Lee–Yang object.  The two
presentations agree field by field (`boundaryFamilyLevels_one_*`). -/
def twoSeriesLevels : ℕ → CosetLevels
  | 1 => leeYangLevels
  | n => boundaryFamilyLevels n

theorem twoSeriesLevels_one : twoSeriesLevels 1 = leeYangLevels := rfl

theorem twoSeriesLevels_kA (n : ℕ) : (twoSeriesLevels n).kA = level n := by
  unfold twoSeriesLevels; split <;> rfl

theorem twoSeriesLevels_kU (n : ℕ) : (twoSeriesLevels n).kU = -3 - 2 / ((2 * n + 1 : ℕ) : ℂ) := by
  unfold twoSeriesLevels
  split
  · change (-11 / 3 : ℂ) = _; norm_num
  · change -5 - level n = _; rw [level_eq]; ring

/-- The target of the `n`th member is `c_{2,2n+3}`. -/
theorem twoSeriesLevels_c (n : ℕ) : (twoSeriesLevels n).c = boundaryCharge (n + 1) := by
  unfold twoSeriesLevels
  split
  · exact boundaryCharge_two_eq_leeYangC.symm
  · rfl

theorem twoSeriesLevels_m (n : ℕ) : (twoSeriesLevels n).m = n + 1 := by
  unfold twoSeriesLevels; split <;> rfl

end

end VOA.TwoSeries
