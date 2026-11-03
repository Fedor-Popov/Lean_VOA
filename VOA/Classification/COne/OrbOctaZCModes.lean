import VOA.Classification.COne.OrbOctaZCRecurrence
import VOA.Modules.ZhuVermaAnArchSkewModOnm
import VOA.Modules.ZhuVermaAnArchBottomDefectClose

/-! The circle and skew relations used by the finite octahedral mode calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZC
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial

abbrev selfMode (k : ℤ) : A OrbOctaR.W :=
  mk OrbOctaR.W (OrbOctaR.W.smul OrbOctaR.X k OrbOctaR.X)

theorem selfMode_high (k : ℤ) (hk : 31 < k) : selfMode k = 0 := by
  have hg : OrbOctaR.W.smul OrbOctaR.X k OrbOctaR.X ∈ OrbOctaR.W.grading (31 - k) := by
    convert OrbOctaR.W.grading_mode _ OrbOctaR.X_grading _ OrbOctaR.X_grading k using 2
    ring
  rw [OrbOctaR.W.positivity _ (by omega)] at hg
  rw [selfMode, (Submodule.mem_bot ℂ).mp hg, map_zero]

/-- All the higher circle relations with a fixed weight-sixteen numerator. -/
theorem selfMode_circle (m : ℕ) :
    ∑ j ∈ Finset.range 17, cbz 16 (j : ℤ) • selfMode ((j : ℤ) - (2 + m)) = 0 := by
  have h := (mk_eq_zero_iff OrbOctaR.W).mpr
    (Hres_mem_O OrbOctaR.W OrbOctaR.X_grading OrbOctaR.X m 0)
  simpa only [Hres, Gres, add_zero, map_sum,
    map_smul, Nat.cast_add, Nat.cast_ofNat] using h

/-- Skew symmetry reduced to a finite sum in the intrinsic Zhu algebra. -/
theorem selfMode_skew (k : ℤ) (hk : k ≤ 30) :
    selfMode k = sgn (k + 1) •
      ∑ j ∈ Finset.range ((30 - k).toNat + 1), cbz (30 - k) (j : ℤ) •
        selfMode (k + j) := by
  have h := skew_mod_Onm OrbOctaR.W 0 0 OrbOctaR.X_grading OrbOctaR.X_grading k
  have hs : (∑ᶠ j : ℕ, cbz (30 - k) (j : ℤ) •
      OrbOctaR.W.smul OrbOctaR.X (k + j) OrbOctaR.X) =
      ∑ j ∈ Finset.range ((30 - k).toNat + 1), cbz (30 - k) (j : ℤ) •
        OrbOctaR.W.smul OrbOctaR.X (k + j) OrbOctaR.X := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hn
    have hj' : 30 - k < (j : ℤ) := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hn
      omega
    exact hj (by dsimp only; rw [cbz_lt (by omega) hj', zero_smul])
  norm_num only at h
  rw [hs, Onm_zero_zero_eq_O] at h
  have hh := (mk_eq_zero_iff OrbOctaR.W).mpr h
  rw [map_sub, map_smul, map_sum] at hh
  simpa only [map_smul, sub_eq_zero] using hh

end VOA.Classification.COne.OrbOctaZC
