import VOA.Classification.COne.OrbIcoZRecurrence
import VOA.Modules.ZhuVermaAnArchSkewModOnm
import VOA.Modules.ZhuVermaAnArchBottomDefectClose

/-! The circle and skew relations used by the finite icosahedral mode calculation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbZhu Polynomial

abbrev selfMode (k : ℤ) : A OrbIco.Wi :=
  mk OrbIco.Wi (OrbIco.Wi.smul OrbIco.Xico k OrbIco.Xico)

theorem selfMode_high (k : ℤ) (hk : 71 < k) : selfMode k = 0 := by
  have hg : OrbIco.Wi.smul OrbIco.Xico k OrbIco.Xico ∈ OrbIco.Wi.grading (71 - k) := by
    convert OrbIco.Wi.grading_mode _ OrbIco.Xico_grading _ OrbIco.Xico_grading k using 2
    ring
  rw [OrbIco.Wi.positivity _ (by omega)] at hg
  rw [selfMode, (Submodule.mem_bot ℂ).mp hg, map_zero]

/-- All the higher circle relations with a fixed weight-thirty-six numerator. -/
theorem selfMode_circle (m : ℕ) :
    ∑ j ∈ Finset.range 37, cbz 36 (j : ℤ) • selfMode ((j : ℤ) - (2 + m)) = 0 := by
  have h := (mk_eq_zero_iff OrbIco.Wi).mpr
    (Hres_mem_O OrbIco.Wi OrbIco.Xico_grading OrbIco.Xico m 0)
  simpa only [Hres, Gres, add_zero, map_sum,
    map_smul, Nat.cast_add, Nat.cast_ofNat] using h

/-- Skew symmetry reduced to a finite sum in the intrinsic Zhu algebra. -/
theorem selfMode_skew (k : ℤ) (hk : k ≤ 70) :
    selfMode k = sgn (k + 1) •
      ∑ j ∈ Finset.range ((70 - k).toNat + 1), cbz (70 - k) (j : ℤ) •
        selfMode (k + j) := by
  have h := skew_mod_Onm OrbIco.Wi 0 0 OrbIco.Xico_grading OrbIco.Xico_grading k
  have hs : (∑ᶠ j : ℕ, cbz (70 - k) (j : ℤ) •
      OrbIco.Wi.smul OrbIco.Xico (k + j) OrbIco.Xico) =
      ∑ j ∈ Finset.range ((70 - k).toNat + 1), cbz (70 - k) (j : ℤ) •
        OrbIco.Wi.smul OrbIco.Xico (k + j) OrbIco.Xico := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hn
    have hj' : 70 - k < (j : ℤ) := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hn
      omega
    exact hj (by dsimp only; rw [cbz_lt (by omega) hj', zero_smul])
  norm_num only at h
  rw [hs, Onm_zero_zero_eq_O] at h
  have hh := (mk_eq_zero_iff OrbIco.Wi).mpr h
  rw [map_sub, map_smul, map_sum] at hh
  simpa only [map_smul, sub_eq_zero] using hh

end VOA.Classification.COne.OrbIcoZ
