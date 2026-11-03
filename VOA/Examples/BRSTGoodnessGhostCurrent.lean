/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTGoodnessFock
import VOA.Examples.Sl2SemiInfiniteNormalOrder

/-!
# The ghost current zero modes preserve the ghost `R`-grading

The ghost current is `J^a_gh = Σ f^{ab}_c :b_c c_b:`, each bilinear the actual `(-1)`-product of
two odd ghost generators. By `normal_product_mode` (translation covariance of the three-pair
system) its zero mode is a locally finite sum of products `b_m c_{-1-m}` (in `z`-exponents), and
each such product shifts `((2R, gh), weight)` by `ghShift 0 m + ghShift 1 (-1-m) = 0`
(`ghShift_bc_cancel`): either `b` creates a mode that `c` destroys at the same level, or the
reverse.

* `ghostCurrentZeroPreserve` — **discharges `GhostCurrentZeroPreserve`**;
* `zeroModesPreserve_proved` — `ZeroModesPreserve (ghostRGrading w)` for every `w`, with no
  remaining hypothesis.
-/

namespace VOA.ConcreteHodge

open VOA.SympFerm VOA.Ghost Sl2SemiInfinite
open scoped TensorProduct

noncomputable section

theorem Y_gen_mem_ghostDeg (a : Fin 3) (e : Fin 2) (j : ℤ) {i : (ℤ × ℤ) × ℂ}
    {x : Sl2GhostSpace} (hx : x ∈ ghostDeg i) :
    sl2GhostSVA.Y (ghostGenerator a e) j x ∈ ghostDeg (i + ghShift e j) := by
  have h := ghostMode_mem_ghostDeg a e (-j - 1) hx
  have e1 : -(-j - 1) - 1 = j := by ring
  rw [e1] at h
  simpa only [gMode, mode_apply, e1] using h

theorem ghShift_bc_cancel (m : ℤ) : ghShift 0 m + ghShift 1 (-1 - m) = 0 := by
  unfold ghShift
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_neg (by omega),
      show (-(-1 - m) - 1).toNat = m.toNat by congr 1; ring,
      show (1 : Fin 2) + 1 = 0 from rfl, add_neg_cancel]
  · rw [if_neg hm, if_pos (by omega),
      show (-1 - m).toNat = (-m - 1).toNat by congr 1; ring,
      show (0 : Fin 2) + 1 = 1 from rfl, neg_add_cancel]

/-- The zero mode of one bilinear `:b_c c_b:` preserves the grading. -/
theorem bilinear_zero_mem (c b : Fin 3) {i : (ℤ × ℤ) × ℂ} {x : Sl2GhostSpace}
    (hx : x ∈ ghostDeg i) :
    mode (sl2GhostSVA.Y (ghostBilinear c b)) 0 x ∈ ghostDeg i := by
  rw [ghostBilinear, TranslationCovariant.normal_product_mode translationCovariant_sl2GhostSVA
    (bGhost_odd c) (cGhost_odd b) 0 x]
  refine finsum_induction (fun y => y ∈ ghostDeg i) (Submodule.zero_mem _)
    (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun m => ?_)
  simp only [normalOrderedε_apply, show -(0 : ℤ) - 1 - m = -1 - m by ring]
  have hb := fun {k} {y : Sl2GhostSpace} (hy : y ∈ ghostDeg k) =>
    Y_gen_mem_ghostDeg c 0 m hy
  have hc := fun {k} {y : Sl2GhostSpace} (hy : y ∈ ghostDeg k) =>
    Y_gen_mem_ghostDeg b 1 (-1 - m) hy
  simp only [ghostGenerator_zero, ghostGenerator_one] at hb hc
  split_ifs
  · rw [Module.End.mul_apply]
    have h := hb (hc hx)
    rwa [add_assoc, add_comm (ghShift 1 _), ghShift_bc_cancel, add_zero] at h
  · rw [LinearMap.smul_apply, Module.End.mul_apply]
    refine Submodule.smul_mem _ _ ?_
    have h := hc (hb hx)
    rwa [add_assoc, ghShift_bc_cancel, add_zero] at h

/-- The `j`-th coefficient of the state-field map, as a linear map. -/
def ghostYCoeff (j : ℤ) : Sl2GhostSpace →ₗ[ℂ] Module.End ℂ Sl2GhostSpace :=
  (LinearMap.proj j : (ℤ → Module.End ℂ Sl2GhostSpace) →ₗ[ℂ] _) ∘ₗ sl2GhostSVA.Y

theorem ghostYCoeff_apply (j : ℤ) (z : Sl2GhostSpace) : ghostYCoeff j z = sl2GhostSVA.Y z j :=
  rfl

/-- **`GhostCurrentZeroPreserve` holds.** -/
theorem ghostCurrentZeroPreserve : GhostCurrentZeroPreserve := by
  intro a i y hy
  change sl2GhostSVA.Y (ghostCurrent a) (-0 - 1) y ∈ ghostDeg i
  rw [← ghostYCoeff_apply, ghostCurrent, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have h := bilinear_zero_mem c b hy
  simpa only [mode_apply, ghostYCoeff_apply] using h

/-- **`ZeroModesPreserve` for the concrete ghost grading, with no hypotheses.** -/
theorem zeroModesPreserve_proved (w : Finset ModeIdx → ℝ) :
    ZeroModesPreserve (ghostRGrading w) :=
  zeroModesPreserve_concrete w ghostCurrentZeroPreserve antighostZeroShift

end

end VOA.ConcreteHodge
