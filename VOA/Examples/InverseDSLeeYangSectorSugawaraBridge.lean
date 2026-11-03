/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangHeterotypicLocality

/-!
# The shifted-current normal product is the momentum-sector Sugawara field

This is the finite bridge from the heterotypic normal-product calculation to the
momentum-sector Virasoro operators.  The only new coefficient in a shifted current is the
momentum zero mode, so the bridge is a four-term expansion with two single-support cross terms.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace LeeYangSectorSugawaraBridge

open Module (End)
open LeeYangFockExponential LeeYangFockVirasoro
open LeeYangHeterotypicLocality
open LatExp

noncomputable section

/-- The one-coefficient momentum correction to the oscillator current field. -/
noncomputable def momentumSpike (p : ℂ) : FormalDist (End ℂ LeeYangFock) :=
  fun j => if j = -1 then (2 * p) • (1 : End ℂ LeeYangFock) else 0

@[simp] theorem momentumSpike_apply (p : ℂ) (j : ℤ) :
    momentumSpike p j = if j = -1 then (2 * p) • (1 : End ℂ LeeYangFock) else 0 := rfl

theorem momentumSpike_isField (p : ℂ) : IsField (momentumSpike p) := by
  intro x
  refine ⟨-1, fun j hj => ?_⟩
  rw [momentumSpike_apply, if_neg (by omega : j ≠ -1)]
  rfl

theorem alphaField_isField : IsField alphaField :=
  HeisenbergN.currentN_isField 1 2 0

/-- A sector current is the oscillator current plus its momentum spike. -/
theorem sectorCurrentDist_eq (p : ℂ) :
    sectorCurrentDist p = alphaField + momentumSpike p := by
  funext j
  change sectorCurrent p (-j - 1) = alphaField j + momentumSpike p j
  rw [sectorCurrent, momentumSpike_apply]
  change alphaMode (-j - 1) +
      (if -j - 1 = 0 then 2 * p else 0) • 1 =
    alphaMode (-j - 1) + (if j = -1 then (2 * p) • 1 else 0)
  by_cases hj : j = -1
  · subst j
    simp
  · rw [if_neg hj, if_neg (by omega), zero_smul]

/-! ## Bilinearity helpers -/

theorem nprod_add_left_fock {a₁ a₂ b : FormalDist (End ℂ LeeYangFock)}
    (ha₁ : IsField a₁) (ha₂ : IsField a₂) (hb : IsField b)
    (hadd : IsField (a₁ + a₂)) (s : ℤ) (x : LeeYangFock) :
    nprod hadd hb s x = nprod ha₁ hb s x + nprod ha₂ hb s x := by
  rw [nprod_apply, nprod_apply, nprod_apply,
    ← finsum_add_distrib (normalOrdered_diag_support_finite ha₁ hb s x)
      (normalOrdered_diag_support_finite ha₂ hb s x)]
  exact finsum_congr fun j => by
    rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
    by_cases hj : 0 ≤ j
    · rw [if_pos hj, if_pos hj, if_pos hj]
      change ((a₁ j + a₂ j) * b (s - j)) x =
        (a₁ j * b (s - j)) x + (a₂ j * b (s - j)) x
      rw [add_mul, LinearMap.add_apply]
    · rw [if_neg hj, if_neg hj, if_neg hj]
      change (b (s - j) * (a₁ j + a₂ j)) x =
        (b (s - j) * a₁ j) x + (b (s - j) * a₂ j) x
      rw [mul_add, LinearMap.add_apply]

theorem nprod_add_right_fock {a b₁ b₂ : FormalDist (End ℂ LeeYangFock)}
    (ha : IsField a) (hb₁ : IsField b₁) (hb₂ : IsField b₂)
    (hadd : IsField (b₁ + b₂)) (s : ℤ) (x : LeeYangFock) :
    nprod ha hadd s x = nprod ha hb₁ s x + nprod ha hb₂ s x := by
  rw [nprod_apply, nprod_apply, nprod_apply,
    ← finsum_add_distrib (normalOrdered_diag_support_finite ha hb₁ s x)
      (normalOrdered_diag_support_finite ha hb₂ s x)]
  exact finsum_congr fun j => by
    rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
    by_cases hj : 0 ≤ j
    · rw [if_pos hj, if_pos hj, if_pos hj]
      change (a j * (b₁ (s - j) + b₂ (s - j))) x =
        (a j * b₁ (s - j)) x + (a j * b₂ (s - j)) x
      rw [mul_add, LinearMap.add_apply]
    · rw [if_neg hj, if_neg hj, if_neg hj]
      change ((b₁ (s - j) + b₂ (s - j)) * a j) x =
        (b₁ (s - j) * a j) x + (b₂ (s - j) * a j) x
      rw [add_mul, LinearMap.add_apply]

/-- `nprod` depends only on the underlying distributions, not on the field witnesses. -/
theorem nprod_congr_fock {a b a' b' : FormalDist (End ℂ LeeYangFock)}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (haa : a = a') (hbb : b = b') (s : ℤ) (x : LeeYangFock) :
    nprod ha hb s x = nprod ha' hb' s x := by
  subst a'
  subst b'
  rfl

/-! ## The three finite momentum terms -/

theorem nprod_alpha_momentumSpike (p : ℂ) (s : ℤ) :
    nprod alphaField_isField (momentumSpike_isField p) s =
      (2 * p) • alphaField (s + 1) := by
  apply LinearMap.ext
  intro x
  rw [nprod_apply]
  have hsupp : ∀ j : ℤ, j ≠ s + 1 →
      normalOrdered alphaField (momentumSpike p) j (s - j) x = 0 := by
    intro j hj
    have hsp : momentumSpike p (s - j) = 0 := by
      rw [momentumSpike_apply, if_neg (by omega)]
    rw [normalOrdered_apply]
    by_cases hgate : 0 ≤ j
    · rw [if_pos hgate, hsp, mul_zero, LinearMap.zero_apply]
    · rw [if_neg hgate, hsp, zero_mul, LinearMap.zero_apply]
  rw [finsum_eq_single _ (s + 1) hsupp, normalOrdered_apply,
    momentumSpike_apply, if_pos (by ring : s - (s + 1) = -1)]
  by_cases hgate : 0 ≤ s + 1
  · rw [if_pos hgate]
    rw [mul_smul_comm, mul_one, LinearMap.smul_apply]
  · rw [if_neg hgate]
    rw [smul_mul_assoc, one_mul, LinearMap.smul_apply]

theorem nprod_momentumSpike_alpha (p : ℂ) (s : ℤ) :
    nprod (momentumSpike_isField p) alphaField_isField s =
      (2 * p) • alphaField (s + 1) := by
  apply LinearMap.ext
  intro x
  rw [nprod_apply]
  have hsupp : ∀ j : ℤ, j ≠ -1 →
      normalOrdered (momentumSpike p) alphaField j (s - j) x = 0 := by
    intro j hj
    have hsp : momentumSpike p j = 0 := by
      rw [momentumSpike_apply, if_neg hj]
    rw [normalOrdered_apply]
    by_cases hgate : 0 ≤ j
    · rw [if_pos hgate, hsp, zero_mul, LinearMap.zero_apply]
    · rw [if_neg hgate, hsp, mul_zero, LinearMap.zero_apply]
  rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply,
    if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1), momentumSpike_apply, if_pos rfl]
  rw [show s - (-1 : ℤ) = s + 1 by ring]
  rw [mul_smul_comm, mul_one, LinearMap.smul_apply]

theorem nprod_momentumSpike_momentumSpike (p : ℂ) (s : ℤ) :
    nprod (momentumSpike_isField p) (momentumSpike_isField p) s =
      if s = -2 then (2 * p) • ((2 * p) • (1 : End ℂ LeeYangFock)) else 0 := by
  apply LinearMap.ext
  intro x
  by_cases hs : s = -2
  · subst s
    rw [if_pos rfl, nprod_apply]
    have hsupp : ∀ j : ℤ, j ≠ -1 →
        normalOrdered (momentumSpike p) (momentumSpike p) j ((-2 : ℤ) - j) x = 0 := by
      intro j hj
      have hsp : momentumSpike p j = 0 := by
        rw [momentumSpike_apply, if_neg hj]
      rw [normalOrdered_apply]
      by_cases hgate : 0 ≤ j
      · rw [if_pos hgate, hsp, zero_mul, LinearMap.zero_apply]
      · rw [if_neg hgate, hsp, mul_zero, LinearMap.zero_apply]
    rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply,
      if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1)]
    change (((2 * p) • (1 : End ℂ LeeYangFock)) *
      ((2 * p) • (1 : End ℂ LeeYangFock))) x =
      ((2 * p) • ((2 * p) • (1 : End ℂ LeeYangFock))) x
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, LinearMap.smul_apply, smul_smul]
  · rw [if_neg hs, nprod_apply]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [normalOrdered_apply]
    by_cases hgate : 0 ≤ j
    · rw [if_pos hgate]
      have hj : j ≠ -1 := by omega
      change ((if j = -1 then (2 * p) • (1 : End ℂ LeeYangFock) else 0) *
        (if s - j = -1 then (2 * p) • (1 : End ℂ LeeYangFock) else 0)) x = 0
      rw [if_neg hj, zero_mul, LinearMap.zero_apply]
    · rw [if_neg hgate]
      by_cases hj : j = -1
      · subst j
        change ((if s - (-1) = -1 then (2 * p) • (1 : End ℂ LeeYangFock) else 0) *
          (if (-1 : ℤ) = -1 then (2 * p) • (1 : End ℂ LeeYangFock) else 0)) x = 0
        rw [if_neg (by omega : s - (-1) ≠ -1), zero_mul, LinearMap.zero_apply]
      · change ((if s - j = -1 then (2 * p) • (1 : End ℂ LeeYangFock) else 0) *
          (if j = -1 then (2 * p) • (1 : End ℂ LeeYangFock) else 0)) x = 0
        rw [if_neg hj, mul_zero, LinearMap.zero_apply]

/-! ## Sugawara bridge -/

/-- Expanding the shifted current normal product gives the oscillator term, two equal cross
terms, and the momentum square. -/
theorem nprod_sectorCurrentDist_expand (p : ℂ) (s : ℤ) (x : LeeYangFock) :
    nprod (sectorCurrentDist_isField p) (sectorCurrentDist_isField p) s x =
      nprod alphaField_isField alphaField_isField s x +
        ((2 * p) • alphaField (s + 1)) x +
        ((2 * p) • alphaField (s + 1)) x +
        (if s = -2 then (2 * p) • ((2 * p) • (1 : End ℂ LeeYangFock)) else 0) x := by
  have hsum : IsField (alphaField + momentumSpike p) :=
    alphaField_isField.add (momentumSpike_isField p)
  have hcur := sectorCurrentDist_eq p
  rw [nprod_congr_fock (sectorCurrentDist_isField p) (sectorCurrentDist_isField p)
      hsum hsum hcur hcur s x,
    nprod_add_left_fock alphaField_isField
      (momentumSpike_isField p) hsum hsum,
    nprod_add_right_fock alphaField_isField alphaField_isField
      (momentumSpike_isField p) hsum,
    nprod_add_right_fock (momentumSpike_isField p)
      alphaField_isField (momentumSpike_isField p) hsum,
    nprod_alpha_momentumSpike, nprod_momentumSpike_alpha,
    nprod_momentumSpike_momentumSpike]
  abel_nf

/-- **Shifted-current Sugawara bridge**:
`(1/4):J_pJ_p:` is exactly the momentum-sector Sugawara field. -/
theorem quarter_nprod_sectorCurrentDist (p : ℂ) (s : ℤ) :
    (1 / 4 : ℂ) • nprod (sectorCurrentDist_isField p) (sectorCurrentDist_isField p) s =
      sectorSugawara p (-s - 2) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.smul_apply, nprod_sectorCurrentDist_expand,
    smul_add, smul_add, smul_add]
  have hquarter₀ := congrArg (fun T : End ℂ LeeYangFock => T x)
    (LatExp.quarter_nprod_alphaField s)
  simp only [LinearMap.smul_apply] at hquarter₀
  have hbase : nprod alphaField_isField alphaField_isField s x =
      nprod (HeisenbergN.currentN_isField 1 2 0)
        (HeisenbergN.currentN_isField 1 2 0) s x :=
    nprod_congr_fock alphaField_isField alphaField_isField
      (HeisenbergN.currentN_isField 1 2 0) (HeisenbergN.currentN_isField 1 2 0)
      rfl rfl s x
  have hquarter : (1 / 4 : ℂ) •
      nprod alphaField_isField alphaField_isField s x =
      HeisenbergN.LvirN 1 2 (-s - 2) x := by
    rw [hbase]
    exact hquarter₀
  rw [hquarter, sectorSugawara, alphaField_apply,
    show -(s + 1) - 1 = -s - 2 by ring]
  simp only [alphaMode, LatExp.α]
  by_cases hs : s = -2
  · subst s
    simp only [if_pos rfl]
    norm_num
    module
  · have hm : -s - 2 ≠ 0 := by omega
    simp only [if_neg hs, if_neg hm, LinearMap.zero_apply, smul_zero, add_zero]
    norm_num
    module

end
end LeeYangSectorSugawaraBridge
end InverseDS
end VOA
