/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorSkewJacobi
import VOA.Modules.LogTensorIntertwining
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Skew-symmetry of logarithmic intertwining operators (HLZ II §3) — T1b

For a logarithmic intertwining operator `𝒴` of type `(W₃ / W₁ W₂)` (HLZ II Def. 3.10) and
`r ∈ ℤ`, Huang–Lepowsky–Zhang define

  `Ω_r(𝒴)(w₂, x) w₁ = e^{x L(−1)} 𝒴(w₁, e^{(2r+1)πi} x) w₂`,

where `e^{(2r+1)πi}x` means: `x^s ↦ e^{(2r+1)πi s} x^s` and `log x ↦ log x + (2r+1)πi`.
In modes it factors into two operations, both formalized here for weak modules:

* the **per-log-degree skew operator** `skewK` (`L₋₁`-twisted reflection with the phase
  `c n = e^{−(2r+1)πi(n+1)}`, applied to each log component; it is the library's FHL skew
  operator `Ω_c`, ported to weak modules in `LogTensorSkewCore`/`LogTensorSkewJacobi`):
  `skewK(𝒴)_{n;k}(w₂)w₁ = c n · Σ_{j ≥ 0} ((−1)ʲ/j!) L₋₁ʲ (w₁)_{n+j;k} w₂`;
* the **log shift** `logShift a` (`log x ↦ log x + a`):
  `(logShift a 𝒴)_{n;j} = Σ_{k ≥ j} C(k,j) a^{k−j} 𝒴_{n;k}`.

## Main results
* `isLogIntertwining_skewK` — `skewK 𝒴` is a logarithmic intertwining operator of type
  `(W₃ / W₂ W₁)` for every phase with `c(n+1) = −c(n)`, `c n ≠ 0`.  The `L(−1)`-derivative
  property picks up the logarithmic correction `(k+1)·skewK_{n−1;k+1}` (`skewK_L_neg_one`).
* `isLogIntertwining_logShift` — `logShift a 𝒴` is a logarithmic intertwining operator of the
  same type, for every `a ∈ ℂ`.
* `omega`, `isLogIntertwining_omega` — **HLZ's `Ω_r(𝒴)` is a logarithmic intertwining
  operator of type `(W₃ / W₂ W₁)`**, for all weak modules and all `r ∈ ℤ`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.LogTensor

open Module (End)
open scoped BigOperators
open VOA.LogSkew

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}

/-- The `k`-th log component of log mode data, as FHL mode data. -/
def comp (Y : LogModes M₁ M₂ M₃) (k : ℕ) : IntertwiningModes M₁ M₂ M₃ := fun n => Y n k

@[simp] theorem comp_apply (Y : LogModes M₁ M₂ M₃) (k : ℕ) (n : ℂ) : comp Y k n = Y n k := rfl

namespace IsLogIntertwining

variable {Y : LogModes M₁ M₂ M₃}

theorem trunc_comp (hY : IsLogIntertwining A₁ A₂ A₃ Y) (k : ℕ) : Trunc (comp Y k) := by
  intro w₁ w₂ n
  obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ n
  exact ⟨N, fun m hm => hN m hm k⟩

/-- Each log component satisfies the Jacobi identity (defect form). -/
theorem S_comp_eq_zero (hY : IsLogIntertwining A₁ A₂ A₃ Y) (k : ℕ) :
    ∀ u w₁ w₂ ℓ m n, S A₁ A₂ A₃ (comp Y k) u w₁ w₂ ℓ m n = 0 := by
  intro u w₁ w₂ ℓ m n
  rw [S, sub_eq_zero]
  exact hY.jacobi u w₁ w₂ ℓ m n k

/-- `𝒴_{q;k}(w₁)(L₋₁w₂) = L₋₁ 𝒴_{q;k}(w₁)w₂ + q 𝒴_{q−1;k}(w₁)w₂ − (k+1) 𝒴_{q−1;k+1}(w₁)w₂`. -/
theorem Y_Lm1_right (hY : IsLogIntertwining A₁ A₂ A₃ Y) (q : ℂ) (k : ℕ) (w₁ : M₁) (w₂ : M₂) :
    Y q k w₁ (Lm1 A₂ w₂)
      = Lm1 A₃ (Y q k w₁ w₂) + q • Y (q - 1) k w₁ w₂ - ((k : ℂ) + 1) • Y (q - 1) (k + 1) w₁ w₂ := by
  have h := hY.commutator W.conformalVector w₁ w₂ 0 q k
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])] at h
  have hL := hY.L_neg_one w₁ q k
  have e : Y ((0 : ℤ) + q - (0 : ℤ)) k (mode (A₁.YM W.conformalVector) (0 : ℤ) w₁) w₂
      = (-q) • Y (q - 1) k w₁ w₂ + ((k : ℂ) + 1) • Y (q - 1) (k + 1) w₁ w₂ := by
    rw [show ((0 : ℤ) : ℂ) + q - ((0 : ℤ) : ℂ) = q by push_cast; ring]
    have := congrArg (fun F => F w₂) hL
    simpa only [LinearMap.add_apply, LinearMap.smul_apply] using this
  rw [cbz_zero_left, if_pos rfl, one_smul, e] at h
  change Y q k w₁ (mode (A₂.YM W.conformalVector) 0 w₂) = _
  change mode (A₃.YM W.conformalVector) 0 (Y q k w₁ w₂) - _ = _ at h
  linear_combination (norm := module) -h

end IsLogIntertwining

/-! ## The per-log-degree skew operator -/

/-- **Per-log-degree skew operator**: `skewK(𝒴)_{n;k} = Ω_c(𝒴_{·;k})_n`. -/
noncomputable def skewK (A₃ : WeakModule W M₃) (c : ℂ → ℂ) (Y : LogModes M₁ M₂ M₃) :
    LogModes M₂ M₁ M₃ :=
  fun n k => skewModes (Lm1 A₃) c (comp Y k) n

namespace IsLogIntertwining

variable {Y : LogModes M₁ M₂ M₃}

theorem skewK_apply (hY : IsLogIntertwining A₁ A₂ A₃ Y) (c : ℂ → ℂ) (n : ℂ) (k : ℕ)
    (w₂ : M₂) (w₁ : M₁) :
    skewK A₃ c Y n k w₂ w₁ = c n • sSum (Lm1 A₃) (comp Y k) n w₁ w₂ :=
  skewModes_apply (hY.trunc_comp k) n w₂ w₁

/-- `skewK` written as a finite sum, given a uniform truncation bound. -/
theorem skewK_eq_sum (hY : IsLogIntertwining A₁ A₂ A₃ Y) (c : ℂ → ℂ) (n : ℂ) (k : ℕ)
    (w₂ : M₂) (w₁ : M₁) (J : ℕ) (hJ : ∀ j : ℕ, J ≤ j → Y (n + j) k w₁ w₂ = 0) :
    skewK A₃ c Y n k w₂ w₁
      = c n • ∑ j ∈ Finset.range J, sc j • (Lm1 A₃ ^ j) (Y (n + j) k w₁ w₂) := by
  rw [hY.skewK_apply, sSum_eq_sum J (fun j hj => hJ j hj)]
  rfl

/-- **`L₋₁`-derivative property of `skewK`**, with the logarithmic correction:
`skewK(L₋₁w₂)_{n;k} = −n skewK(w₂)_{n−1;k} + (k+1) skewK(w₂)_{n−1;k+1}`. -/
theorem skewK_L_neg_one (hY : IsLogIntertwining A₁ A₂ A₃ Y) {c : ℂ → ℂ}
    (hc : ∀ n, c (n + 1) = -c n) (w₂ : M₂) (n : ℂ) (k : ℕ) :
    skewK A₃ c Y n k (Lm1 A₂ w₂)
      = (-n) • skewK A₃ c Y (n - 1) k w₂ + ((k : ℂ) + 1) • skewK A₃ c Y (n - 1) (k + 1) w₂ := by
  refine LinearMap.ext fun w₁ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  set L := Lm1 A₃
  have hcn : c (n - 1) = - c n := by
    have := hc (n - 1); rw [sub_add_cancel] at this; linear_combination this
  obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ (n - 1)
  set K := N.toNat
  have hK : ∀ j : ℕ, K ≤ j → ∀ k, Y (n - 1 + j) k w₁ w₂ = 0 := fun j hj k =>
    hN (j : ℤ) (by omega) k
  have hK' : ∀ j : ℕ, K ≤ j → ∀ k, Y (n + j) k w₁ w₂ = 0 := fun j hj k => by
    rw [show n + (j : ℂ) = n - 1 + ((j + 1 : ℕ) : ℂ) by push_cast; ring]
    exact hK _ (by omega) k
  have hcomb : ∀ j : ℕ, Y (n + j) k w₁ (Lm1 A₂ w₂)
      = L (Y (n + j) k w₁ w₂) + (n + j) • Y (n - 1 + j) k w₁ w₂
        - ((k : ℂ) + 1) • Y (n - 1 + j) (k + 1) w₁ w₂ := by
    intro j
    rw [hY.Y_Lm1_right, show n + (j : ℂ) - 1 = n - 1 + j by ring]
  rw [hY.skewK_eq_sum c n k _ w₁ (K + 1) (fun j hj => by
      rw [hcomb, hK' j (by omega), hK j (by omega), hK j (by omega), map_zero, smul_zero,
        smul_zero, add_zero, sub_zero]),
    hY.skewK_eq_sum c (n - 1) k w₂ w₁ (K + 1) (fun j hj => hK j (by omega) k),
    hY.skewK_eq_sum c (n - 1) (k + 1) w₂ w₁ (K + 1) (fun j hj => hK j (by omega) (k + 1)), hcn]
  simp only [hcomb, map_add, map_sub, map_smul, smul_add, smul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : ∑ j ∈ Finset.range (K + 1), sc j • (L ^ j) (L (Y (n + j) k w₁ w₂))
      = ∑ j ∈ Finset.range K, sc j • (L ^ (j + 1)) (Y (n + j) k w₁ w₂) := by
    rw [Finset.sum_range_succ, hK' K le_rfl, map_zero, map_zero, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ, Module.End.mul_apply]
  have hB2 : ∑ j ∈ Finset.range (K + 1), (sc j * (j : ℂ)) • (L ^ j) (Y (n - 1 + j) k w₁ w₂)
      = -∑ j ∈ Finset.range K, sc j • (L ^ (j + 1)) (Y (n + j) k w₁ w₂) := by
    rw [Finset.sum_range_succ', ← Finset.sum_neg_distrib]
    simp only [Nat.cast_zero, mul_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((j + 1 : ℕ) : ℂ) = (j : ℂ) + 1 by push_cast; ring, sc_succ_mul,
      show n - 1 + ((j : ℂ) + 1) = n + j by ring, neg_smul]
  have hB : ∑ j ∈ Finset.range (K + 1), sc j • (n + (j : ℂ)) • (L ^ j) (Y (n - 1 + j) k w₁ w₂)
      = n • ∑ j ∈ Finset.range (K + 1), sc j • (L ^ j) (Y (n - 1 + j) k w₁ w₂)
        - ∑ j ∈ Finset.range K, sc j • (L ^ (j + 1)) (Y (n + j) k w₁ w₂) := by
    have hsplit : ∀ j ∈ Finset.range (K + 1),
        sc j • (n + (j : ℂ)) • (L ^ j) (Y (n - 1 + j) k w₁ w₂)
          = n • (sc j • (L ^ j) (Y (n - 1 + j) k w₁ w₂))
            + (sc j * (j : ℂ)) • (L ^ j) (Y (n - 1 + j) k w₁ w₂) := by
      intro j _
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.smul_sum, hB2,
      ← sub_eq_add_neg]
  have hE : ∑ j ∈ Finset.range (K + 1),
        sc j • ((k : ℂ) + 1) • (L ^ j) (Y (n - 1 + j) (k + 1) w₁ w₂)
      = ((k : ℂ) + 1) • ∑ j ∈ Finset.range (K + 1),
          sc j • (L ^ j) (Y (n - 1 + j) (k + 1) w₁ w₂) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  rw [hA, hB, hE]
  module

/-- **`skewK 𝒴` is a logarithmic intertwining operator of type `(W₃ / W₂ W₁)`.** -/
theorem isLogIntertwining_skewK (hY : IsLogIntertwining A₁ A₂ A₃ Y) {c : ℂ → ℂ}
    (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0) :
    IsLogIntertwining A₂ A₁ A₃ (skewK A₃ c Y) := by
  refine ⟨fun w₂ w₁ n => ?_, fun w₂ w₁ n => ?_, fun w₂ n k => hY.skewK_L_neg_one hc w₂ n k, ?_⟩
  · -- polynomial in `log x`
    obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ n
    set J := N.toNat
    have hJ : ∀ j : ℕ, J ≤ j → ∀ k, Y (n + j) k w₁ w₂ = 0 := fun j hj k => hN (j : ℤ) (by omega) k
    have hK : ∀ j : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Y (n + j) k w₁ w₂ = 0 :=
      fun j => hY.logFinite w₁ w₂ (n + j)
    choose K hK using hK
    refine ⟨(Finset.range J).sup K, fun k hk => ?_⟩
    rw [hY.skewK_eq_sum c n k w₂ w₁ J (fun j hj => hJ j hj k)]
    rw [Finset.sum_eq_zero (fun j hj => ?_), smul_zero]
    rw [hK j k (le_trans (Finset.le_sup hj) hk), map_zero, smul_zero]
  · -- truncation, uniform in `k`
    obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ n
    refine ⟨N, fun m hm k => ?_⟩
    rw [hY.skewK_eq_sum c (n + m) k w₂ w₁ 0 (fun j _ => by
      rw [show n + (m : ℂ) + (j : ℂ) = n + ((m + j : ℤ) : ℂ) by push_cast; ring]
      exact hN _ (by omega) k)]
    simp
  · intro u w₂ w₁ ℓ m n k
    have h := S_skewModes_eq_zero (hY.trunc_comp k) (hY.S_comp_eq_zero k) hc hc0
      u w₂ w₁ ℓ m n
    rw [S, sub_eq_zero] at h
    exact h

end IsLogIntertwining

/-! ## The log shift `log x ↦ log x + a` -/

/-- Pointwise polynomiality in `log x`. -/
def LogFin (Y : LogModes M₁ M₂ M₃) : Prop :=
  ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Y n k w₁ w₂ = 0

/-- The coefficient `C(k,j) a^{k−j}` of the log shift. -/
noncomputable def shc (a : ℂ) (k j : ℕ) : ℂ := (k.choose j : ℂ) * a ^ (k - j)

/-- The `j`-th shifted coefficient, pointwise: `Σ_k C(k,j) a^{k−j} 𝒴_{n;k} w₁ w₂`. -/
noncomputable def shiftPt (a : ℂ) (Y : LogModes M₁ M₂ M₃) (n : ℂ) (j : ℕ) (w₁ : M₁)
    (w₂ : M₂) : M₃ :=
  ∑ᶠ k : ℕ, shc a k j • Y n k w₁ w₂

theorem shiftPt_eq_sum {a : ℂ} {Y : LogModes M₁ M₂ M₃} {n : ℂ} {j : ℕ} {w₁ : M₁} {w₂ : M₂}
    (K : ℕ) (hK : ∀ k : ℕ, K ≤ k → Y n k w₁ w₂ = 0) :
    shiftPt a Y n j w₁ w₂ = ∑ k ∈ Finset.range K, shc a k j • Y n k w₁ w₂ := by
  rw [shiftPt]
  refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
  rw [Function.mem_support] at hk
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hk (by rw [hK k (by omega), smul_zero])

/-- The bilinear map `(w₁, w₂) ↦ shiftPt`, for log-finite data. -/
noncomputable def shiftLin (a : ℂ) (Y : LogModes M₁ M₂ M₃) (hY : LogFin Y) (n : ℂ) (j : ℕ) :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃ :=
  LinearMap.mk₂ ℂ (fun w₁ w₂ => shiftPt a Y n j w₁ w₂)
    (fun w₁ w₁' w₂ => by
      dsimp only
      obtain ⟨K₁, h₁⟩ := hY w₁ w₂ n
      obtain ⟨K₂, h₂⟩ := hY w₁' w₂ n
      have h₃ : ∀ k : ℕ, K₁ + K₂ ≤ k → Y n k (w₁ + w₁') w₂ = 0 := fun k hk => by
        rw [map_add, LinearMap.add_apply, h₁ k (by omega), h₂ k (by omega), add_zero]
      rw [shiftPt_eq_sum (K₁ + K₂) h₃, shiftPt_eq_sum (K₁ + K₂) (fun k hk => h₁ k (by omega)),
        shiftPt_eq_sum (K₁ + K₂) (fun k hk => h₂ k (by omega)), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_add, LinearMap.add_apply, smul_add])
    (fun c w₁ w₂ => by
      dsimp only
      obtain ⟨K, h⟩ := hY w₁ w₂ n
      rw [shiftPt_eq_sum K (fun k hk => by rw [map_smul, LinearMap.smul_apply, h k hk, smul_zero]),
        shiftPt_eq_sum K h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, LinearMap.smul_apply, smul_comm])
    (fun w₁ w₂ w₂' => by
      dsimp only
      obtain ⟨K₁, h₁⟩ := hY w₁ w₂ n
      obtain ⟨K₂, h₂⟩ := hY w₁ w₂' n
      have h₃ : ∀ k : ℕ, K₁ + K₂ ≤ k → Y n k w₁ (w₂ + w₂') = 0 := fun k hk => by
        rw [map_add, h₁ k (by omega), h₂ k (by omega), add_zero]
      rw [shiftPt_eq_sum (K₁ + K₂) h₃, shiftPt_eq_sum (K₁ + K₂) (fun k hk => h₁ k (by omega)),
        shiftPt_eq_sum (K₁ + K₂) (fun k hk => h₂ k (by omega)), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_add, smul_add])
    (fun c w₁ w₂ => by
      dsimp only
      obtain ⟨K, h⟩ := hY w₁ w₂ n
      rw [shiftPt_eq_sum K (fun k hk => by rw [map_smul, h k hk, smul_zero]),
        shiftPt_eq_sum K h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, smul_comm])

open Classical in
/-- **The log shift** `log x ↦ log x + a`:
`(logShift a 𝒴)_{n;j} = Σ_{k} C(k,j) a^{k−j} 𝒴_{n;k}` (junk value `0` off log-finite data). -/
noncomputable def logShift (a : ℂ) (Y : LogModes M₁ M₂ M₃) : LogModes M₁ M₂ M₃ :=
  fun n j => if h : LogFin Y then shiftLin a Y h n j else 0

theorem logShift_apply {a : ℂ} {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) (n : ℂ) (j : ℕ)
    (w₁ : M₁) (w₂ : M₂) : logShift a Y n j w₁ w₂ = shiftPt a Y n j w₁ w₂ := by
  simp only [logShift, dif_pos hY, shiftLin, LinearMap.mk₂_apply]

theorem logShift_eq_sum {a : ℂ} {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) {n : ℂ} {j : ℕ}
    {w₁ : M₁} {w₂ : M₂} (K : ℕ) (hK : ∀ k : ℕ, K ≤ k → Y n k w₁ w₂ = 0) :
    logShift a Y n j w₁ w₂ = ∑ k ∈ Finset.range K, shc a k j • Y n k w₁ w₂ := by
  rw [logShift_apply hY, shiftPt_eq_sum K hK]

theorem shc_eq_zero {a : ℂ} {k j : ℕ} (h : k < j) : shc a k j = 0 := by
  simp [shc, Nat.choose_eq_zero_of_lt h]

/-- `(k+1)·C(k,j) a^{k−j} = (j+1)·C(k+1,j+1) a^{(k+1)−(j+1)}`. -/
theorem shc_succ (a : ℂ) (k j : ℕ) :
    ((k : ℂ) + 1) * shc a k j = ((j : ℂ) + 1) * shc a (k + 1) (j + 1) := by
  have h := Nat.add_one_mul_choose_eq k j
  have hC : ((k : ℂ) + 1) * (k.choose j : ℂ) = ((k + 1).choose (j + 1) : ℂ) * ((j : ℂ) + 1) := by
    exact_mod_cast h
  rw [shc, shc, show k + 1 - (j + 1) = k - j by omega]
  linear_combination (a ^ (k - j)) * hC

namespace IsLogIntertwining

variable {Y : LogModes M₁ M₂ M₃}

theorem logFin (hY : IsLogIntertwining A₁ A₂ A₃ Y) : LogFin Y := hY.logFinite

/-- **The log shift preserves logarithmic intertwining operators.** -/
theorem isLogIntertwining_logShift (hY : IsLogIntertwining A₁ A₂ A₃ Y) (a : ℂ) :
    IsLogIntertwining A₁ A₂ A₃ (logShift a Y) := by
  have hF := hY.logFin
  refine ⟨fun w₁ w₂ n => ?_, fun w₁ w₂ n => ?_, fun w₁ n j => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hY.logFinite w₁ w₂ n
    refine ⟨K, fun j hj => ?_⟩
    rw [logShift_eq_sum hF K hK]
    exact Finset.sum_eq_zero fun k hk => by
      rw [shc_eq_zero (by rw [Finset.mem_range] at hk; omega), zero_smul]
  · obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ n
    refine ⟨N, fun m hm j => ?_⟩
    rw [logShift_eq_sum hF 0 (fun k _ => hN m hm k)]
    simp
  · -- `L(−1)`-derivative
    refine LinearMap.ext fun w₂ => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    obtain ⟨K, hK⟩ := hY.logFinite w₁ w₂ (n - 1)
    have hL : ∀ k : ℕ, Y n k (Lm1 A₁ w₁) w₂
        = (-n) • Y (n - 1) k w₁ w₂ + ((k : ℂ) + 1) • Y (n - 1) (k + 1) w₁ w₂ := by
      intro k
      have := congrArg (fun F => F w₂) (hY.L_neg_one w₁ n k)
      simpa only [LinearMap.add_apply, LinearMap.smul_apply] using this
    rw [logShift_eq_sum hF (K + 1) (fun k hk => by
        rw [hL, hK k (by omega), hK (k + 1) (by omega), smul_zero, smul_zero, add_zero]),
      logShift_eq_sum hF (K + 1) (fun k hk => hK k (by omega)),
      logShift_eq_sum hF (K + 2) (fun k hk => hK k (by omega))]
    simp only [hL, smul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_comm]
    · rw [Finset.sum_range_succ' (fun k => shc a k (j + 1) • Y (n - 1) k w₁ w₂),
        shc_eq_zero (Nat.succ_pos j), zero_smul, add_zero, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, smul_smul, mul_comm (shc a k j), shc_succ]
  · -- Jacobi identity
    intro u w₁ w₂ ℓ m n j
    -- the `i`-range
    obtain ⟨N₁, hN₁⟩ := hY.truncation w₁ w₂ n
    obtain ⟨N₂, hN₂⟩ := A₂.truncation u w₂
    obtain ⟨N₃, hN₃⟩ := A₁.truncation u w₁
    set R : ℕ := N₁.toNat + (N₂ - m).toNat + (N₃ - ℓ).toNat
    -- the `k`-range
    have hb : ∀ i : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        Y (n + i) k w₁ w₂ = 0 ∧ Y (ℓ + n - i) k w₁ (mode (A₂.YM u) (m + i) w₂) = 0 ∧
          Y (m + n - i) k (mode (A₁.YM u) (ℓ + i) w₁) w₂ = 0 := by
      intro i
      obtain ⟨K₁, h₁⟩ := hY.logFinite w₁ w₂ (n + i)
      obtain ⟨K₂, h₂⟩ := hY.logFinite w₁ (mode (A₂.YM u) (m + i) w₂) (ℓ + n - i)
      obtain ⟨K₃, h₃⟩ := hY.logFinite (mode (A₁.YM u) (ℓ + i) w₁) w₂ (m + n - i)
      exact ⟨K₁ + K₂ + K₃, fun k hk => ⟨h₁ k (by omega), h₂ k (by omega), h₃ k (by omega)⟩⟩
    choose Kf hKf using hb
    set K : ℕ := (Finset.range R).sup Kf
    have hKi : ∀ i : ℕ, i < R → ∀ k : ℕ, K ≤ k →
        Y (n + i) k w₁ w₂ = 0 ∧ Y (ℓ + n - i) k w₁ (mode (A₂.YM u) (m + i) w₂) = 0 ∧
          Y (m + n - i) k (mode (A₁.YM u) (ℓ + i) w₁) w₂ = 0 := fun i hi k hk =>
      hKf i k (le_trans (Finset.le_sup (Finset.mem_range.mpr hi)) hk)
    -- termwise expansion of the left summand
    have hLt : ∀ i : ℤ,
        (negOnePow i * cbz ℓ i) • (mode (A₃.YM u) (ℓ + m - i) (logShift a Y (n + i) j w₁ w₂)
          - negOnePow ℓ • logShift a Y (ℓ + n - i) j w₁ (mode (A₂.YM u) (m + i) w₂))
        = ∑ k ∈ Finset.range K, shc a k j • IsLogIntertwining.jacL A₂ A₃ Y u w₁ w₂ ℓ m n k i := by
      intro i
      rcases lt_or_ge i 0 with hi | hi
      · simp [jacL, cbz_apply_neg ℓ hi]
      obtain ⟨i, rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
      by_cases hiR : i < R
      · have e1 := logShift_eq_sum (a := a) (j := j) hF K (fun k hk => (hKi i hiR k hk).1)
        have e2 := logShift_eq_sum (a := a) (j := j) hF K (fun k hk => (hKi i hiR k hk).2.1)
        simp only [Int.cast_natCast] at e1 e2 ⊢
        rw [e1, e2, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [jacL, Int.cast_natCast, map_smul]
        rw [smul_comm (negOnePow ℓ), ← smul_sub, smul_comm]
      · have z1 : ∀ k, Y (n + i) k w₁ w₂ = 0 := fun k => hN₁ i (by omega) k
        have z2 : mode (A₂.YM u) (m + i) w₂ = 0 := hN₂ _ (by omega)
        have e1 := logShift_eq_sum (a := a) (j := j) hF 0 (fun k _ => z1 k)
        simp only [Int.cast_natCast] at e1 ⊢
        rw [e1, z2, map_zero, Finset.sum_range_zero, map_zero, smul_zero, sub_zero, smul_zero]
        symm
        refine Finset.sum_eq_zero fun k _ => ?_
        simp only [jacL, Int.cast_natCast, z1 k, z2, map_zero, smul_zero, sub_zero]
    have hRt : ∀ i : ℤ,
        cbz m i • logShift a Y (m + n - i) j (mode (A₁.YM u) (ℓ + i) w₁) w₂
        = ∑ k ∈ Finset.range K, shc a k j • IsLogIntertwining.jacR A₁ Y u w₁ w₂ ℓ m n k i := by
      intro i
      rcases lt_or_ge i 0 with hi | hi
      · simp [jacR, cbz_apply_neg m hi]
      obtain ⟨i, rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, by omega⟩
      by_cases hiR : i < R
      · have e3 := logShift_eq_sum (a := a) (j := j) hF K (fun k hk => (hKi i hiR k hk).2.2)
        simp only [Int.cast_natCast] at e3 ⊢
        rw [e3, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [jacR, Int.cast_natCast]
        rw [smul_comm]
      · have z3 : mode (A₁.YM u) (ℓ + i) w₁ = 0 := hN₃ _ (by omega)
        simp only [Int.cast_natCast]
        rw [z3, map_zero, LinearMap.zero_apply, smul_zero]
        symm
        refine Finset.sum_eq_zero fun k _ => ?_
        simp only [jacR, Int.cast_natCast, z3, map_zero, LinearMap.zero_apply, smul_zero]
    have fin_smul : ∀ (f : ℤ → M₃) (c : ℂ), (Function.support f).Finite →
        (Function.support fun i => c • f i).Finite := fun f c hf =>
      hf.subset fun i hi => by
        simp only [Function.mem_support] at hi ⊢
        intro h; exact hi (by rw [h, smul_zero])
    rw [finsum_congr hLt, finsum_congr hRt,
      finsum_sum_comm (Finset.range K)
        (fun i k => shc a k j • IsLogIntertwining.jacL A₂ A₃ Y u w₁ w₂ ℓ m n k i)
        (fun k _ => fin_smul _ _ (IsLogIntertwining.jacL_support_finite hY.truncation
          u w₁ w₂ ℓ m n k)),
      finsum_sum_comm (Finset.range K)
        (fun i k => shc a k j • IsLogIntertwining.jacR A₁ Y u w₁ w₂ ℓ m n k i)
        (fun k _ => fin_smul _ _ (IsLogIntertwining.jacR_support_finite (A₁ := A₁) Y
          u w₁ w₂ ℓ m n k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← smul_finsum' _ (IsLogIntertwining.jacL_support_finite hY.truncation u w₁ w₂ ℓ m n k),
      ← smul_finsum' _ (IsLogIntertwining.jacR_support_finite (A₁ := A₁) Y u w₁ w₂ ℓ m n k)]
    exact congrArg (shc a k j • ·) (hY.jacobi u w₁ w₂ ℓ m n k)

end IsLogIntertwining

/-! ## HLZ's `Ω_r` -/

/-- The phase `c_r(n) = e^{−(2r+1)πi(n+1)}` of `x ↦ e^{(2r+1)πi} x` on `x^{−n−1}`. -/
noncomputable def omegaPhase (r : ℤ) (n : ℂ) : ℂ :=
  Complex.exp (-((2 * r + 1 : ℂ) * (Real.pi * Complex.I)) * (n + 1))

theorem omegaPhase_succ (r : ℤ) (n : ℂ) : omegaPhase r (n + 1) = -omegaPhase r n := by
  rw [omegaPhase, omegaPhase, show -((2 * (r : ℂ) + 1) * (↑Real.pi * Complex.I)) * (n + 1 + 1)
      = -((2 * (r : ℂ) + 1) * (↑Real.pi * Complex.I)) * (n + 1)
        + ((-r - 1 : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) + (↑Real.pi * Complex.I) by
          push_cast; ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I]
  ring

theorem omegaPhase_ne_zero (r : ℤ) (n : ℂ) : omegaPhase r n ≠ 0 := Complex.exp_ne_zero _

/-- **HLZ's skew-symmetry operator** `Ω_r(𝒴)(w₂, x)w₁ = e^{xL(−1)} 𝒴(w₁, e^{(2r+1)πi}x) w₂`:
the per-log-degree skew with phase `e^{−(2r+1)πi(n+1)}`, followed by the log shift
`log x ↦ log x + (2r+1)πi`. -/
noncomputable def omega (A₃ : WeakModule W M₃) (r : ℤ) (Y : LogModes M₁ M₂ M₃) :
    LogModes M₂ M₁ M₃ :=
  logShift ((2 * r + 1 : ℂ) * (Real.pi * Complex.I)) (skewK A₃ (omegaPhase r) Y)

/-- **Skew-symmetry for logarithmic intertwining operators** (HLZ II §3): `Ω_r(𝒴)` is a
logarithmic intertwining operator of type `(W₃ / W₂ W₁)` for every `r ∈ ℤ`, for arbitrary weak
modules. -/
theorem IsLogIntertwining.isLogIntertwining_omega {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁ A₂ A₃ Y) (r : ℤ) :
    IsLogIntertwining A₂ A₁ A₃ (omega A₃ r Y) :=
  (hY.isLogIntertwining_skewK (omegaPhase_succ r) (omegaPhase_ne_zero r)).isLogIntertwining_logShift _

end VOA.LogTensor
