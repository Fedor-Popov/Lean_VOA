/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorSkew

/-!
# `Ω_{−r−1} ∘ Ω_r = id`; the skew-symmetry isomorphism of fusion spaces — T1b

For logarithmic intertwining operators among weak modules (HLZ II Def. 3.10):

* `logShift_zero`, `logShift_logShift` (`log x ↦ log x + b ↦ log x + a + b`, via the binomial
  identity `shc_sum`), `logShift_add`, `logShift_smul`;
* `skewK_skewK` (`Ω_{c'} ∘ Ω_c = id` per log degree when `c' c = 1`) and
  `skewK_logShift` (the per-degree skew commutes with the log shift);
* `omega_omega` — **`Ω_{−r−1}(Ω_r(𝒴)) = 𝒴`** (HLZ II §3);
* `omegaEquiv r : LogIntertwiningOperator A₁ A₂ A₃ ≃ₗ[ℂ] LogIntertwiningOperator A₂ A₁ A₃`
  and `logFusionRule_swap : N^{W₃}_{W₂W₁} = N^{W₃}_{W₁W₂}` for **all** weak modules
  (finite-dimensional or not: both sides are `finrank`s of isomorphic spaces).

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

/-! ## Linearity of the FHL skew operator (from `VOA/Huang/BraidingSkewJacobi.lean`) -/

theorem trunc_add' {Y Y' : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (hY' : Trunc Y') :
    Trunc (Y + Y') := by
  intro w₁ w₂ n
  obtain ⟨N, hN⟩ := hY w₁ w₂ n
  obtain ⟨N', hN'⟩ := hY' w₁ w₂ n
  refine ⟨max N N', fun k hk => ?_⟩
  simp only [Pi.add_apply, LinearMap.add_apply, hN k (le_trans (le_max_left _ _) hk),
    hN' k (le_trans (le_max_right _ _) hk), add_zero]

theorem trunc_smul' {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (a : ℂ) :
    Trunc (a • Y) := by
  intro w₁ w₂ n
  obtain ⟨N, hN⟩ := hY w₁ w₂ n
  exact ⟨N, fun k hk => by simp only [Pi.smul_apply, LinearMap.smul_apply, hN k hk, smul_zero]⟩

theorem skewModes_add' (L : End ℂ M₃) (c : ℂ → ℂ) {Y Y' : IntertwiningModes M₁ M₂ M₃}
    (hY : Trunc Y) (hY' : Trunc Y') :
    skewModes L c (Y + Y') = skewModes L c Y + skewModes L c Y' := by
  funext n
  refine LinearMap.ext fun w₂ => LinearMap.ext fun w₁ => ?_
  simp only [Pi.add_apply, LinearMap.add_apply]
  rw [skewModes_apply (trunc_add' hY hY'), skewModes_apply hY, skewModes_apply hY', ← smul_add]
  congr 1
  obtain ⟨K, hK⟩ := hY.bound w₁ w₂ n
  obtain ⟨K', hK'⟩ := hY'.bound w₁ w₂ n
  rw [sSum_eq_sum (K + K') (fun j hj => by
      simp only [Pi.add_apply, LinearMap.add_apply, hK j (by omega), hK' j (by omega), add_zero]),
    sSum_eq_sum (K + K') (fun j hj => hK j (by omega)),
    sSum_eq_sum (K + K') (fun j hj => hK' j (by omega)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sTerm, Pi.add_apply, LinearMap.add_apply, map_add, smul_add]

theorem skewModes_smul' (L : End ℂ M₃) (c : ℂ → ℂ) {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : Trunc Y) (a : ℂ) : skewModes L c (a • Y) = a • skewModes L c Y := by
  funext n
  refine LinearMap.ext fun w₂ => LinearMap.ext fun w₁ => ?_
  simp only [Pi.smul_apply, LinearMap.smul_apply]
  rw [skewModes_apply (trunc_smul' hY a), skewModes_apply hY, smul_comm a]
  congr 1
  obtain ⟨K, hK⟩ := hY.bound w₁ w₂ n
  rw [sSum_eq_sum K (fun j hj => by
      simp only [Pi.smul_apply, LinearMap.smul_apply, hK j hj, smul_zero]),
    sSum_eq_sum K hK, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sTerm, Pi.smul_apply, LinearMap.smul_apply, map_smul]
  rw [smul_comm]

/-! ## The log shift: group law and linearity -/

theorem logFin_logShift {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) (a : ℂ) :
    LogFin (logShift a Y) := by
  intro w₁ w₂ n
  obtain ⟨K, hK⟩ := hY w₁ w₂ n
  refine ⟨K, fun j hj => ?_⟩
  rw [logShift_eq_sum hY K hK]
  exact Finset.sum_eq_zero fun k hk => by
    rw [shc_eq_zero (by rw [Finset.mem_range] at hk; omega), zero_smul]

theorem logShift_zero {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) : logShift 0 Y = Y := by
  funext n j
  refine LinearMap.ext fun w₁ => LinearMap.ext fun w₂ => ?_
  obtain ⟨K, hK⟩ := hY w₁ w₂ n
  rw [logShift_eq_sum hY (K + j + 1) (fun k hk => hK k (by omega)),
    Finset.sum_eq_single j]
  · simp [shc]
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with h | h
    · rw [shc_eq_zero h, zero_smul]
    · rw [shc, zero_pow (by omega), mul_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The binomial identity `Σ_k C(k,j)a^{k−j} C(l,k)b^{l−k} = C(l,j)(a+b)^{l−j}`. -/
theorem shc_sum (a b : ℂ) (l j : ℕ) :
    ∑ k ∈ Finset.range (l + 1), shc a k j * shc b l k = shc (a + b) l j := by
  rcases lt_or_ge l j with hlj | hjl
  · rw [shc_eq_zero hlj]
    exact Finset.sum_eq_zero fun k hk => by
      rw [shc_eq_zero (by rw [Finset.mem_range] at hk; omega), zero_mul]
  · obtain ⟨d, rfl⟩ : ∃ d, l = j + d := ⟨l - j, by omega⟩
    rw [show j + d + 1 = j + (d + 1) by ring, Finset.sum_range_add,
      Finset.sum_eq_zero (fun k hk => by
        rw [shc_eq_zero (by rw [Finset.mem_range] at hk; omega), zero_mul]), zero_add]
    have hterm : ∀ i ∈ Finset.range (d + 1), shc a (j + i) j * shc b (j + d) (j + i)
        = ((j + d).choose j : ℂ) * (a ^ i * b ^ (d - i) * (d.choose i : ℂ)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hcm := Nat.choose_mul (n := j + d) (k := j + i) (s := j) (by omega)
      have hcm' : ((j + d).choose (j + i) : ℂ) * ((j + i).choose j : ℂ)
          = ((j + d).choose j : ℂ) * (d.choose i : ℂ) := by
        rw [show j + d - j = d by omega, show j + i - j = i by omega] at hcm
        exact_mod_cast hcm
      rw [shc, shc, show j + i - j = i by omega, show j + d - (j + i) = d - i by omega]
      linear_combination (a ^ i * b ^ (d - i)) * hcm'
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow, shc,
      show j + d - j = d by omega]

theorem logShift_logShift {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) (a b : ℂ) :
    logShift a (logShift b Y) = logShift (a + b) Y := by
  funext n j
  refine LinearMap.ext fun w₁ => LinearMap.ext fun w₂ => ?_
  obtain ⟨K, hK⟩ := hY w₁ w₂ n
  have hK' : ∀ k : ℕ, K ≤ k → logShift b Y n k w₁ w₂ = 0 := fun k hk => by
    rw [logShift_eq_sum hY K hK]
    exact Finset.sum_eq_zero fun l hl => by
      rw [shc_eq_zero (by rw [Finset.mem_range] at hl; omega), zero_smul]
  rw [logShift_eq_sum (logFin_logShift hY b) K hK', logShift_eq_sum hY K hK]
  simp only [logShift_eq_sum hY K hK, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [Finset.mem_range] at hl
  rw [← shc_sum a b l j]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show l + 1 ≤ K by omega))
    (fun k _ hk => by
      rw [Finset.mem_range] at hk
      rw [shc_eq_zero (show l < k by omega), mul_zero])]

theorem logFin_add {Y Y' : LogModes M₁ M₂ M₃} (hY : LogFin Y) (hY' : LogFin Y') :
    LogFin (Y + Y') := by
  intro w₁ w₂ n
  obtain ⟨K, hK⟩ := hY w₁ w₂ n
  obtain ⟨K', hK'⟩ := hY' w₁ w₂ n
  exact ⟨K + K', fun k hk => by
    simp only [Pi.add_apply, LinearMap.add_apply, hK k (by omega), hK' k (by omega), add_zero]⟩

theorem logFin_smul {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) (c : ℂ) : LogFin (c • Y) := by
  intro w₁ w₂ n
  obtain ⟨K, hK⟩ := hY w₁ w₂ n
  exact ⟨K, fun k hk => by simp only [Pi.smul_apply, LinearMap.smul_apply, hK k hk, smul_zero]⟩

theorem logShift_add {Y Y' : LogModes M₁ M₂ M₃} (hY : LogFin Y) (hY' : LogFin Y') (a : ℂ) :
    logShift a (Y + Y') = logShift a Y + logShift a Y' := by
  funext n j
  refine LinearMap.ext fun w₁ => LinearMap.ext fun w₂ => ?_
  obtain ⟨K, hK⟩ := hY w₁ w₂ n
  obtain ⟨K', hK'⟩ := hY' w₁ w₂ n
  simp only [Pi.add_apply, LinearMap.add_apply]
  rw [logShift_eq_sum (logFin_add hY hY') (K + K') (fun k hk => by
      simp only [Pi.add_apply, LinearMap.add_apply, hK k (by omega), hK' k (by omega), add_zero]),
    logShift_eq_sum hY (K + K') (fun k hk => hK k (by omega)),
    logShift_eq_sum hY' (K + K') (fun k hk => hK' k (by omega)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, LinearMap.add_apply, smul_add]

theorem logShift_smul {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y) (a c : ℂ) :
    logShift a (c • Y) = c • logShift a Y := by
  funext n j
  refine LinearMap.ext fun w₁ => LinearMap.ext fun w₂ => ?_
  obtain ⟨K, hK⟩ := hY w₁ w₂ n
  simp only [Pi.smul_apply, LinearMap.smul_apply]
  rw [logShift_eq_sum (logFin_smul hY c) K (fun k hk => by
      simp only [Pi.smul_apply, LinearMap.smul_apply, hK k hk, smul_zero]),
    logShift_eq_sum hY K hK, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, LinearMap.smul_apply]
  rw [smul_comm]

/-! ## The per-degree skew: involutivity, commutation with the log shift, linearity -/

namespace IsLogIntertwining

variable {Y : LogModes M₁ M₂ M₃}

/-- `skewK_{c'} ∘ skewK_c = id` when `c' n · c n = 1`. -/
theorem skewK_skewK (hY : IsLogIntertwining A₁ A₂ A₃ Y) {c c' : ℂ → ℂ}
    (hc : ∀ n, c (n + 1) = -c n) (hcc : ∀ n, c' n * c n = 1) :
    skewK A₃ c' (skewK A₃ c Y) = Y := by
  funext n k
  have h : comp (skewK A₃ c Y) k = skewModes (Lm1 A₃) c (comp Y k) := rfl
  change skewModes (Lm1 A₃) c' (comp (skewK A₃ c Y) k) n = Y n k
  rw [h, skewModes_skewModes hc hcc (hY.trunc_comp k)]
  rfl

/-- The per-degree skew commutes with the log shift. -/
theorem skewK_logShift (hY : IsLogIntertwining A₁ A₂ A₃ Y) {c : ℂ → ℂ}
    (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0) (a : ℂ) :
    skewK A₃ c (logShift a Y) = logShift a (skewK A₃ c Y) := by
  have hS := hY.isLogIntertwining_logShift a
  have hK' := hY.isLogIntertwining_skewK hc hc0
  funext n j
  refine LinearMap.ext fun w₂ => LinearMap.ext fun w₁ => ?_
  obtain ⟨N, hN⟩ := hY.truncation w₁ w₂ n
  set J := N.toNat
  have hJ : ∀ t : ℕ, J ≤ t → ∀ k, Y (n + t) k w₁ w₂ = 0 := fun t ht k =>
    hN (t : ℤ) (by omega) k
  have hb : ∀ t : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Y (n + t) k w₁ w₂ = 0 :=
    fun t => hY.logFinite w₁ w₂ (n + t)
  choose Kf hKf using hb
  set K := (Finset.range J).sup Kf
  have hKt : ∀ t : ℕ, t < J → ∀ k : ℕ, K ≤ k → Y (n + t) k w₁ w₂ = 0 := fun t ht k hk =>
    hKf t k (le_trans (Finset.le_sup (Finset.mem_range.mpr ht)) hk)
  -- left side
  rw [hS.skewK_eq_sum c n j w₂ w₁ J (fun t ht => by
    rw [logShift_eq_sum hY.logFin 0 (fun k _ => hJ t ht k)]; simp)]
  have hL : ∀ t ∈ Finset.range J, sc t • (Lm1 A₃ ^ t) (logShift a Y (n + t) j w₁ w₂)
      = ∑ k ∈ Finset.range K, (sc t * shc a k j) • (Lm1 A₃ ^ t) (Y (n + t) k w₁ w₂) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [logShift_eq_sum hY.logFin K (hKt t ht), map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_smul]
  rw [Finset.sum_congr rfl hL]
  -- right side
  have hR0 : ∀ k : ℕ, K ≤ k → skewK A₃ c Y n k w₂ w₁ = 0 := fun k hk => by
    rw [hY.skewK_eq_sum c n k w₂ w₁ J (fun t ht => hJ t ht k)]
    rw [Finset.sum_eq_zero (fun t ht => by
      rw [hKt t (Finset.mem_range.mp ht) k hk, map_zero, smul_zero]), smul_zero]
  rw [logShift_eq_sum hK'.logFin K hR0]
  have hR : ∀ k ∈ Finset.range K, shc a k j • skewK A₃ c Y n k w₂ w₁
      = c n • ∑ t ∈ Finset.range J, (sc t * shc a k j) • (Lm1 A₃ ^ t) (Y (n + t) k w₁ w₂) := by
    intro k _
    rw [hY.skewK_eq_sum c n k w₂ w₁ J (fun t ht => hJ t ht k), Finset.smul_sum,
      Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_comm (shc a k j), smul_smul (shc a k j), mul_comm (shc a k j)]
  rw [Finset.sum_congr rfl hR, ← Finset.smul_sum, Finset.sum_comm]

end IsLogIntertwining

theorem skewK_add {Y Y' : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y)
    (hY' : IsLogIntertwining A₁ A₂ A₃ Y') (c : ℂ → ℂ) :
    skewK A₃ c (Y + Y') = skewK A₃ c Y + skewK A₃ c Y' := by
  funext n k
  change skewModes (Lm1 A₃) c (comp Y k + comp Y' k) n = _
  rw [skewModes_add' _ c (hY.trunc_comp k) (hY'.trunc_comp k)]
  rfl

theorem skewK_smul {Y : LogModes M₁ M₂ M₃} (hY : IsLogIntertwining A₁ A₂ A₃ Y) (c : ℂ → ℂ)
    (a : ℂ) : skewK A₃ c (a • Y) = a • skewK A₃ c Y := by
  funext n k
  change skewModes (Lm1 A₃) c (a • comp Y k) n = _
  rw [skewModes_smul' _ c (hY.trunc_comp k)]
  rfl

/-! ## `Ω_{−r−1} ∘ Ω_r = id` and the isomorphism -/

theorem omegaPhase_mul (r : ℤ) (n : ℂ) : omegaPhase (-r - 1) n * omegaPhase r n = 1 := by
  rw [omegaPhase, omegaPhase, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  push_cast
  ring

/-- **`Ω_{−r−1}(Ω_r(𝒴)) = 𝒴`** (HLZ II §3). -/
theorem IsLogIntertwining.omega_omega {Y : LogModes M₁ M₂ M₃}
    (hY : IsLogIntertwining A₁ A₂ A₃ Y) (r : ℤ) :
    omega A₃ (-r - 1) (omega A₃ r Y) = Y := by
  have hK := hY.isLogIntertwining_skewK (omegaPhase_succ r) (omegaPhase_ne_zero r)
  rw [omega, omega, hK.skewK_logShift (omegaPhase_succ (-r - 1)) (omegaPhase_ne_zero (-r - 1)),
    hY.skewK_skewK (omegaPhase_succ r) (omegaPhase_mul r),
    logShift_logShift hY.logFin]
  rw [show (2 * (((-r - 1 : ℤ)) : ℂ) + 1) * (↑Real.pi * Complex.I)
      + (2 * (r : ℂ) + 1) * (↑Real.pi * Complex.I) = 0 by push_cast; ring]
  exact logShift_zero hY.logFin

/-- `Ω_r` as a linear map between spaces of logarithmic intertwining operators. -/
noncomputable def omegaMap (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) (r : ℤ) :
    LogIntertwiningOperator A₁ A₂ A₃ →ₗ[ℂ] LogIntertwiningOperator A₂ A₁ A₃ where
  toFun Y := ⟨omega A₃ r Y, Y.2.isLogIntertwining_omega r⟩
  map_add' Y Y' := by
    apply Subtype.ext
    change omega A₃ r ((Y : LogModes M₁ M₂ M₃) + (Y' : LogModes M₁ M₂ M₃))
      = omega A₃ r (Y : LogModes M₁ M₂ M₃) + omega A₃ r (Y' : LogModes M₁ M₂ M₃)
    have hc := omegaPhase_succ r
    have hc0 := omegaPhase_ne_zero r
    rw [omega, omega, omega, skewK_add Y.2 Y'.2,
      logShift_add (Y.2.isLogIntertwining_skewK hc hc0).logFin
        (Y'.2.isLogIntertwining_skewK hc hc0).logFin]
  map_smul' a Y := by
    apply Subtype.ext
    change omega A₃ r (a • (Y : LogModes M₁ M₂ M₃)) = a • omega A₃ r (Y : LogModes M₁ M₂ M₃)
    rw [omega, omega, skewK_smul Y.2,
      logShift_smul (Y.2.isLogIntertwining_skewK (omegaPhase_succ r) (omegaPhase_ne_zero r)).logFin]

/-- **The skew-symmetry isomorphism** `Ω_r` (HLZ II §3), inverse `Ω_{−r−1}`:
`LogIntertwiningOperator A₁ A₂ A₃ ≃ₗ[ℂ] LogIntertwiningOperator A₂ A₁ A₃`, for arbitrary weak
modules. -/
noncomputable def omegaEquiv (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) (r : ℤ) :
    LogIntertwiningOperator A₁ A₂ A₃ ≃ₗ[ℂ] LogIntertwiningOperator A₂ A₁ A₃ :=
  { omegaMap A₁ A₂ A₃ r with
    invFun := omegaMap A₂ A₁ A₃ (-r - 1)
    left_inv := fun Y => Subtype.ext (Y.2.omega_omega r)
    right_inv := fun Y => by
      apply Subtype.ext
      have h := Y.2.omega_omega (-r - 1)
      rw [show -(-r - 1) - 1 = r by ring] at h
      exact h }

/-- **`N^{W₃}_{W₂W₁} = N^{W₃}_{W₁W₂}`** for logarithmic fusion rules of arbitrary weak
modules. -/
theorem logFusionRule_swap (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)
    (A₃ : WeakModule W M₃) : logFusionRule A₂ A₁ A₃ = logFusionRule A₁ A₂ A₃ :=
  (omegaEquiv A₁ A₂ A₃ 0).finrank_eq.symm

end VOA.LogTensor
