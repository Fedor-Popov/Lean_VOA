/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.Intertwining
import VOA.Moonshine.SkewIntertwiner

/-!
# Skew-symmetry operator on mode data over WEAK modules — T1b (port, part 1)

A port of `VOA/Huang/BraidingSkew.lean` (FHL Prop. 5.4.7, mode form) from `OrdVModule` to
`WeakModule`: the original uses only the vertex operators `YM` and lower truncation of the
modules, never the `L₀`-eigenspace grading.  Changes: `WeakModule W ↦ WeakModule W`,
`Lm1 A.toWeakModule ↦ Lm1 A`; the three declarations that mention `IsIntertwiningOperator`
(`trunc_of_isIntertwining`, `Y_Lm1_right`, `skewModes_L_neg_one`) are dropped — their logarithmic
replacements are in `Modules/LogTensorSkew.lean`.  Everything else (the operator `skewModes`
`Ω_c(𝒴)₍ₙ₎(w₂)w₁ = c n · Σ_{j ≥ 0} ((−1)ʲ/j!) L₋₁ʲ 𝒴₍ₙ₊ⱼ₎(w₁)w₂`, `skewModes_skewModes`, the
Jacobi sums `JL`, `JR`, `S`, the Pascal recurrences and `eq_zero_of_boundaries`) is verbatim.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.LogSkew

open VOA VOA.SkewIntertwiner
open Module (End)
open scoped BigOperators

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Elementary combinatorics -/

/-- `Σ_{j ≤ N} (−1)^j / (j! (N−j)!) = δ_{N,0}`. -/
theorem alt_inv_fact (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * ((N - j).factorial : ℂ)⁻¹)
      = if N = 0 then 1 else 0 := by
  have key : ∀ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j
      * ((j.factorial : ℂ)⁻¹ * ((N - j).factorial : ℂ)⁻¹)
      = (N.factorial : ℂ)⁻¹ * (((-1 : ℤ) ^ j * (N.choose j : ℤ) : ℤ) : ℂ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hc := Nat.choose_mul_factorial_mul_factorial (show j ≤ N by omega)
    have hN : ((N.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    have hj' : ((j.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hNj : (((N - j).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N - j)
    have hc' : ((N.choose j : ℂ)) * (j.factorial : ℂ) * ((N - j).factorial : ℂ)
        = (N.factorial : ℂ) := by exact_mod_cast hc
    have hC : ((N.choose j : ℂ)) = (N.factorial : ℂ) * ((j.factorial : ℂ)⁻¹
        * ((N - j).factorial : ℂ)⁻¹) := by
      field_simp
      linear_combination hc'
    push_cast
    rw [hC]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Int.cast_sum,
    Int.alternating_sum_range_choose]
  split_ifs with h
  · subst h; simp
  · simp

/-- The triangle sum `Σ_{j+i ≤ w} (−1)^j/(j! i!) T(i+j) = T 0`. -/
theorem triangle_sum {X : Type*} [AddCommGroup X] [Module ℂ X] (w : ℕ) (T : ℕ → X) :
    ∑ j ∈ Finset.range (w + 1), ∑ i ∈ Finset.range (w - j + 1),
      ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹)) • T (i + j) = T 0 := by
  have h1 : ∀ j ∈ Finset.range (w + 1), ∑ i ∈ Finset.range (w - j + 1),
      ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹)) • T (i + j)
      = ∑ N ∈ Finset.Ico j (w + 1),
          ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * ((N - j).factorial : ℂ)⁻¹)) • T N := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.sum_Ico_eq_sum_range, show w + 1 - j = w - j + 1 by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show j + i - j = i by omega, add_comm i j]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Finset.range (w + 1)) (s' := fun N => Finset.range (N + 1))
    (fun j N => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have h2 : ∀ N ∈ Finset.range (w + 1), ∑ j ∈ Finset.range (N + 1),
      ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * ((N - j).factorial : ℂ)⁻¹)) • T N
      = (if N = 0 then (1 : ℂ) else 0) • T N := by
    intro N _
    rw [← Finset.sum_smul, alt_inv_fact]
  rw [Finset.sum_congr rfl h2, Finset.sum_eq_single 0 (fun N _ hN => by rw [if_neg hN, zero_smul])
    (fun h => absurd (Finset.mem_range.2 (Nat.succ_pos w)) h), if_pos rfl, one_smul]

/-- The coefficient `(−1)ʲ / j!` of `e^{−xL₋₁}`. -/
noncomputable def sc (j : ℕ) : ℂ := (j.factorial : ℂ)⁻¹ * (-1) ^ j

theorem sc_succ_mul (j : ℕ) : sc (j + 1) * ((j : ℂ) + 1) = - sc j := by
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hf : (((j + 1).factorial : ℂ)) = ((j : ℂ) + 1) * (j.factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [sc, sc, hf, pow_succ]
  field_simp

/-! ## Phases -/

section Phase

variable {c : ℂ → ℂ}

theorem phase_nat (hc : ∀ n, c (n + 1) = -c n) (n : ℂ) (j : ℕ) :
    c (n + j) = (-1) ^ j * c n := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show n + ((j + 1 : ℕ) : ℂ) = (n + j) + 1 by push_cast; ring, hc, ih, pow_succ]
      ring

theorem phase_int (hc : ∀ n, c (n + 1) = -c n) (n : ℂ) (k : ℤ) :
    c (n + k) = negOnePow k * c n := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by omega⟩
    rw [Int.cast_natCast, phase_nat hc, negOnePow_natCast]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -(j : ℤ) := ⟨(-k).toNat, by omega⟩
    have h := phase_nat hc (n + ((-(j : ℤ) : ℤ) : ℂ)) j
    rw [show n + ((-(j : ℤ) : ℤ) : ℂ) + (j : ℂ) = n by push_cast; ring] at h
    rw [VertexOperatorAlgebra.negOnePow_neg', negOnePow_natCast, h, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul]
    norm_num

end Phase

/-! ## The skew operator -/

section Skew

variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]

/-- **Truncation** of mode data (the first FHL axiom, as a predicate). -/
def Trunc (Y : IntertwiningModes M₁ M₂ M₃) : Prop :=
  ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) w₁ w₂ = 0

theorem Trunc.bound {Y : IntertwiningModes M₁ M₂ M₃} (h : Trunc Y) (w₁ : M₁) (w₂ : M₂)
    (n : ℂ) : ∃ K : ℕ, ∀ j : ℕ, K ≤ j → Y (n + j) w₁ w₂ = 0 := by
  obtain ⟨N, hN⟩ := h w₁ w₂ n
  refine ⟨N.toNat, fun j hj => ?_⟩
  have := hN (j : ℤ) (by omega)
  rwa [Int.cast_natCast] at this

variable (L : End ℂ M₃)

/-- The `j`-th summand `((−1)ʲ/j!) L₋₁ʲ (𝒴₍ₙ₊ⱼ₎ w₁ w₂)`. -/
noncomputable def sTerm (Y : IntertwiningModes M₁ M₂ M₃) (n : ℂ) (w₁ : M₁) (w₂ : M₂) (j : ℕ) :
    M₃ :=
  sc j • (L ^ j) (Y (n + j) w₁ w₂)

/-- `Σ_{j ≥ 0} ((−1)ʲ/j!) L₋₁ʲ (𝒴₍ₙ₊ⱼ₎ w₁ w₂)` (finite by truncation). -/
noncomputable def sSum (Y : IntertwiningModes M₁ M₂ M₃) (n : ℂ) (w₁ : M₁) (w₂ : M₂) : M₃ :=
  ∑ᶠ j : ℕ, sTerm L Y n w₁ w₂ j

variable {L}

theorem sSum_eq_sum {Y : IntertwiningModes M₁ M₂ M₃} {n : ℂ} {w₁ : M₁} {w₂ : M₂} (K : ℕ)
    (hK : ∀ j : ℕ, K ≤ j → Y (n + j) w₁ w₂ = 0) :
    sSum L Y n w₁ w₂ = ∑ j ∈ Finset.range K, sTerm L Y n w₁ w₂ j := by
  rw [sSum]
  refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
  rw [Function.mem_support] at hj
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra h
  exact hj (by rw [sTerm, hK j (by omega), map_zero, smul_zero])

theorem sSum_add_left {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (n : ℂ) (w₁ w₁' : M₁)
    (w₂ : M₂) : sSum L Y n (w₁ + w₁') w₂ = sSum L Y n w₁ w₂ + sSum L Y n w₁' w₂ := by
  obtain ⟨K₁, h₁⟩ := hY.bound w₁ w₂ n
  obtain ⟨K₂, h₂⟩ := hY.bound w₁' w₂ n
  rw [sSum_eq_sum (K₁ + K₂) (fun j hj => by
      rw [map_add, LinearMap.add_apply, h₁ j (by omega), h₂ j (by omega), add_zero]),
    sSum_eq_sum (K₁ + K₂) (fun j hj => h₁ j (by omega)),
    sSum_eq_sum (K₁ + K₂) (fun j hj => h₂ j (by omega)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sTerm, map_add, LinearMap.add_apply, smul_add]

theorem sSum_smul_left {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (n : ℂ) (a : ℂ)
    (w₁ : M₁) (w₂ : M₂) : sSum L Y n (a • w₁) w₂ = a • sSum L Y n w₁ w₂ := by
  obtain ⟨K, h⟩ := hY.bound w₁ w₂ n
  rw [sSum_eq_sum K (fun j hj => by rw [map_smul, LinearMap.smul_apply, h j hj, smul_zero]),
    sSum_eq_sum K h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sTerm, map_smul, LinearMap.smul_apply]
  rw [smul_comm]

theorem sSum_add_right {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (n : ℂ) (w₁ : M₁)
    (w₂ w₂' : M₂) : sSum L Y n w₁ (w₂ + w₂') = sSum L Y n w₁ w₂ + sSum L Y n w₁ w₂' := by
  obtain ⟨K₁, h₁⟩ := hY.bound w₁ w₂ n
  obtain ⟨K₂, h₂⟩ := hY.bound w₁ w₂' n
  rw [sSum_eq_sum (K₁ + K₂) (fun j hj => by
      rw [map_add, h₁ j (by omega), h₂ j (by omega), add_zero]),
    sSum_eq_sum (K₁ + K₂) (fun j hj => h₁ j (by omega)),
    sSum_eq_sum (K₁ + K₂) (fun j hj => h₂ j (by omega)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sTerm, map_add, smul_add]

theorem sSum_smul_right {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (n : ℂ) (a : ℂ)
    (w₁ : M₁) (w₂ : M₂) : sSum L Y n w₁ (a • w₂) = a • sSum L Y n w₁ w₂ := by
  obtain ⟨K, h⟩ := hY.bound w₁ w₂ n
  rw [sSum_eq_sum K (fun j hj => by rw [map_smul, h j hj, smul_zero]),
    sSum_eq_sum K h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sTerm, map_smul]
  rw [smul_comm]

variable (L)

/-- The bilinear map `(w₂, w₁) ↦ c n · sSum`, for truncated data. -/
noncomputable def skewLin (c : ℂ → ℂ) (Y : IntertwiningModes M₁ M₂ M₃) (hY : Trunc Y) (n : ℂ) :
    M₂ →ₗ[ℂ] M₁ →ₗ[ℂ] M₃ :=
  LinearMap.mk₂ ℂ (fun w₂ w₁ => c n • sSum L Y n w₁ w₂)
    (fun w₂ w₂' w₁ => by simp only [sSum_add_right hY, smul_add])
    (fun a w₂ w₁ => by simp only [sSum_smul_right hY]; rw [smul_comm])
    (fun w₂ w₁ w₁' => by simp only [sSum_add_left hY, smul_add])
    (fun a w₂ w₁ => by simp only [sSum_smul_left hY]; rw [smul_comm])

open Classical in
/-- **The skew-symmetry operator** `Ω_c(𝒴)` of type `(M₃ / M₂ M₁)`:
`Ω_c(𝒴)₍ₙ₎ w₂ w₁ = c n · Σ_{j≥0} ((−1)ʲ/j!) L₋₁ʲ 𝒴₍ₙ₊ⱼ₎ w₁ w₂` (FHL Prop. 5.4.7 with the phase
`c`).  On non-truncated data (never an intertwiner) the junk value is `0`. -/
noncomputable def skewModes (c : ℂ → ℂ) (Y : IntertwiningModes M₁ M₂ M₃) :
    IntertwiningModes M₂ M₁ M₃ :=
  fun n => if h : Trunc Y then skewLin L c Y h n else 0

variable {L}

theorem skewModes_apply {c : ℂ → ℂ} {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (n : ℂ)
    (w₂ : M₂) (w₁ : M₁) : skewModes L c Y n w₂ w₁ = c n • sSum L Y n w₁ w₂ := by
  simp only [skewModes, dif_pos hY, skewLin, LinearMap.mk₂_apply]

/-- `Ω_c(𝒴)` is always truncated. -/
theorem trunc_skewModes (c : ℂ → ℂ) (Y : IntertwiningModes M₁ M₂ M₃) :
    Trunc (skewModes L c Y) := by
  by_cases hY : Trunc Y
  · intro w₂ w₁ n
    obtain ⟨N, hN⟩ := hY w₁ w₂ n
    refine ⟨N, fun k hk => ?_⟩
    rw [skewModes_apply hY, sSum]
    rw [finsum_eq_zero_of_forall_eq_zero fun j => ?_, smul_zero]
    rw [sTerm, show n + (k : ℂ) + (j : ℂ) = n + ((k + j : ℤ) : ℂ) by push_cast; ring,
      hN _ (by omega), map_zero, smul_zero]
  · intro w₂ w₁ n
    refine ⟨0, fun k _ => ?_⟩
    simp only [skewModes, dif_neg hY, LinearMap.zero_apply]

/-- **`Ω_{c'} ∘ Ω_c = id`** when `c' n · c n = 1` (FHL: `Ω₋₁ ∘ Ω₀ = id`). -/
theorem skewModes_skewModes {c c' : ℂ → ℂ} (hc : ∀ n, c (n + 1) = -c n)
    (hcc : ∀ n, c' n * c n = 1) {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) :
    skewModes L c' (skewModes L c Y) = Y := by
  funext n
  refine LinearMap.ext fun w₁ => LinearMap.ext fun w₂ => ?_
  rw [skewModes_apply (trunc_skewModes c Y)]
  obtain ⟨K, hK⟩ := hY.bound w₁ w₂ n
  -- the outer sum
  have hout : ∀ k : ℕ, K + 1 ≤ k → skewModes L c Y (n + k) w₂ w₁ = 0 := by
    intro k hk
    rw [skewModes_apply hY, sSum]
    rw [finsum_eq_zero_of_forall_eq_zero fun j => ?_, smul_zero]
    rw [sTerm, show n + (k : ℂ) + (j : ℂ) = n + ((k + j : ℕ) : ℂ) by push_cast; ring,
      hK _ (by omega), map_zero, smul_zero]
  rw [sSum_eq_sum (K + 1) hout]
  have hin : ∀ k : ℕ, sTerm L (skewModes L c Y) n w₂ w₁ k
      = ∑ j ∈ Finset.range (K + 1), (c n * ((k.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ j
          * (j.factorial : ℂ)⁻¹))) • (L ^ (j + k)) (Y (n + ((j + k : ℕ) : ℂ)) w₁ w₂) := by
    intro k
    rw [sTerm, skewModes_apply hY, sSum_eq_sum (K + 1) (fun j hj => by
      rw [show n + (k : ℂ) + (j : ℂ) = n + ((k + j : ℕ) : ℂ) by push_cast; ring]
      exact hK _ (by omega)), Finset.smul_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sTerm, map_smul, map_smul, smul_smul, smul_smul, ← Module.End.mul_apply, ← pow_add,
      phase_nat hc, show n + (k : ℂ) + (j : ℂ) = n + ((j + k : ℕ) : ℂ) by push_cast; ring,
      add_comm k j]
    congr 1
    simp only [sc]
    have h1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination (c n * (k.factorial : ℂ)⁻¹ * (-1) ^ j * (j.factorial : ℂ)⁻¹) * h1
  rw [Finset.sum_congr rfl fun k _ => hin k, Finset.sum_comm]
  -- restrict to the triangle
  have htri : ∀ j ∈ Finset.range (K + 1), ∑ k ∈ Finset.range (K + 1),
      (c n * ((k.factorial : ℂ)⁻¹ * ((-1 : ℂ) ^ j * (j.factorial : ℂ)⁻¹))) •
        (L ^ (j + k)) (Y (n + ((j + k : ℕ) : ℂ)) w₁ w₂)
      = c n • ∑ k ∈ Finset.range (K - j + 1),
          ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * (k.factorial : ℂ)⁻¹)) •
            (fun N : ℕ => (L ^ N) (Y (n + (N : ℂ)) w₁ w₂)) (k + j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.smul_sum]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : K - j + 1 ≤ K + 1))
      (fun k _ hk => by
        rw [Finset.mem_range] at hk
        rw [hK _ (by omega), map_zero, smul_zero])]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, add_comm k j]
    congr 1
    ring
  rw [Finset.sum_congr rfl htri, ← Finset.smul_sum,
    triangle_sum K (fun N : ℕ => (L ^ N) (Y (n + (N : ℂ)) w₁ w₂)), smul_smul, hcc]
  simp

end Skew

/-! ## Pascal recurrences of the Jacobi sums, and the boundary descent -/

section Pascal

variable {N₁ : Type v₁} {N₂ : Type v₂} {N₃ : Type v₃}
  [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂] [Module ℂ N₂]
  [AddCommGroup N₃] [Module ℂ N₃]
variable (B₁ : WeakModule W N₁) (B₂ : WeakModule W N₂) (B₃ : WeakModule W N₃)

/-- The left side of the Jacobi identity (the sum in `IsIntertwiningOperator.jacobi`). -/
noncomputable def JL (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) : N₃ :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
    (mode (B₃.YM u) (ℓ + m - i) (X (n + i) x₁ x₂)
      - negOnePow ℓ • X (ℓ + n - i) x₁ (mode (B₂.YM u) (m + i) x₂))

/-- The right side of the Jacobi identity. -/
noncomputable def JR (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) : N₃ :=
  ∑ᶠ i : ℤ, cbz m i • X (m + n - i) (mode (B₁.YM u) (ℓ + i) x₁) x₂

/-- The first ordered sum. -/
noncomputable def P (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) : N₃ :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • mode (B₃.YM u) (ℓ + m - i) (X (n + i) x₁ x₂)

/-- The second ordered sum. -/
noncomputable def Q (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) : N₃ :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • X (ℓ + n - i) x₁ (mode (B₂.YM u) (m + i) x₂)

/-- Finite support from two-sided vanishing. -/
theorem fin_of_bounds {X : Type*} [Zero X] (f : ℤ → X) (a b : ℤ)
    (h₁ : ∀ i, i < a → f i = 0) (h₂ : ∀ i, b ≤ i → f i = 0) :
    (Function.support f).Finite := by
  refine (Set.finite_Ico a b).subset fun i hi => ?_
  rw [Function.mem_support] at hi
  rw [Set.mem_Ico]
  by_contra h
  rcases not_and_or.1 h with h | h
  · exact hi (h₁ i (not_le.1 h))
  · exact hi (h₂ i (not_lt.1 h))

variable {B₁ B₂ B₃}

theorem P_fin {X : IntertwiningModes N₁ N₂ N₃} (hX : Trunc X) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ : ℤ) (n : ℂ) (p : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      mode (B₃.YM u) (p - i) (X (n + i) x₁ x₂)).Finite := by
  obtain ⟨N, hN⟩ := hX x₁ x₂ n
  refine fin_of_bounds _ 0 (max N 0) (fun i hi => ?_) (fun i hi => ?_)
  · rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul]
  · rw [hN i (le_trans (le_max_left _ _) hi), map_zero, smul_zero]

theorem P_fin' {X : IntertwiningModes N₁ N₂ N₃} (hX : Trunc X) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ : ℤ) (n : ℂ) (p : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ (i - 1)) •
      mode (B₃.YM u) (p - i) (X (n + i) x₁ x₂)).Finite := by
  obtain ⟨N, hN⟩ := hX x₁ x₂ n
  refine fin_of_bounds _ 1 (max N 1) (fun i hi => ?_) (fun i hi => ?_)
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [hN i (le_trans (le_max_left _ _) hi), map_zero, smul_zero]

theorem Q_fin (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (ℓ m : ℤ) (q : ℂ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      X (q - i) x₁ (mode (B₂.YM u) (m + i) x₂)).Finite := by
  obtain ⟨N, hN⟩ := B₂.truncation u x₂
  refine fin_of_bounds _ 0 (max (N - m) 0) (fun i hi => ?_) (fun i hi => ?_)
  · rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul]
  · rw [hN (m + i) (by have := le_max_left (N - m) 0; omega), map_zero, smul_zero]

theorem Q_fin' (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (ℓ m : ℤ) (q : ℂ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ (i - 1)) •
      X (q - i) x₁ (mode (B₂.YM u) (m + i) x₂)).Finite := by
  obtain ⟨N, hN⟩ := B₂.truncation u x₂
  refine fin_of_bounds _ 1 (max (N - m) 1) (fun i hi => ?_) (fun i hi => ?_)
  · rw [cbz_apply_neg ℓ (by omega), mul_zero, zero_smul]
  · rw [hN (m + i) (by have := le_max_left (N - m) 1; omega), map_zero, smul_zero]

theorem JR_fin (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (ℓ m : ℤ) (q : ℂ) :
    (Function.support fun i : ℤ =>
      cbz m i • X (q - i) (mode (B₁.YM u) (ℓ + i) x₁) x₂).Finite := by
  obtain ⟨N, hN⟩ := B₁.truncation u x₁
  refine fin_of_bounds _ 0 (max (N - ℓ) 0) (fun i hi => ?_) (fun i hi => ?_)
  · rw [cbz_apply_neg m hi, zero_smul]
  · rw [hN (ℓ + i) (by have := le_max_left (N - ℓ) 0; omega), map_zero, LinearMap.zero_apply,
      smul_zero]

theorem JR_fin' (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (ℓ m : ℤ)
    (q : ℂ) :
    (Function.support fun i : ℤ =>
      cbz m (i - 1) • X (q - i) (mode (B₁.YM u) (ℓ + i) x₁) x₂).Finite := by
  obtain ⟨N, hN⟩ := B₁.truncation u x₁
  refine fin_of_bounds _ 1 (max (N - ℓ) 1) (fun i hi => ?_) (fun i hi => ?_)
  · rw [cbz_apply_neg m (by omega), zero_smul]
  · rw [hN (ℓ + i) (by have := le_max_left (N - ℓ) 1; omega), map_zero, LinearMap.zero_apply,
      smul_zero]

omit [Module ℂ N₃] in
theorem finsum_neg' {ι : Type*} (f : ι → N₃) : (∑ᶠ i, -f i) = -∑ᶠ i, f i := by
  by_cases h : (Function.support f).Finite
  · rw [← neg_one_zsmul (∑ᶠ i, f i), smul_finsum' (-1 : ℤ) h]
    exact finsum_congr fun i => (neg_one_zsmul (f i)).symm
  · have h' : ¬ (Function.support fun i => -f i).Finite := by
      rwa [show (Function.support fun i => -f i) = Function.support f from by
        ext i
        simp [Function.mem_support]]
    rw [finsum_of_infinite_support h', finsum_of_infinite_support h, neg_zero]

theorem P_rec {X : IntertwiningModes N₁ N₂ N₃} (hX : Trunc X) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) :
    P B₃ X u x₁ x₂ ℓ (m + 1) n = P B₃ X u x₁ x₂ ℓ m (n + 1) + P B₃ X u x₁ x₂ (ℓ + 1) m n := by
  have e1 : P B₃ X u x₁ x₂ (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • mode (B₃.YM u) (ℓ + 1 + m - i) (X (n + i) x₁ x₂))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
          mode (B₃.YM u) (ℓ + 1 + m - i) (X (n + i) x₁ x₂) := by
    rw [P, ← finsum_add_distrib (P_fin hX u x₁ x₂ ℓ n _) (P_fin' hX u x₁ x₂ ℓ n _)]
    refine finsum_congr fun i => ?_
    rw [cbz_pascal_up, mul_add, add_smul]
  have e0 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      mode (B₃.YM u) (ℓ + 1 + m - i) (X (n + i) x₁ x₂)) = P B₃ X u x₁ x₂ ℓ (m + 1) n := by
    rw [P]
    exact finsum_congr fun i => by rw [show ℓ + (m + 1) - i = ℓ + 1 + m - i by ring]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
      mode (B₃.YM u) (ℓ + 1 + m - i) (X (n + i) x₁ x₂)) = -P B₃ X u x₁ x₂ ℓ m (n + 1) := by
    rw [← finsum_int_succ_shift, P, ← finsum_neg']
    refine finsum_congr fun i => ?_
    rw [show i + 1 - 1 = i by ring, negOnePow_succ, show ℓ + 1 + m - (i + 1) = ℓ + m - i by ring,
      show n + ((i + 1 : ℤ) : ℂ) = n + 1 + (i : ℂ) by push_cast; ring, neg_mul, neg_smul]
  rw [e1, e0, e2]
  abel

theorem Q_rec (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) :
    Q B₂ X u x₁ x₂ ℓ (m + 1) n = Q B₂ X u x₁ x₂ ℓ m (n + 1) - Q B₂ X u x₁ x₂ (ℓ + 1) m n := by
  have e1 : Q B₂ X u x₁ x₂ (ℓ + 1) m n
      = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          X (((ℓ + 1 : ℤ) : ℂ) + n - i) x₁ (mode (B₂.YM u) (m + i) x₂))
        + ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
          X (((ℓ + 1 : ℤ) : ℂ) + n - i) x₁ (mode (B₂.YM u) (m + i) x₂) := by
    rw [Q, ← finsum_add_distrib (Q_fin X u x₁ x₂ ℓ m _) (Q_fin' X u x₁ x₂ ℓ m _)]
    refine finsum_congr fun i => ?_
    rw [cbz_pascal_up, mul_add, add_smul]
  have e0 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      X (((ℓ + 1 : ℤ) : ℂ) + n - i) x₁ (mode (B₂.YM u) (m + i) x₂))
      = Q B₂ X u x₁ x₂ ℓ m (n + 1) := by
    rw [Q]
    exact finsum_congr fun i => by
      rw [show ((ℓ + 1 : ℤ) : ℂ) + n - i = (ℓ : ℂ) + (n + 1) - i by push_cast; ring]
  have e2 : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) •
      X (((ℓ + 1 : ℤ) : ℂ) + n - i) x₁ (mode (B₂.YM u) (m + i) x₂))
      = -Q B₂ X u x₁ x₂ ℓ (m + 1) n := by
    rw [← finsum_int_succ_shift, Q, ← finsum_neg']
    refine finsum_congr fun i => ?_
    rw [show i + 1 - 1 = i by ring, negOnePow_succ,
      show ((ℓ + 1 : ℤ) : ℂ) + n - ((i + 1 : ℤ) : ℂ) = (ℓ : ℂ) + n - (i : ℂ) by push_cast; ring,
      show m + (i + 1) = m + 1 + i by ring, neg_mul, neg_smul]
  rw [e1, e0, e2]
  abel

theorem JR_rec (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (ℓ m : ℤ) (n : ℂ) :
    JR B₁ X u x₁ x₂ ℓ (m + 1) n = JR B₁ X u x₁ x₂ ℓ m (n + 1) + JR B₁ X u x₁ x₂ (ℓ + 1) m n := by
  have e1 : JR B₁ X u x₁ x₂ ℓ (m + 1) n
      = (∑ᶠ i : ℤ, cbz m i • X (((m + 1 : ℤ) : ℂ) + n - i) (mode (B₁.YM u) (ℓ + i) x₁) x₂)
        + ∑ᶠ i : ℤ, cbz m (i - 1) • X (((m + 1 : ℤ) : ℂ) + n - i)
            (mode (B₁.YM u) (ℓ + i) x₁) x₂ := by
    rw [JR, ← finsum_add_distrib (JR_fin X u x₁ x₂ ℓ m _) (JR_fin' X u x₁ x₂ ℓ m _)]
    refine finsum_congr fun i => ?_
    rw [cbz_pascal_up, add_smul]
  have e0 : (∑ᶠ i : ℤ, cbz m i • X (((m + 1 : ℤ) : ℂ) + n - i) (mode (B₁.YM u) (ℓ + i) x₁) x₂)
      = JR B₁ X u x₁ x₂ ℓ m (n + 1) := by
    rw [JR]
    exact finsum_congr fun i => by
      rw [show ((m + 1 : ℤ) : ℂ) + n - i = (m : ℂ) + (n + 1) - i by push_cast; ring]
  have e2 : (∑ᶠ i : ℤ, cbz m (i - 1) • X (((m + 1 : ℤ) : ℂ) + n - i)
      (mode (B₁.YM u) (ℓ + i) x₁) x₂) = JR B₁ X u x₁ x₂ (ℓ + 1) m n := by
    rw [← finsum_int_succ_shift, JR]
    refine finsum_congr fun i => ?_
    rw [show i + 1 - 1 = i by ring, show ℓ + (i + 1) = ℓ + 1 + i by ring,
      show ((m + 1 : ℤ) : ℂ) + n - ((i + 1 : ℤ) : ℂ) = (m : ℂ) + n - (i : ℂ) by push_cast; ring]
  rw [e1, e0, e2]

/-- `JL = P − (−1)^ℓ Q`. -/
theorem JL_eq (X : IntertwiningModes N₁ N₂ N₃) (hX : Trunc X) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) :
    JL B₂ B₃ X u x₁ x₂ ℓ m n = P B₃ X u x₁ x₂ ℓ m n - negOnePow ℓ • Q B₂ X u x₁ x₂ ℓ m n := by
  have hP := P_fin (B₃ := B₃) hX u x₁ x₂ ℓ n (ℓ + m)
  have hQ := Q_fin (B₂ := B₂) X u x₁ x₂ ℓ m ((ℓ : ℂ) + n)
  have hQ' : (Function.support fun i : ℤ => -(negOnePow ℓ • ((negOnePow i * cbz ℓ i) •
      X (ℓ + n - i) x₁ (mode (B₂.YM u) (m + i) x₂)))).Finite := by
    refine hQ.subset fun i hi => ?_
    simp only [Function.mem_support] at hi ⊢
    intro hz
    exact hi (by rw [hz, smul_zero, neg_zero])
  rw [JL, P, Q, smul_finsum' _ hQ, sub_eq_add_neg, ← finsum_neg', ← finsum_add_distrib hP hQ']
  refine finsum_congr fun i => ?_
  rw [smul_sub, smul_comm (negOnePow ℓ), sub_eq_add_neg]

/-- The Jacobi defect `S = JL − JR`. -/
noncomputable def S (B₁ : WeakModule W N₁) (B₂ : WeakModule W N₂) (B₃ : WeakModule W N₃)
    (X : IntertwiningModes N₁ N₂ N₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) : N₃ :=
  JL B₂ B₃ X u x₁ x₂ ℓ m n - JR B₁ X u x₁ x₂ ℓ m n

theorem S_rec (X : IntertwiningModes N₁ N₂ N₃) (hX : Trunc X) (u : 𝒱) (x₁ : N₁) (x₂ : N₂)
    (ℓ m : ℤ) (n : ℂ) :
    S B₁ B₂ B₃ X u x₁ x₂ ℓ (m + 1) n
      = S B₁ B₂ B₃ X u x₁ x₂ ℓ m (n + 1) + S B₁ B₂ B₃ X u x₁ x₂ (ℓ + 1) m n := by
  simp only [S, JL_eq X hX, P_rec hX, Q_rec, JR_rec, negOnePow_succ]
  module

end Pascal

/-- **Boundary descent.**  A family `S ℓ m n` satisfying the Pascal recurrence
`S ℓ (m+1) n = S ℓ m (n+1) + S (ℓ+1) m n` and vanishing on `ℓ = 0` and on `m = 0` vanishes. -/
theorem eq_zero_of_boundaries {X : Type*} [AddCommGroup X] (S : ℤ → ℤ → ℂ → X)
    (hrec : ∀ ℓ m n, S ℓ (m + 1) n = S ℓ m (n + 1) + S (ℓ + 1) m n)
    (h0 : ∀ m n, S 0 m n = 0) (h1 : ∀ ℓ n, S ℓ 0 n = 0) : ∀ ℓ m n, S ℓ m n = 0 := by
  have hnn : ∀ k : ℕ, ∀ ℓ n, S ℓ k n = 0 := by
    intro k
    induction k with
    | zero => exact fun ℓ n => by simpa using h1 ℓ n
    | succ k ih =>
        intro ℓ n
        rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring, hrec, ih, ih, add_zero]
  have step : ∀ m : ℤ, (∀ ℓ n, S ℓ (m + 1) n = 0) → ∀ ℓ n, S ℓ m n = 0 := by
    intro m hm
    have rel : ∀ ℓ n, S (ℓ + 1) m n = - S ℓ m (n + 1) := by
      intro ℓ n
      have h := hrec ℓ m n
      rw [hm] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    intro ℓ
    induction ℓ using Int.induction_on with
    | zero => exact h0 m
    | succ k ih => intro n; rw [rel, ih, neg_zero]
    | pred k ih =>
        intro n
        have h := rel (-(k : ℤ) - 1) (n - 1)
        rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ih, sub_add_cancel] at h
        exact neg_eq_zero.mp h.symm
  have hneg : ∀ k : ℕ, ∀ ℓ n, S ℓ (-(k : ℤ) - 1) n = 0 := by
    intro k
    induction k with
    | zero => exact step _ fun ℓ n => by simpa using h1 ℓ n
    | succ k ih =>
        refine step _ fun ℓ n => ?_
        rw [show -((k + 1 : ℕ) : ℤ) - 1 + 1 = -(k : ℤ) - 1 by push_cast; ring]
        exact ih ℓ n
  intro ℓ m n
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
    exact hnn k ℓ n
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) - 1 := ⟨(-m - 1).toNat, by omega⟩
    exact hneg k ℓ n

end VOA.LogSkew
