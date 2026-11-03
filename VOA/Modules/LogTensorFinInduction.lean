/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorFinArtin

/-!
# The reduction induction for logarithmic intertwining operators (stage T1d, part 4)

Let `𝒴` be a logarithmic intertwining operator of type `(N₃ / N₁ N₂)` among `LogVModule`s.
Write `Van α₁ α₂ n` for "`(w₁)_{n;k} w₂ = 0` for all `k`, `w₁ ∈ (N₁)_[α₁]`, `w₂ ∈ (N₂)_[α₂]`";
the output then has weight `α₃ = α₁ + α₂ − n − 1`.

`van_below`: suppose that outside finite sets `F₁`, `F₂` of weights the graded pieces of `N₁`,
`N₂` lie in `C₂` (`c2Part`).  If `Van α₁ α₂ n` holds for all `α₁ ∈ F₁`, `α₂ ∈ F₂` and all `n`
with `Re α₃ < C`, then it holds for **all** `α₁, α₂, n` with `Re α₃ < C`.

*Proof.*  Induction on `Re α₃` (outer) and then on `Re (α₁ + α₂)` (inner); both drop by
integers `≥ 1` at every step and are bounded below.
* `w₁ = u₍ℓ₎ w'` with `ℓ ≤ −2` (slot 1 in `C₂`): the associator (Jacobi at `m = 0`) writes
  `(u₍ℓ₎w')_{n;k} w₂` through `u₍ℓ−i₎ (w')_{n+i;k} w₂` (output weight drops by
  `≥ wt u − ℓ − 1 ≥ 1`) and `(w')_{ℓ+n−i;k} u₍ᵢ₎ w₂`, `i ≥ 0` (same output weight,
  `Re(α₁ + α₂)` drops by `i − ℓ ≥ 2`).
* `w₂ = u₍ₘ₎ w'` with `m ≤ −2` (slot 2 in `C₂`): the commutator formula writes
  `(w₁)_{n;k} u₍ₘ₎ w'` through `u₍ₘ₎ (w₁)_{n;k} w'` (output weight drops) and
  `(u₍ᵢ₎ w₁)_{m+n−i;k} w'`, `i ≥ 0` (same output weight, `Re(α₁ + α₂)` drops by `i − m ≥ 2`).
* Otherwise `α₁ ∈ F₁`, `α₂ ∈ F₂`: the hypothesis.

Only the Jacobi identity at a fixed log degree `k` is used, never the `L(−1)` property, so the
induction is uniform in `k`.

No `sorry`, no new axioms.
-/

namespace VOA.LogTensor.LogFin

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable {N₁ : LogVModule W M₁} {N₂ : LogVModule W M₂} {N₃ : LogVModule W M₃}

/-- `(w₁)_{n;k} w₂ = 0` for all `k` and all `w₁ ∈ (N₁)_[α₁]`, `w₂ ∈ (N₂)_[α₂]`. -/
def Van (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (Y : LogModes M₁ M₂ M₃)
    (α₁ α₂ n : ℂ) : Prop :=
  ∀ (k : ℕ) (w₁ : M₁) (w₂ : M₂), w₁ ∈ N₁.weight α₁ → w₂ ∈ N₂.weight α₂ → Y n k w₁ w₂ = 0

variable {Y : LogModes M₁ M₂ M₃}

/-- **The reduction induction.** -/
theorem van_below
    (hY : IsLogIntertwining N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Y)
    {F₁ F₂ : Set ℂ} (hF₁ : ∀ α, α ∉ F₁ → N₁.weight α ≤ c2Part N₁ α)
    (hF₂ : ∀ α, α ∉ F₂ → N₂.weight α ≤ c2Part N₂ α) (C : ℝ)
    (hbase : ∀ α₁ ∈ F₁, ∀ α₂ ∈ F₂, ∀ n : ℂ, (α₁ + α₂ - n - 1).re < C → Van N₁ N₂ Y α₁ α₂ n) :
    ∀ α₁ α₂ n : ℂ, (α₁ + α₂ - n - 1).re < C → Van N₁ N₂ Y α₁ α₂ n := by
  obtain ⟨B₁, hB₁⟩ := exists_lower_bound N₁
  obtain ⟨B₂, hB₂⟩ := exists_lower_bound N₂
  obtain ⟨B₃, hB₃⟩ := exists_lower_bound N₃
  have key : ∀ T : ℕ, ∀ α₁ α₂ n : ℂ, (α₁ + α₂ - n - 1).re < C →
      (α₁ + α₂ - n - 1).re < B₃ + T → Van N₁ N₂ Y α₁ α₂ n := by
    intro T
    induction T with
    | zero =>
      intro α₁ α₂ n _ h3 k w₁ w₂ h₁ h₂
      have hmem := hY.mem_weight h₁ h₂ n k
      exact eq_zero_of_mem_bot N₃ (hB₃ _ (by simpa using h3)) hmem
    | succ T IHo =>
      have inner : ∀ K : ℕ, ∀ α₁ α₂ n : ℂ, (α₁ + α₂ - n - 1).re < C →
          (α₁ + α₂ - n - 1).re < B₃ + (T + 1 : ℕ) → (α₁ + α₂).re < B₁ + B₂ + K →
          Van N₁ N₂ Y α₁ α₂ n := by
        intro K
        induction K with
        | zero =>
          intro α₁ α₂ n _ _ hs k w₁ w₂ h₁ h₂
          simp only [Complex.add_re, CharP.cast_eq_zero, add_zero] at hs
          by_cases hr : α₁.re < B₁
          · rw [eq_zero_of_mem_bot N₁ (hB₁ _ hr) h₁, map_zero, LinearMap.zero_apply]
          · have hr2 : α₂.re < B₂ := by linarith
            rw [eq_zero_of_mem_bot N₂ (hB₂ _ hr2) h₂, map_zero]
        | succ K IHi =>
          intro α₁ α₂ n hC h3 hs k w₁ w₂ h₁ h₂
          have h3' : (α₁ + α₂ - n - 1).re < B₃ + T + 1 := by push_cast at h3; linarith
          have hs' : (α₁ + α₂).re < B₁ + B₂ + K + 1 := by push_cast at hs; linarith
          by_cases hα₁ : α₁ ∈ F₁
          · by_cases hα₂ : α₂ ∈ F₂
            · exact hbase α₁ hα₁ α₂ hα₂ n hC k w₁ w₂ h₁ h₂
            · -- slot 2 lies in `C₂`: the commutator formula
              have hw₂ := hF₂ α₂ hα₂ h₂
              clear h₂
              induction hw₂ using Submodule.span_induction with
              | mem z hz =>
                obtain ⟨d, m, u, w', hu, hd, hm, hw', rfl⟩ := hz
                have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
                have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hm
                have hcomm := hY.commutator u w₁ w' m n k
                have h1 : Y n k w₁ w' = 0 := by
                  refine IHo α₁ (α₂ - ((d - m - 1 : ℤ) : ℂ)) n ?_ ?_ k w₁ w' h₁ hw'
                  · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re,
                      Complex.one_re] at hC ⊢
                    push_cast; linarith
                  · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re,
                      Complex.one_re] at h3' ⊢
                    push_cast; linarith
                have h2 : ∀ i : ℤ,
                    cbz m i • Y (m + n - i) k (mode (N₁.YM u) i w₁) w' = 0 := by
                  intro i
                  by_cases hi : i < 0
                  · rw [cbz_apply_neg m hi, zero_smul]
                  · have hiR : (0 : ℝ) ≤ i := by exact_mod_cast (not_lt.mp hi)
                    rw [IHi (α₁ + ((d - i - 1 : ℤ) : ℂ)) (α₂ - ((d - m - 1 : ℤ) : ℂ))
                      (m + n - i) ?_ ?_ ?_ k _ w' (mode_mem_weight N₁ hu i h₁) hw', smul_zero]
                    · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re,
                        Complex.one_re] at hC ⊢
                      push_cast; linarith
                    · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re,
                        Complex.one_re] at h3 ⊢
                      push_cast at h3 ⊢; linarith
                    · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re] at hs' ⊢
                      push_cast; linarith
                rw [h1, map_zero, zero_sub, finsum_eq_zero_of_forall_eq_zero h2,
                  neg_eq_zero] at hcomm
                exact hcomm
              | zero => rw [map_zero]
              | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
              | smul c a _ ha => rw [map_smul, ha, smul_zero]
          · -- slot 1 lies in `C₂`: the associator
            have hw₁ := hF₁ α₁ hα₁ h₁
            clear h₁
            induction hw₁ using Submodule.span_induction with
            | mem z hz =>
              obtain ⟨d, ℓ, u, w', hu, hd, hℓ, hw', rfl⟩ := hz
              have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
              have hℓR : (ℓ : ℝ) ≤ -2 := by exact_mod_cast hℓ
              rw [← hY.associator u w' w₂ ℓ n k]
              refine finsum_eq_zero_of_forall_eq_zero (fun i => ?_)
              by_cases hi : i < 0
              · rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul]
              · have hiR : (0 : ℝ) ≤ i := by exact_mod_cast (not_lt.mp hi)
                have h1 : Y (n + i) k w' w₂ = 0 := by
                  refine IHo (α₁ - ((d - ℓ - 1 : ℤ) : ℂ)) α₂ (n + i) ?_ ?_ k w' w₂ hw' h₂
                  · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re,
                      Complex.one_re] at hC ⊢
                    push_cast; linarith
                  · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re,
                      Complex.one_re] at h3' ⊢
                    push_cast; linarith
                have h2 : Y (ℓ + n - i) k w' (mode (N₂.YM u) (0 + i) w₂) = 0 := by
                  refine IHi (α₁ - ((d - ℓ - 1 : ℤ) : ℂ)) (α₂ + ((d - (0 + i) - 1 : ℤ) : ℂ))
                    (ℓ + n - i) ?_ ?_ ?_ k w' _ hw' (mode_mem_weight N₂ hu (0 + i) h₂)
                  · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re,
                      Complex.one_re] at hC ⊢
                    push_cast; linarith
                  · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re,
                      Complex.one_re] at h3 ⊢
                    push_cast at h3 ⊢; linarith
                  · simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re] at hs' ⊢
                    push_cast; linarith
                rw [h1, h2, map_zero, smul_zero, sub_zero, smul_zero]
            | zero => rw [map_zero, LinearMap.zero_apply]
            | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
            | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
      intro α₁ α₂ n hC h3
      obtain ⟨K, hK⟩ := exists_nat_gt ((α₁ + α₂).re - B₁ - B₂)
      exact inner K α₁ α₂ n hC h3 (by linarith)
  intro α₁ α₂ n hC
  obtain ⟨T, hT⟩ := exists_nat_gt ((α₁ + α₂ - n - 1).re - B₃)
  exact key T α₁ α₂ n hC (by linarith)

end VOA.LogTensor.LogFin
