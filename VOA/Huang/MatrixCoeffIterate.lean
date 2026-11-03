/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.MatrixCoeff

/-!
# The `u₋₁`-iterate formula for intertwining operators — first VOA step of V3b

Huang's generator `𝒜(u, w₀, w₁, w₂, w₃)` (CCM 7 (2005), §1) encodes, after pairing, the identity

  `𝒴(u₋₁ w₁, z) = Res_x [(x − z)⁻¹ Y(u, x) 𝒴(w₁, z) − (−z + x)⁻¹ 𝒴(w₁, z) Y(u, x)]`,

which moves the `C₁`-type vector `u₋₁ w₁` out of the intertwiner slot.  In modes it is the Jacobi
identity of `𝒴` at `(ℓ, m) = (−1, 0)`:

  `(u₋₁ w₁)₍ₙ₎ w₂ = Σ_{i ≥ 0} ( u₋₁₋ᵢ (w₁)₍ₙ₊ᵢ₎ w₂ + (w₁)₍ₙ₋₁₋ᵢ₎ uᵢ w₂ )`

(`mode_neg_one_left`), a finite sum by truncation.  This is the mode-level content of
`φ(𝒜) = 0` for the outer operator (the remaining part of `𝒜` moves `uᵢ` past the inner operator by
the commutator formula `IsIntertwiningOperator.commutator`, and `u₋₁₋ᵢ` onto the functional `w₀`).
Each term on the right has total weight strictly below the left side's in the slot of `w₁` when
`u ∈ V₊` — the engine of Huang's Prop. 1.1 (`Huang/MatrixCoeffODE.lean`).

## Main results
* `cbz_neg_one_mul_negOnePow` — `(−1)ⁱ C(−1, i) = 1` for `i ≥ 0`.
* `mode_neg_one_left` — the iterate formula above.
* `prodCoeff_neg_one_left` — its matrix-coefficient form for products (outer slot).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.MatrixCoeffIterate

open VOA VOA.Huang.MatrixCoeff
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]

/-- `(−1)ⁱ C(−1, i) = 1` for `i ≥ 0`. -/
theorem cbz_neg_one_mul_negOnePow {i : ℤ} (hi : 0 ≤ i) : negOnePow i * cbz (-1) i = 1 := by
  rw [cbz_apply_nonneg _ hi, gBinom_neg_one]
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [negOnePow_natCast, Int.toNat_natCast, ← mul_pow]
  norm_num

/-- **The `u₋₁`-iterate formula** (Jacobi at `(ℓ, m) = (−1, 0)`):
`(u₋₁ w₁)₍ₙ₎ w₂ = Σ_{i ≥ 0} (u₋₁₋ᵢ (w₁)₍ₙ₊ᵢ₎ w₂ + (w₁)₍ₙ₋₁₋ᵢ₎ uᵢ w₂)`. -/
theorem mode_neg_one_left {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (n : ℂ) :
    Y n (mode (A₁.YM u) (-1) w₁) w₂
      = ∑ᶠ i : ℤ, if 0 ≤ i then
          mode (A₃.YM u) (-1 - i) (Y (n + i) w₁ w₂) + Y (n - 1 - i) w₁ (mode (A₂.YM u) i w₂)
        else 0 := by
  have h := hY.jacobi u w₁ w₂ (-1) 0 n
  rw [finsum_eq_single (fun i : ℤ => cbz 0 i • Y (((0 : ℤ) : ℂ) + n - i)
      (mode (A₁.YM u) (-1 + i) w₁) w₂) 0 (fun i hi => by simp [cbz_zero_left, hi])] at h
  simp only [cbz_zero, one_smul, Int.cast_zero, zero_add, sub_zero, add_zero] at h
  rw [← h]
  refine finsum_congr fun i => ?_
  split_ifs with hi
  · rw [cbz_neg_one_mul_negOnePow hi, one_smul]
    have e2 : ((-1 : ℤ) : ℂ) + n - i = n - 1 - (i : ℂ) := by push_cast; ring
    have e3 : negOnePow (-1) = -1 := by
      rw [negOnePow, if_neg]
      exact Int.not_even_iff_odd.mpr ⟨-1, by ring⟩
    simp only [e3, neg_one_smul, sub_neg_eq_add, e2]
  · simp [cbz_apply_neg _ (not_le.mp hi)]

/-- The matrix-coefficient form, outer slot of a product:
`⟨f, 𝒴₁(u₋₁w₁)₍ₙ₁₎ 𝒴₂(w₂)₍ₙ₂₎ w₃⟩` is the pairing of `f` with the finite sum of
`mode_neg_one_left`. -/
theorem prodCoeff_neg_one_left {M₄ M₅ : Type u} [AddCommGroup M₄] [Module ℂ M₄]
    [AddCommGroup M₅] [Module ℂ M₅] {A₁ : OrdVModule W M₁} {A₅ : OrdVModule W M₅}
    {A₄ : OrdVModule W M₄} {Y₁ : IntertwiningModes M₁ M₅ M₄} {Y₂ : IntertwiningModes M₂ M₃ M₅}
    (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁) (u : 𝒱) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂)
    (w₃ : M₃) (n₁ n₂ : ℂ) :
    prodCoeff Y₁ Y₂ f (mode (A₁.YM u) (-1) w₁) w₂ w₃ n₁ n₂
      = f (∑ᶠ i : ℤ, if 0 ≤ i then
          mode (A₄.YM u) (-1 - i) (Y₁ (n₁ + i) w₁ (Y₂ n₂ w₂ w₃))
            + Y₁ (n₁ - 1 - i) w₁ (mode (A₅.YM u) i (Y₂ n₂ w₂ w₃))
        else 0) := by
  rw [prodCoeff, mode_neg_one_left hY₁]

end VOA.Huang.MatrixCoeffIterate
