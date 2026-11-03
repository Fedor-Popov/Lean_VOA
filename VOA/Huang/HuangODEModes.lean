/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.MatrixCoeffIterate
import VOA.Huang.HuangODEAlgebra
import VOA.Core.FieldCombinatorics

/-!
# Mode identities behind Huang's generators `𝒜, ℬ, 𝒞` (VOA part, modes)

For FHL intertwining operators, the three families of Huang's submodule `J` (CCM 7 (2005), §1)
that move a `C₁`-vector `u₋₁w` out of one of the three *vector* slots of a product
`⟨f, 𝒴₁(w₁, z₁) 𝒴₂(w₂, z₂) w₃⟩` (or of an iterate `⟨f, 𝒴₃(𝒴₄(w₁, z₀) w₂, z₂) w₃⟩`) are, in
modes, finite combinations of three moves:

* the **commutator formula** with an arbitrary integral mode (`comm_range`);
* the **`u₋₁`-iterate formula** (`negOneLeft_range`, from `mode_neg_one_left`);
* the **general iterate formula** `(u₍ℓ₎ w)₍ₙ₎` for `ℓ < 0` (`iterate_range`, Jacobi at `m = 0`),
  needed for iterates;
* moving a mode onto the functional `f`: `f ∘ u₍ₘ₎` (Huang's fourth family `𝒟` is then the
  statement that the functionals are spanned by such `g ∘ u₍ₘ₎`, `m ≥ 2 wt u − 1`:
  `HuangODEProduct.DualC1Graded`).

All sums are written over `Finset.range` with explicit truncation bounds.

## Main results
* `finsum_eq_sum_range` — finite `ℤ`-sums supported in `[0, K)`.
* `comm_range`, `negOneLeft_range`, `iterate_range` — the three moves.
* `gBinom_nat`, `gBinom_neg_one_sub` — `C(n, k) = (n choose k)`, `C(−1−i, k) = (−1)^k C(i+k, k)`.
* `prod_slot3`, `prod_slot2`, `prod_slot1` — the mode content of `φ(𝒞) = φ(ℬ) = φ(𝒜) = 0` for
  products (each a pure mode identity, no index arithmetic hidden).  The functional slot
  (`prod_slot0`) and the iterate identities are assembled where they are used
  (`Huang/HuangODEProduct.lean`, `Huang/HuangODEIterate.lean`).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.HuangODEModes

open VOA
open scoped BigOperators

universe u

/-! ## Finite sums and binomial coefficients -/

/-- A finite `ℤ`-sum supported in `[0, K)` is a `Finset.range K` sum. -/
theorem finsum_eq_sum_range {X : Type*} [AddCommMonoid X] (g : ℤ → X) (K : ℕ)
    (h : ∀ i : ℤ, i < 0 ∨ (K : ℤ) ≤ i → g i = 0) :
    ∑ᶠ i : ℤ, g i = ∑ k ∈ Finset.range K, g k := by
  rw [finsum_eq_sum_of_support_subset g (s := (Finset.range K).map Nat.castEmbedding)]
  · rw [Finset.sum_map]; rfl
  · intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Nat.castEmbedding_apply]
    by_contra hcon
    apply hi
    apply h
    by_contra hcon'
    push_neg at hcon'
    exact hcon ⟨i.toNat, by omega, by omega⟩

theorem gBinom_nat (n k : ℕ) : gBinom (n : ℤ) k = (n.choose k : ℂ) := by
  rcases le_or_gt k n with hk | hk
  · exact VOA.FieldCombinatorics.gBinom_natCast_eq_choose hk
  · rw [Nat.choose_eq_zero_of_lt hk, gBinom, Nat.cast_zero]
    rw [Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr hk) (by push_cast; ring), zero_div]

theorem cbz_nat (n k : ℕ) : cbz (n : ℤ) (k : ℤ) = (n.choose k : ℂ) := by
  rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast, gBinom_nat]

theorem gBinom_neg_one_sub (i k : ℕ) :
    gBinom (-1 - (i : ℤ)) k = (-1) ^ k * ((i + k).choose k : ℂ) := by
  have h := VOA.FieldCombinatorics.gBinom_negsucc i k
  rw [show (-(i : ℤ) - 1) = -1 - (i : ℤ) by ring] at h
  rw [h, ← Nat.choose_symm_add, Nat.cast_add_choose]
  ring

theorem cbz_neg_one_sub (i k : ℕ) :
    cbz (-1 - (i : ℤ)) (k : ℤ) = (-1) ^ k * ((i + k).choose k : ℂ) := by
  rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast, gBinom_neg_one_sub]

/-! ## The three moves -/

section Moves

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {Y : IntertwiningModes M₁ M₂ M₃}

/-- The commutator formula with a `Finset.range` sum. -/
theorem comm_range (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (m : ℤ) (n : ℂ) (K : ℕ) (hK : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0) :
    Y n w₁ (mode (A₂.YM u) m w₂)
      = mode (A₃.YM u) m (Y n w₁ w₂)
        - ∑ k ∈ Finset.range K, cbz m k • Y (m + n - k) (mode (A₁.YM u) k w₁) w₂ := by
  have h := hY.commutator u w₁ w₂ m n
  rw [finsum_eq_sum_range _ K (fun i hi => by
    rcases hi with hi | hi
    · simp [cbz_apply_neg m hi]
    · rw [hK i hi]; simp)] at h
  simp only [Int.cast_natCast] at h
  rw [← h]; abel

/-- The `u₋₁`-iterate formula with a `Finset.range` sum (`I` beyond both truncations). -/
theorem negOneLeft_range (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (n : ℂ) (I : ℕ)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y (n + i) w₁ w₂ = 0 ∧ mode (A₂.YM u) i w₂ = 0) :
    Y n (mode (A₁.YM u) (-1) w₁) w₂
      = ∑ i ∈ Finset.range I, (mode (A₃.YM u) (-1 - i) (Y (n + i) w₁ w₂)
          + Y (n - 1 - i) w₁ (mode (A₂.YM u) i w₂)) := by
  rw [VOA.Huang.MatrixCoeffIterate.mode_neg_one_left hY]
  rw [finsum_eq_sum_range _ I (fun i hi => by
    rcases hi with hi | hi
    · simp [not_le.mpr hi]
    · obtain ⟨h1, h2⟩ := hI i hi
      rw [h1, h2]; simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_pos (by positivity)]
  simp only [Int.cast_natCast]

/-- The iterate formula `(u₍ℓ₎ w₁)₍ₙ₎ w₂` (Jacobi at `m = 0`) with `Finset.range` sums. -/
theorem iterate_range (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ : ℤ) (n : ℂ) (I : ℕ)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y (n + i) w₁ w₂ = 0 ∧ mode (A₂.YM u) i w₂ = 0) :
    Y n (mode (A₁.YM u) ℓ w₁) w₂
      = ∑ i ∈ Finset.range I, (negOnePow i * cbz ℓ i) •
          (mode (A₃.YM u) (ℓ - i) (Y (n + i) w₁ w₂)
            - negOnePow ℓ • Y (ℓ + n - i) w₁ (mode (A₂.YM u) i w₂)) := by
  have h := hY.jacobi u w₁ w₂ ℓ 0 n
  rw [finsum_eq_single (fun i : ℤ => cbz 0 i • Y (((0 : ℤ) : ℂ) + n - i)
      (mode (A₁.YM u) (ℓ + i) w₁) w₂) 0 (fun i hi => by simp [cbz_zero_left, hi])] at h
  simp only [cbz_zero, one_smul, Int.cast_zero, zero_add, sub_zero, add_zero] at h
  rw [← h]
  rw [finsum_eq_sum_range _ I (fun i hi => by
    rcases hi with hi | hi
    · simp [cbz_apply_neg ℓ hi]
    · obtain ⟨h1, h2⟩ := hI i hi
      rw [h1, h2]; simp)]
  simp only [Int.cast_natCast]

end Moves

/-! ## Products -/

section Product

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}
  {Y₁ : IntertwiningModes M₁ M₅ M₄} {Y₂ : IntertwiningModes M₂ M₃ M₅}

/-- **Slot 3 (`𝒞`)**: `u₋₁` on `w₃` moves onto `f`, `w₁`, `w₂` (two commutators). -/
theorem prod_slot3 (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (u : 𝒱) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂)
    (w₃ : M₃) (p q : ℂ) (K : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0) :
    f (Y₁ p w₁ (Y₂ q w₂ (mode (A₃.YM u) (-1) w₃)))
      = f (mode (A₄.YM u) (-1) (Y₁ p w₁ (Y₂ q w₂ w₃)))
        - ∑ k ∈ Finset.range K, cbz (-1) k * f (Y₁ (-1 + p - k) (mode (A₁.YM u) k w₁)
            (Y₂ q w₂ w₃))
        - ∑ k ∈ Finset.range K, cbz (-1) k * f (Y₁ p w₁ (Y₂ (-1 + q - k)
            (mode (A₂.YM u) k w₂) w₃)) := by
  rw [comm_range hY₂ u w₂ w₃ (-1) q K hK₂, map_sub, comm_range hY₁ u w₁ _ (-1) p K hK₁]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  push_cast
  abel

/-- **Slot 2 (`ℬ`)**: `u₋₁` on `w₂` (iterate formula for `𝒴₂`, then a commutator through
`𝒴₁` with the mode `u₍₋₁₋ᵢ₎`). -/
theorem prod_slot2 (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (u : 𝒱) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂)
    (w₃ : M₃) (p q : ℂ) (K I : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₂ (q + i) w₂ w₃ = 0 ∧ mode (A₃.YM u) i w₃ = 0) :
    f (Y₁ p w₁ (Y₂ q (mode (A₂.YM u) (-1) w₂) w₃))
      = ∑ i ∈ Finset.range I, (f (mode (A₄.YM u) (-1 - i) (Y₁ p w₁ (Y₂ (q + i) w₂ w₃)))
          - ∑ k ∈ Finset.range K, cbz (-1 - i) k * f (Y₁ ((-1 - i : ℤ) + p - k)
              (mode (A₁.YM u) k w₁) (Y₂ (q + i) w₂ w₃))
          + f (Y₁ p w₁ (Y₂ (q - 1 - i) w₂ (mode (A₃.YM u) i w₃)))) := by
  rw [negOneLeft_range hY₂ u w₂ w₃ q I hI, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_add, comm_range hY₁ u w₁ _ (-1 - i) p K hK₁]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]

/-- **Slot 1 (`𝒜`)**: `u₋₁` on `w₁` (iterate formula for `𝒴₁`, then the commutator of `uᵢ`,
`i ≥ 0`, through `𝒴₂`). -/
theorem prod_slot1 (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) (u : 𝒱) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂)
    (w₃ : M₃) (p q : ℂ) (K I : ℕ) (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₁ (p + i) w₁ (Y₂ q w₂ w₃) = 0 ∧
      mode (A₅.YM u) i (Y₂ q w₂ w₃) = 0) :
    f (Y₁ p (mode (A₁.YM u) (-1) w₁) (Y₂ q w₂ w₃))
      = ∑ i ∈ Finset.range I, (f (mode (A₄.YM u) (-1 - i) (Y₁ (p + i) w₁ (Y₂ q w₂ w₃)))
          + f (Y₁ (p - 1 - i) w₁ (Y₂ q w₂ (mode (A₃.YM u) i w₃)))
          + ∑ k ∈ Finset.range K, cbz i k * f (Y₁ (p - 1 - i) w₁
              (Y₂ ((i : ℤ) + q - k) (mode (A₂.YM u) k w₂) w₃))) := by
  rw [negOneLeft_range hY₁ u w₁ _ p I hI, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc := comm_range hY₂ u w₂ w₃ (i : ℤ) q K hK₂
  rw [eq_sub_iff_add_eq] at hc
  rw [map_add, ← hc]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  push_cast
  ring

end Product

end VOA.Huang.HuangODEModes
