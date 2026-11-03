/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.BraidingSkew
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Skew-symmetry of intertwining operators (FHL Prop. 5.4.7), part 2

For an intertwining operator `𝒴` of type `(M₃ / M₁ M₂)` and a phase `c` with
`c (n+1) = −c n`, `c n ≠ 0`, the operator `Ω_c(𝒴)(w₂, x) w₁ = e^{xL₋₁} 𝒴(w₁, e^{πi}x) w₂`
(`BraidingSkew.skewModes`) is an intertwining operator of type `(M₃ / M₂ M₁)`
(`isIntertwiningOperator_skewModes`).  Consequently the spaces of intertwining operators of
types `(M₃ / M₁ M₂)` and `(M₃ / M₂ M₁)` are isomorphic (`skewEquiv`) and
`fusionRule_swap : fusionRule A₂ A₁ A₃ = fusionRule A₁ A₂ A₃` — for **any** modules,
unconditionally.

## Proof route (no formal-calculus substitution)
* The **defect identity** `CD_skew`: the commutator defect of `Ω_c(Z)` at `(m, n)` is
  `c n · Σ_t ((−1)ᵗ/t!) L₋₁ᵗ (associator defect of Z at (m, n+t))`
  (the mode form of `e^{−xL₋₁} u_m e^{xL₋₁} = Σ_k C(m,k) xᵏ u_{m−k}`).
* Hence: associator of `𝒴` ⟹ commutator of `Ω_c 𝒴`; and, by downward induction on `t`
  (`AD_eq_zero_of_CD`), commutator of `Ω_{1/c}(Ω_c 𝒴) = 𝒴` ⟹ associator of `Ω_c 𝒴`.
* The Jacobi identity of `Ω_c 𝒴` follows from its two boundary families by the Pascal recurrence
  (`BraidingSkew.S_rec`, `BraidingSkew.eq_zero_of_boundaries`).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.BraidingSkew

open VOA VOA.SkewIntertwiner
open VOA.VertexOperatorAlgebra (mcoeff fallI)
open Module (End)
open scoped BigOperators

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {N₁ : Type v₁} {N₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂] [Module ℂ N₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable (B₁ : OrdVModule W N₁) (B₂ : OrdVModule W N₂) (A₃ : OrdVModule W M₃)

/-! ## The two defects -/

/-- The **commutator defect** of mode data `X` of type `(M₃ / N₂ N₁)`. -/
noncomputable def CD (X : IntertwiningModes N₂ N₁ M₃) (u : 𝒱) (x₂ : N₂) (x₁ : N₁) (m : ℤ)
    (n : ℂ) : M₃ :=
  mode (A₃.YM u) m (X n x₂ x₁) - X n x₂ (mode (B₁.YM u) m x₁)
    - ∑ᶠ i : ℤ, cbz m i • X (m + n - i) (mode (B₂.YM u) i x₂) x₁

/-- The **associator defect** of mode data `Z` of type `(M₃ / N₁ N₂)`. -/
noncomputable def AD (Z : IntertwiningModes N₁ N₂ M₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (ℓ : ℤ)
    (q : ℂ) : M₃ :=
  (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) • (mode (A₃.YM u) (ℓ - i) (Z (q + i) x₁ x₂)
      - negOnePow ℓ • Z (ℓ + q - i) x₁ (mode (B₂.YM u) i x₂)))
    - Z q (mode (B₁.YM u) ℓ x₁) x₂

/-- The Jacobi defect at `ℓ = 0` is the commutator defect. -/
theorem S_zero_left (X : IntertwiningModes N₂ N₁ M₃) (u : 𝒱) (x₂ : N₂) (x₁ : N₁) (m : ℤ)
    (n : ℂ) : S B₂ B₁ A₃ X u x₂ x₁ 0 m n = CD B₁ B₂ A₃ X u x₂ x₁ m n := by
  rw [S, JL, JR, CD, finsum_eq_single _ (0 : ℤ)
    (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
  simp [negOnePow]

/-- The Jacobi defect at `m = 0` is the associator defect. -/
theorem S_zero_mid (Z : IntertwiningModes N₁ N₂ M₃) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (ℓ : ℤ)
    (q : ℂ) : S B₁ B₂ A₃ Z u x₁ x₂ ℓ 0 q = AD B₁ B₂ A₃ Z u x₁ x₂ ℓ q := by
  rw [S, JL, JR, AD, finsum_eq_single (fun i : ℤ => cbz 0 i • Z ((0 : ℤ) + q - i)
      (mode (B₁.YM u) (ℓ + i) x₁) x₂) (0 : ℤ)
    (fun i hi => by dsimp only; rw [cbz_zero_left, if_neg hi, zero_smul])]
  simp

variable {B₁ B₂ A₃}

/-! ## Expansion of `u_m` through the skew sum -/

theorem scalar_re (m : ℤ) (a r : ℕ) :
    sc (a + r) * ((mcoeff m (a + r) r : ℤ) : ℂ) = sc a * ((-1) ^ r * gBinom m r) := by
  have hfac := Nat.add_choose_mul_factorial_mul_factorial a r
  have hfacC : (((a + r).choose r : ℕ) : ℂ) * (a.factorial : ℂ) * (r.factorial : ℂ)
      = ((a + r).factorial : ℂ) := by exact_mod_cast hfac
  have ha : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hr : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hC : (((a + r).choose r : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left r a)).ne'
  rw [mcoeff, fallI, gBinom, sc, sc]
  push_cast
  rw [← hfacC, pow_add]
  field_simp

theorem act_sSum_expand (Z : IntertwiningModes N₁ N₂ M₃) (u : 𝒱) (m : ℤ) (n : ℂ) (x₁ : N₁)
    (x₂ : N₂) (K : ℕ) (hK : ∀ j : ℕ, K ≤ j → Z (n + j) x₁ x₂ = 0) :
    mode (A₃.YM u) m (sSum (Lm1 A₃.toWeakModule) Z n x₁ x₂)
      = ∑ a ∈ Finset.range K, ∑ r ∈ Finset.range K, (sc a * ((-1) ^ r * gBinom m r)) •
          (Lm1 A₃.toWeakModule ^ a)
            (mode (A₃.YM u) (m - r) (Z (n + ((a + r : ℕ) : ℂ)) x₁ x₂)) := by
  set L := Lm1 A₃.toWeakModule with hL
  rw [sSum_eq_sum K hK, map_sum]
  set g : ℕ → ℕ → M₃ := fun r i => (sc i * ((mcoeff m i r : ℤ) : ℂ)) •
    (L ^ (i - r)) (mode (A₃.YM u) (m - r) (Z (n + i) x₁ x₂)) with hg
  have h1 : ∀ i ∈ Finset.range K, mode (A₃.YM u) m (sTerm L Z n x₁ x₂ i)
      = ∑ r ∈ Finset.range K, g r i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [sTerm, map_smul]
    have hx := act_Lm1_pow_expand A₃.toWeakModule u m i (Z (n + i) x₁ x₂)
    simp only [WeakModule.act_def] at hx
    rw [hL, hx, Finset.smul_sum]
    rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega : i + 1 ≤ K)) (fun r _ hr => ?_)]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [hg]
      dsimp only
      rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    · rw [Finset.mem_range] at hr
      rw [mcoeff, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_smul,
        smul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_range_shift (g r) K r]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hg]
    dsimp only
    rw [scalar_re, Nat.add_sub_cancel]
  · intro i hi
    rw [hg]
    dsimp only
    rw [mcoeff, Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, zero_mul, Int.cast_zero, mul_zero,
      zero_smul]
  · intro i hi
    rw [hg]
    dsimp only
    rw [hK i hi, map_zero, map_zero, smul_zero]

/-! ## Eventual vanishing of the associator defect -/

theorem AD_eventually {Z : IntertwiningModes N₁ N₂ M₃} (hZ : Trunc Z) (u : 𝒱) (x₁ : N₁)
    (x₂ : N₂) (ℓ : ℤ) (q : ℂ) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → AD B₁ B₂ A₃ Z u x₁ x₂ ℓ (q + t) = 0 := by
  obtain ⟨K₁, h₁⟩ := hZ.bound x₁ x₂ q
  obtain ⟨K₂, h₂⟩ := hZ.bound (mode (B₁.YM u) ℓ x₁) x₂ q
  obtain ⟨N, hN⟩ := B₂.truncation u x₂
  set J := N.toNat
  have hJ : ∀ i : ℕ, J ≤ i → mode (B₂.YM u) i x₂ = 0 := fun i hi => hN _ (by omega)
  obtain ⟨K₃, h₃⟩ := exists_bound_fin J
    (fun r K => ∀ j : ℕ, K ≤ j → Z ((ℓ : ℂ) + q - r + j) x₁ (mode (B₂.YM u) r x₂) = 0)
    (fun r K K' hKK' hP j hj => hP j (le_trans hKK' hj))
    (fun r => hZ.bound _ _ _)
  refine ⟨K₁ + K₂ + K₃, fun t ht => ?_⟩
  rw [AD, finsum_eq_zero_of_forall_eq_zero fun i => ?_,
    h₂ t (by omega), zero_sub, neg_zero]
  rcases lt_or_ge i 0 with hi | hi
  · rw [cbz_apply_neg ℓ hi, mul_zero, zero_smul]
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, i = r := ⟨i.toNat, by omega⟩
    rw [show q + (t : ℂ) + ((r : ℤ) : ℂ) = q + ((t + r : ℕ) : ℂ) by push_cast; ring,
      h₁ _ (by omega), map_zero]
    by_cases hr : r < J
    · rw [show (ℓ : ℂ) + (q + (t : ℂ)) - ((r : ℤ) : ℂ) = (ℓ : ℂ) + q - (r : ℂ) + t by
          push_cast; ring, h₃ r hr t (by omega), smul_zero, sub_zero, smul_zero]
    · rw [hJ r (by omega), map_zero, smul_zero, sub_zero, smul_zero]

/-! ## The defect identity -/

section Key

variable {Z : IntertwiningModes N₁ N₂ M₃} (hZ : Trunc Z) {c : ℂ → ℂ}
  (hc : ∀ n, c (n + 1) = -c n)
include hZ hc

/-- **The defect identity**: the commutator defect of `Ω_c(Z)` at `(m, n)` is
`c n · Σ_t ((−1)ᵗ/t!) L₋₁ᵗ AD(Z)(m, n + t)`. -/
theorem CD_skew (u : 𝒱) (x₂ : N₂) (x₁ : N₁) (m : ℤ) (n : ℂ) :
    CD B₁ B₂ A₃ (skewModes (Lm1 A₃.toWeakModule) c Z) u x₂ x₁ m n
      = c n • ∑ᶠ t : ℕ, sc t • (Lm1 A₃.toWeakModule ^ t) (AD B₁ B₂ A₃ Z u x₁ x₂ m (n + t)) := by
  set L := Lm1 A₃.toWeakModule with hL
  obtain ⟨K₁, h₁⟩ := hZ.bound x₁ x₂ n
  obtain ⟨K₂, h₂⟩ := hZ.bound (mode (B₁.YM u) m x₁) x₂ n
  obtain ⟨N, hN⟩ := B₂.truncation u x₂
  obtain ⟨T, hT⟩ := AD_eventually (B₁ := B₁) (B₂ := B₂) (A₃ := A₃) hZ u x₁ x₂ m n
  obtain ⟨K₃, h₃⟩ := exists_bound_fin N.toNat
    (fun r K => ∀ j : ℕ, K ≤ j → Z ((m : ℂ) + n - r + j) x₁ (mode (B₂.YM u) r x₂) = 0)
    (fun r K K' hKK' hP j hj => hP j (le_trans hKK' hj))
    (fun r => hZ.bound _ _ _)
  set K := K₁ + K₂ + K₃ + N.toNat + T with hK
  have hb₁ : ∀ j : ℕ, K ≤ j → Z (n + j) x₁ x₂ = 0 := fun j hj => h₁ j (by omega)
  have hb₂ : ∀ j : ℕ, K ≤ j → Z (n + j) (mode (B₁.YM u) m x₁) x₂ = 0 :=
    fun j hj => h₂ j (by omega)
  have hbJ : ∀ i : ℕ, K ≤ i → mode (B₂.YM u) i x₂ = 0 := fun i hi => hN _ (by omega)
  have hb₃ : ∀ r j : ℕ, K ≤ j →
      Z ((m : ℂ) + n - r + j) x₁ (mode (B₂.YM u) r x₂) = 0 := by
    intro r j hj
    by_cases hr : r < N.toNat
    · exact h₃ r hr j (by omega)
    · rw [hN r (by omega), map_zero]
  -- the associator defect as a finite sum
  have hAD : ∀ a : ℕ, AD B₁ B₂ A₃ Z u x₁ x₂ m (n + a)
      = ∑ r ∈ Finset.range K, (negOnePow r * gBinom m r) •
          (mode (A₃.YM u) (m - r) (Z (n + ((a + r : ℕ) : ℂ)) x₁ x₂)
            - negOnePow m • Z ((m : ℂ) + n - r + a) x₁ (mode (B₂.YM u) r x₂))
        - Z (n + a) (mode (B₁.YM u) m x₁) x₂ := by
    intro a
    rw [AD, finsum_int_eq_sum_range _ K]
    · congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [cbz_apply_nonneg m (Int.natCast_nonneg r), Int.toNat_natCast,
        show n + (a : ℂ) + ((r : ℤ) : ℂ) = n + ((a + r : ℕ) : ℂ) by push_cast; ring,
        show (m : ℂ) + (n + (a : ℂ)) - ((r : ℤ) : ℂ) = (m : ℂ) + n - (r : ℂ) + a by
          push_cast; ring]
    · intro i hi
      by_contra hc'
      apply hi
      rcases lt_or_ge i 0 with hneg | hpos
      · rw [cbz_apply_neg m hneg, mul_zero, zero_smul]
      · obtain ⟨r, rfl⟩ : ∃ r : ℕ, i = r := ⟨i.toNat, by omega⟩
        have hr : K ≤ r := by omega
        rw [show n + (a : ℂ) + ((r : ℤ) : ℂ) = n + ((a + r : ℕ) : ℂ) by push_cast; ring,
          hb₁ _ (by omega), map_zero, hbJ r hr, map_zero, smul_zero, sub_zero, smul_zero]
  -- the right side as a finite sum
  have hR : (∑ᶠ t : ℕ, sc t • (L ^ t) (AD B₁ B₂ A₃ Z u x₁ x₂ m (n + t)))
      = (∑ a ∈ Finset.range K, ∑ r ∈ Finset.range K, (sc a * ((-1) ^ r * gBinom m r)) •
            (L ^ a) (mode (A₃.YM u) (m - r) (Z (n + ((a + r : ℕ) : ℂ)) x₁ x₂)))
        - (∑ a ∈ Finset.range K, ∑ r ∈ Finset.range K,
            (sc a * ((-1) ^ r * gBinom m r) * negOnePow m) •
              (L ^ a) (Z ((m : ℂ) + n - r + a) x₁ (mode (B₂.YM u) r x₂)))
        - ∑ a ∈ Finset.range K, sc a • (L ^ a) (Z (n + a) (mode (B₁.YM u) m x₁) x₂) := by
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range K) (fun t ht => by
      rw [Function.mem_support] at ht
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      exact ht (by rw [hT t (by omega), map_zero, smul_zero]))]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hAD a, map_sub, map_sum, smul_sub, Finset.smul_sum, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, map_sub, map_smul, negOnePow_natCast, smul_smul, smul_sub, smul_smul]
  -- the third piece of the commutator defect
  have h3 : (∑ᶠ i : ℤ, cbz m i • skewModes L c Z (m + n - i) (mode (B₂.YM u) i x₂) x₁)
      = c n • ∑ a ∈ Finset.range K, ∑ r ∈ Finset.range K,
            (sc a * ((-1) ^ r * gBinom m r) * negOnePow m) •
              (L ^ a) (Z ((m : ℂ) + n - r + a) x₁ (mode (B₂.YM u) r x₂)) := by
    rw [finsum_int_eq_sum_range _ K]
    · rw [Finset.sum_comm, Finset.smul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [cbz_apply_nonneg m (Int.natCast_nonneg r), Int.toNat_natCast, skewModes_apply hZ,
        Int.cast_natCast, sSum_eq_sum K (hb₃ r), Finset.smul_sum, Finset.smul_sum,
        Finset.smul_sum]
      have hph : c ((m : ℂ) + n - (r : ℂ)) = negOnePow m * (-1) ^ r * c n := by
        have := phase_int hc n (m - r)
        rw [show n + (((m - r : ℤ)) : ℂ) = (m : ℂ) + n - (r : ℂ) by push_cast; ring] at this
        rw [this, show m - (r : ℤ) = m + (-(r : ℤ)) by ring, negOnePow_add,
          VertexOperatorAlgebra.negOnePow_neg', negOnePow_natCast]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [sTerm, hph, smul_smul, smul_smul, smul_smul]
      congr 1
      ring
    · intro i hi
      by_contra hc'
      apply hi
      rcases lt_or_ge i 0 with hneg | hpos
      · rw [cbz_apply_neg m hneg, zero_smul]
      · obtain ⟨r, rfl⟩ : ∃ r : ℕ, i = r := ⟨i.toNat, by omega⟩
        rw [hbJ r (by omega), map_zero, LinearMap.zero_apply, smul_zero]
  rw [hR, CD, skewModes_apply hZ, skewModes_apply hZ, map_smul, act_sSum_expand Z u m n x₁ x₂ K hb₁,
    sSum_eq_sum K hb₂, h3]
  simp only [sTerm, smul_sub]
  abel

end Key

/-! ## Commutator of `Ω` from associator of `𝒴`, and conversely -/

/-- If `Z` satisfies the associator formula, `Ω_c(Z)` satisfies the commutator formula. -/
theorem CD_skew_eq_zero {Z : IntertwiningModes N₁ N₂ M₃} (hZ : Trunc Z) {c : ℂ → ℂ}
    (hc : ∀ n, c (n + 1) = -c n) (u : 𝒱) (x₂ : N₂) (x₁ : N₁) (m : ℤ)
    (hAD : ∀ q, AD B₁ B₂ A₃ Z u x₁ x₂ m q = 0) (n : ℂ) :
    CD B₁ B₂ A₃ (skewModes (Lm1 A₃.toWeakModule) c Z) u x₂ x₁ m n = 0 := by
  rw [CD_skew hZ hc]
  rw [finsum_eq_zero_of_forall_eq_zero fun t => by rw [hAD, map_zero, smul_zero], smul_zero]

/-- **Downward induction**: if `Ω_c(Z)` satisfies the commutator formula (with `c ≠ 0`), then
`Z` satisfies the associator formula. -/
theorem AD_eq_zero_of_CD {Z : IntertwiningModes N₁ N₂ M₃} (hZ : Trunc Z) {c : ℂ → ℂ}
    (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (m : ℤ)
    (hCD : ∀ n, CD B₁ B₂ A₃ (skewModes (Lm1 A₃.toWeakModule) c Z) u x₂ x₁ m n = 0) (q : ℂ) :
    AD B₁ B₂ A₃ Z u x₁ x₂ m q = 0 := by
  set L := Lm1 A₃.toWeakModule
  obtain ⟨T, hT⟩ := AD_eventually (B₁ := B₁) (B₂ := B₂) (A₃ := A₃) hZ u x₁ x₂ m q
  set e : ℕ → M₃ := fun k => AD B₁ B₂ A₃ Z u x₁ x₂ m (q + k) with he
  have hrel : ∀ k : ℕ, ∑ᶠ t : ℕ, sc t • (L ^ t) (e (k + t)) = 0 := by
    intro k
    have h := hCD (q + k)
    rw [CD_skew hZ hc] at h
    have h' := (smul_eq_zero.mp h).resolve_left (hc0 _)
    rw [← h']
    refine finsum_congr fun t => ?_
    rw [he]
    dsimp only
    rw [show q + ((k + t : ℕ) : ℂ) = q + (k : ℂ) + (t : ℂ) by push_cast; ring]
  have key : ∀ d : ℕ, ∀ k : ℕ, T ≤ k + d → e k = 0 := by
    intro d
    induction d with
    | zero => exact fun k hk => hT k (by omega)
    | succ d ih =>
        intro k hk
        have h := hrel k
        rw [finsum_eq_single _ 0 (fun t ht => by
          rw [ih (k + t) (by omega), map_zero, smul_zero])] at h
        simpa [sc] using h
  have := key T 0 (by omega)
  simpa [he] using this

/-! ## The main theorem -/

section Main

variable {M₁ : Type v₁} {M₂ : Type v₂}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

/-- **Skew-symmetry of intertwining operators** (FHL Prop. 5.4.7): for a phase `c` with
`c (n+1) = −c n` and `c n ≠ 0`, `Ω_c(𝒴)(w₂, x)w₁ = e^{xL₋₁}𝒴(w₁, e^{πi}x)w₂` is an intertwining
operator of type `(M₃ / M₂ M₁)` whenever `𝒴` is one of type `(M₃ / M₁ M₂)`.  Any modules. -/
theorem isIntertwiningOperator_skewModes {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) {c : ℂ → ℂ} (hc : ∀ n, c (n + 1) = -c n)
    (hc0 : ∀ n, c n ≠ 0) :
    IsIntertwiningOperator A₂ A₁ A₃ (skewModes (Lm1 A₃.toWeakModule) c Y) := by
  set L := Lm1 A₃.toWeakModule
  have htY : Trunc Y := trunc_of_isIntertwining hY
  have htX : Trunc (skewModes L c Y) := trunc_skewModes c Y
  -- the Jacobi defects of `Y` vanish
  have hSY : ∀ u w₁ w₂ ℓ m n, S A₁ A₂ A₃ Y u w₁ w₂ ℓ m n = 0 := by
    intro u w₁ w₂ ℓ m n
    rw [S, sub_eq_zero]
    exact hY.jacobi u w₁ w₂ ℓ m n
  -- inverse phase
  set c' : ℂ → ℂ := fun n => (c n)⁻¹ with hc'
  have hc'r : ∀ n, c' n * c n = 1 := fun n => inv_mul_cancel₀ (hc0 n)
  have hc's : ∀ n, c' (n + 1) = -c' n := fun n => by simp only [hc', hc n, inv_neg]
  have hc'0 : ∀ n, c' n ≠ 0 := fun n => inv_ne_zero (hc0 n)
  refine ⟨htX, fun w₂ n => skewModes_L_neg_one hY hc w₂ n, ?_⟩
  intro u w₂ w₁ ℓ m n
  have hS : ∀ ℓ m n, S A₂ A₁ A₃ (skewModes L c Y) u w₂ w₁ ℓ m n = 0 := by
    refine eq_zero_of_boundaries _ (S_rec _ htX u w₂ w₁) (fun m n => ?_)
      (fun ℓ n => ?_)
    · -- `ℓ = 0`: commutator of `Ω Y` from the associator of `Y`
      rw [S_zero_left]
      exact CD_skew_eq_zero htY hc u w₂ w₁ m (fun q => by
        rw [← S_zero_mid]; exact hSY u w₁ w₂ m 0 q) n
    · -- `m = 0`: associator of `Ω Y` from the commutator of `Ω_{c'}(Ω_c Y) = Y`
      rw [S_zero_mid]
      refine AD_eq_zero_of_CD htX hc's hc'0 u w₂ w₁ ℓ (fun n' => ?_) n
      rw [skewModes_skewModes hc hc'r htY, ← S_zero_left]
      exact hSY u w₁ w₂ 0 ℓ n'
  have := hS ℓ m n
  rw [S, sub_eq_zero] at this
  exact this

end Main

/-! ## Linearity in `𝒴`, the isomorphism of intertwiner spaces, fusion-rule symmetry -/

section Equiv

variable {M₁ : Type v₁} {M₂ : Type v₂}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

theorem trunc_add {Y Y' : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (hY' : Trunc Y') :
    Trunc (Y + Y') := by
  intro w₁ w₂ n
  obtain ⟨N, hN⟩ := hY w₁ w₂ n
  obtain ⟨N', hN'⟩ := hY' w₁ w₂ n
  refine ⟨max N N', fun k hk => ?_⟩
  simp only [Pi.add_apply, LinearMap.add_apply, hN k (le_trans (le_max_left _ _) hk),
    hN' k (le_trans (le_max_right _ _) hk), add_zero]

theorem trunc_smul {Y : IntertwiningModes M₁ M₂ M₃} (hY : Trunc Y) (a : ℂ) : Trunc (a • Y) := by
  intro w₁ w₂ n
  obtain ⟨N, hN⟩ := hY w₁ w₂ n
  exact ⟨N, fun k hk => by simp only [Pi.smul_apply, LinearMap.smul_apply, hN k hk, smul_zero]⟩

theorem skewModes_add (L : End ℂ M₃) (c : ℂ → ℂ) {Y Y' : IntertwiningModes M₁ M₂ M₃}
    (hY : Trunc Y) (hY' : Trunc Y') :
    skewModes L c (Y + Y') = skewModes L c Y + skewModes L c Y' := by
  funext n
  refine LinearMap.ext fun w₂ => LinearMap.ext fun w₁ => ?_
  simp only [Pi.add_apply, LinearMap.add_apply]
  rw [skewModes_apply (trunc_add hY hY'), skewModes_apply hY, skewModes_apply hY', ← smul_add]
  congr 1
  obtain ⟨K, hK⟩ := hY.bound w₁ w₂ n
  obtain ⟨K', hK'⟩ := hY'.bound w₁ w₂ n
  rw [sSum_eq_sum (K + K') (fun j hj => by
      simp only [Pi.add_apply, LinearMap.add_apply, hK j (by omega), hK' j (by omega), add_zero]),
    sSum_eq_sum (K + K') (fun j hj => hK j (by omega)),
    sSum_eq_sum (K + K') (fun j hj => hK' j (by omega)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sTerm, Pi.add_apply, LinearMap.add_apply, map_add, smul_add]

theorem skewModes_smul (L : End ℂ M₃) (c : ℂ → ℂ) {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : Trunc Y) (a : ℂ) : skewModes L c (a • Y) = a • skewModes L c Y := by
  funext n
  refine LinearMap.ext fun w₂ => LinearMap.ext fun w₁ => ?_
  simp only [Pi.smul_apply, LinearMap.smul_apply]
  rw [skewModes_apply (trunc_smul hY a), skewModes_apply hY, smul_comm a]
  congr 1
  obtain ⟨K, hK⟩ := hY.bound w₁ w₂ n
  rw [sSum_eq_sum K (fun j hj => by
      simp only [Pi.smul_apply, LinearMap.smul_apply, hK j hj, smul_zero]),
    sSum_eq_sum K hK, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sTerm, Pi.smul_apply, LinearMap.smul_apply, map_smul]
  rw [smul_comm]

variable (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) (A₃ : OrdVModule W M₃)

/-- `Ω_c` as a linear map between spaces of intertwining operators. -/
noncomputable def skewMap {c : ℂ → ℂ} (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0) :
    intertwiningSpace A₁ A₂ A₃ →ₗ[ℂ] intertwiningSpace A₂ A₁ A₃ where
  toFun Y := ⟨skewModes (Lm1 A₃.toWeakModule) c Y.1,
    isIntertwiningOperator_skewModes Y.2 hc hc0⟩
  map_add' Y Y' := Subtype.ext (skewModes_add _ c (trunc_of_isIntertwining Y.2)
    (trunc_of_isIntertwining Y'.2))
  map_smul' a Y := Subtype.ext (skewModes_smul _ c (trunc_of_isIntertwining Y.2) a)

@[simp] theorem skewMap_apply {c : ℂ → ℂ} (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0)
    (Y : intertwiningSpace A₁ A₂ A₃) :
    (skewMap A₁ A₂ A₃ hc hc0 Y).1 = skewModes (Lm1 A₃.toWeakModule) c Y.1 := rfl

/-- **The skew-symmetry isomorphism** `I(M₃ / M₁ M₂) ≃ I(M₃ / M₂ M₁)` (FHL Prop. 5.4.7),
with inverse `Ω_{1/c}`. -/
noncomputable def skewEquiv {c : ℂ → ℂ} (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0) :
    intertwiningSpace A₁ A₂ A₃ ≃ₗ[ℂ] intertwiningSpace A₂ A₁ A₃ :=
  have hc' : ∀ n, (fun n => (c n)⁻¹) (n + 1) = -(fun n => (c n)⁻¹) n :=
    fun n => by simp only [hc n, inv_neg]
  have hc'0 : ∀ n, (fun n => (c n)⁻¹) n ≠ 0 := fun n => inv_ne_zero (hc0 n)
  LinearEquiv.ofLinear (skewMap A₁ A₂ A₃ hc hc0) (skewMap A₂ A₁ A₃ hc' hc'0)
    (LinearMap.ext fun Y => Subtype.ext (skewModes_skewModes hc' (fun n => mul_inv_cancel₀ (hc0 n))
      (trunc_of_isIntertwining Y.2)))
    (LinearMap.ext fun Y => Subtype.ext (skewModes_skewModes hc (fun n => inv_mul_cancel₀ (hc0 n))
      (trunc_of_isIntertwining Y.2)))

/-- FHL's phase for `Ω₀`: `c n = e^{−πi(n+1)}`, i.e. `𝒴(w₁, e^{πi}x)`. -/
noncomputable def omegaPhase (n : ℂ) : ℂ := Complex.exp (-(↑Real.pi * Complex.I) * (n + 1))

theorem omegaPhase_succ (n : ℂ) : omegaPhase (n + 1) = -omegaPhase n := by
  rw [omegaPhase, omegaPhase, show -(↑Real.pi * Complex.I) * (n + 1 + 1)
      = -(↑Real.pi * Complex.I) * (n + 1) + -(↑Real.pi * Complex.I) by ring, Complex.exp_add,
    Complex.exp_neg, Complex.exp_pi_mul_I]
  ring

theorem omegaPhase_ne_zero (n : ℂ) : omegaPhase n ≠ 0 := Complex.exp_ne_zero _

/-- **Symmetry of fusion rules** `N^{M₃}_{M₂ M₁} = N^{M₃}_{M₁ M₂}` (FHL Prop. 5.4.7), for any
modules (finite-dimensional or not: both sides are the `finrank` of isomorphic spaces). -/
theorem fusionRule_swap : fusionRule A₂ A₁ A₃ = fusionRule A₁ A₂ A₃ :=
  (skewEquiv A₁ A₂ A₃ omegaPhase_succ omegaPhase_ne_zero).finrank_eq.symm

/-- `FiniteDimensional` transfers along the skew isomorphism. -/
theorem finiteDimensional_swap [FiniteDimensional ℂ (intertwiningSpace A₁ A₂ A₃)] :
    FiniteDimensional ℂ (intertwiningSpace A₂ A₁ A₃) :=
  LinearEquiv.finiteDimensional (skewEquiv A₁ A₂ A₃ omegaPhase_succ omegaPhase_ne_zero)

end Equiv

end VOA.Huang.BraidingSkew
