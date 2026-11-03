/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorSkewCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Skew-symmetry on WEAK modules: the Jacobi identity of `Ω_c` — T1b (port, part 2)

A port of `VOA/Huang/BraidingSkewJacobi.lean` from `OrdVModule` to `WeakModule` (only `YM` and
truncation are used).  The defect identity `CD_skew`, `CD_skew_eq_zero`, `AD_eq_zero_of_CD` are
verbatim.  The FHL main theorem (stated with `IsIntertwiningOperator`) is replaced by its
defect-level core `S_skewModes_eq_zero`: **if mode data `𝒴` is truncated and satisfies the
Jacobi identity (all `ℓ, m, n`), then so does `Ω_c(𝒴)` with the roles of `W₁, W₂` swapped**, for
any weak modules.  No `L₋₁`-derivative property is needed for this step.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.LogSkew

open VOA VOA.SkewIntertwiner
open VOA.VertexOperatorAlgebra (mcoeff fallI)
open Module (End)
open scoped BigOperators

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {N₁ : Type v₁} {N₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂] [Module ℂ N₂]
  [AddCommGroup M₃] [Module ℂ M₃]
variable (B₁ : WeakModule W N₁) (B₂ : WeakModule W N₂) (A₃ : WeakModule W M₃)

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
    mode (A₃.YM u) m (sSum (Lm1 A₃) Z n x₁ x₂)
      = ∑ a ∈ Finset.range K, ∑ r ∈ Finset.range K, (sc a * ((-1) ^ r * gBinom m r)) •
          (Lm1 A₃ ^ a)
            (mode (A₃.YM u) (m - r) (Z (n + ((a + r : ℕ) : ℂ)) x₁ x₂)) := by
  set L := Lm1 A₃ with hL
  rw [sSum_eq_sum K hK, map_sum]
  set g : ℕ → ℕ → M₃ := fun r i => (sc i * ((mcoeff m i r : ℤ) : ℂ)) •
    (L ^ (i - r)) (mode (A₃.YM u) (m - r) (Z (n + i) x₁ x₂)) with hg
  have h1 : ∀ i ∈ Finset.range K, mode (A₃.YM u) m (sTerm L Z n x₁ x₂ i)
      = ∑ r ∈ Finset.range K, g r i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [sTerm, map_smul]
    have hx := act_Lm1_pow_expand A₃ u m i (Z (n + i) x₁ x₂)
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
    CD B₁ B₂ A₃ (skewModes (Lm1 A₃) c Z) u x₂ x₁ m n
      = c n • ∑ᶠ t : ℕ, sc t • (Lm1 A₃ ^ t) (AD B₁ B₂ A₃ Z u x₁ x₂ m (n + t)) := by
  set L := Lm1 A₃ with hL
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
    CD B₁ B₂ A₃ (skewModes (Lm1 A₃) c Z) u x₂ x₁ m n = 0 := by
  rw [CD_skew hZ hc]
  rw [finsum_eq_zero_of_forall_eq_zero fun t => by rw [hAD, map_zero, smul_zero], smul_zero]

/-- **Downward induction**: if `Ω_c(Z)` satisfies the commutator formula (with `c ≠ 0`), then
`Z` satisfies the associator formula. -/
theorem AD_eq_zero_of_CD {Z : IntertwiningModes N₁ N₂ M₃} (hZ : Trunc Z) {c : ℂ → ℂ}
    (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0) (u : 𝒱) (x₁ : N₁) (x₂ : N₂) (m : ℤ)
    (hCD : ∀ n, CD B₁ B₂ A₃ (skewModes (Lm1 A₃) c Z) u x₂ x₁ m n = 0) (q : ℂ) :
    AD B₁ B₂ A₃ Z u x₁ x₂ m q = 0 := by
  set L := Lm1 A₃
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
/-! ## The Jacobi identity of `Ω_c` (defect form) -/

section Main

variable {M₁ : Type v₁} {M₂ : Type v₂}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

/-- **Skew-symmetry preserves the Jacobi identity** (FHL Prop. 5.4.7, Jacobi part), for weak
modules: if `Y` is truncated and its Jacobi defect `S A₁ A₂ A₃ Y` vanishes identically, then the
Jacobi defect of `Ω_c(Y)` (type `(W₃ / W₂ W₁)`) vanishes identically. -/
theorem S_skewModes_eq_zero {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}
    {A₃ : WeakModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃} (htY : Trunc Y)
    (hSY : ∀ u w₁ w₂ ℓ m n, S A₁ A₂ A₃ Y u w₁ w₂ ℓ m n = 0) {c : ℂ → ℂ}
    (hc : ∀ n, c (n + 1) = -c n) (hc0 : ∀ n, c n ≠ 0) :
    ∀ u w₂ w₁ ℓ m n, S A₂ A₁ A₃ (skewModes (Lm1 A₃) c Y) u w₂ w₁ ℓ m n = 0 := by
  set L := Lm1 A₃
  have htX : Trunc (skewModes L c Y) := trunc_skewModes c Y
  set c' : ℂ → ℂ := fun n => (c n)⁻¹ with hc'
  have hc'r : ∀ n, c' n * c n = 1 := fun n => inv_mul_cancel₀ (hc0 n)
  have hc's : ∀ n, c' (n + 1) = -c' n := fun n => by simp only [hc', hc n, inv_neg]
  have hc'0 : ∀ n, c' n ≠ 0 := fun n => inv_ne_zero (hc0 n)
  intro u w₂ w₁
  refine eq_zero_of_boundaries _ (S_rec _ htX u w₂ w₁) (fun m n => ?_) (fun ℓ n => ?_)
  · rw [S_zero_left]
    exact CD_skew_eq_zero htY hc u w₂ w₁ m (fun q => by
      rw [← S_zero_mid]; exact hSY u w₁ w₂ m 0 q) n
  · rw [S_zero_mid]
    refine AD_eq_zero_of_CD htX hc's hc'0 u w₂ w₁ ℓ (fun n' => ?_) n
    rw [skewModes_skewModes hc hc'r htY, ← S_zero_left]
    exact hSY u w₁ w₂ 0 ℓ n'

end Main

end VOA.LogSkew
