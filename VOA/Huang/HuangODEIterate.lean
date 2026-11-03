/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangODEProduct

/-!
# Huang's equation for iterates of intertwining operators (iterates)

Huang, CCM 7 (2005), Thms 1.4 and 2.3 at the singular point `z₂⁻¹(z₁ − z₂) = 0` (the case proved in
detail there: regularity at `z₁ = z₂` by the filtration "pole order in `z₁ − z₂` plus weight",
then the degree-0 selection), in the direct one-variable form of `Huang/HuangODEProduct.lean`:
`x = z₀/z₂` (`z₀ = z₁ − z₂`), coefficients in `ℂ[x, (1 + x)⁻¹]` (`ratRing (−1)`; the other finite
singular point `z₁ = 0` is `x = −1`).

`QI = Σₙ f(𝒴₃(𝒴₄(w₁)₍ν+s−n₎ w₂)₍c−ν−2N₄+n₎ w₃) xⁿ`, normalized as `QT`.

## Main results
* `moveIA` (`u₋₁w₁`: `u` passes through `𝒴₄` and then through `𝒴₃` by the iterate formula with
  `ℓ = −1−i`; coefficients `C(i+j, j) x^{2d+2i+j}` and `x Σᵢ C(i+j,j)(−x)ⁱ = x(1+x)^{−j−1}`),
  `moveIB`, `moveIC` (`Σ_k (−1)ᵏ C(k,j) x^{k+1} = (−1)ʲ x · x^j (1+x)^{−j−1}`), `moveID`.
* `qi_mem`; `ratFuchsian_iterSeries_of_C1`;
  `huangIterateODE_of_moduleC1Data`; `huangODEInput_of_moduleC1Input`
  (`ModuleC1Input → HuangODEInput`).

## Status
No `sorry`, no new axioms.  Conditional only on `ModuleC1Input`.
-/

namespace VOA.Huang.HuangODEIterate

open VOA PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence VOA.Huang.HuangODEAlgebra
  VOA.Huang.HuangODEModes VOA.Huang.MatrixCoeff VOA.Huang.HuangODEProduct
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem negOnePow_neg_one_sub (i : ℕ) : negOnePow (-1 - (i : ℤ)) = -(-1 : ℂ) ^ i := by
  unfold negOnePow
  rcases Nat.even_or_odd i with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · have h : ¬ Even (-1 - ((r + r : ℕ) : ℤ)) := by
      rw [Int.not_even_iff_odd]; exact ⟨-r - 1, by push_cast; ring⟩
    rw [if_neg h, ← two_mul, pow_mul]; simp
  · have h : Even (-1 - ((2 * r + 1 : ℕ) : ℤ)) := ⟨-r - 1, by push_cast; ring⟩
    rw [if_pos h, pow_succ, pow_mul]; simp

theorem neg_one_pow_binom (k j : ℕ) :
    (-1 : ℂ) ^ j * ((k.choose j : ℂ) * (-1 : ℂ) ^ (k - j)) = (-1 : ℂ) ^ k * (k.choose j : ℂ) := by
  rcases lt_or_ge k j with h | h
  · rw [Nat.choose_eq_zero_of_lt h]; simp
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show j + t - j = t by omega, pow_add]; ring

section Iterate

variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}
  {Y₃ : IntertwiningModes M₅ M₃ M₄} {Y₄ : IntertwiningModes M₁ M₂ M₅}

/-- `Σ_n f(𝒴₃(𝒴₄(w₁)₍ᵦ₋ₙ₎ w₂)₍ₐ₊ₙ₎ w₃) xⁿ`, `x = z₀/z₂`. -/
noncomputable def iterQ (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (a b : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => f (Y₃ (a + n) (Y₄ (b - n) w₁ w₂) w₃)

theorem coeff_iterQ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (a b : ℂ) (n : ℕ) :
    coeff n (iterQ Y₃ Y₄ f w₁ w₂ w₃ a b) = f (Y₃ (a + n) (Y₄ (b - n) w₁ w₂) w₃) :=
  coeff_mk _ _

theorem iterQ_congr {f : M₄ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {p p' q q' : ℂ}
    (hp : p = p') (hq : q = q') :
    f (Y₃ p (Y₄ q w₁ w₂) w₃) = f (Y₃ p' (Y₄ q' w₁ w₂) w₃) := by
  rw [hp, hq]

theorem iterV_congr {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {p p' q q' : ℂ}
    (hp : p = p') (hq : q = q') :
    Y₃ p (Y₄ q w₁ w₂) w₃ = Y₃ p' (Y₄ q' w₁ w₂) w₃ := by
  rw [hp, hq]

theorem coeff_X_pow_mul_iterQ {f : M₄ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {a b : ℂ}
    (hb : IsBase Y₄ w₁ w₂ b) (e n : ℕ) :
    coeff n (X ^ e * iterQ Y₃ Y₄ f w₁ w₂ w₃ a b)
      = f (Y₃ (a + n - e) (Y₄ (b - n + e) w₁ w₂) w₃) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterQ]
    have e1 : a + ((n - e : ℕ) : ℂ) = a + n - e := by rw [Nat.cast_sub h]; ring
    have e2 : b - ((n - e : ℕ) : ℂ) = b - n + e := by rw [Nat.cast_sub h]; ring
    rw [e1, e2]
  · have e3 : b - n + e = b + (((e - n - 1 : ℕ) : ℂ) + 1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e3, hb, map_zero, LinearMap.zero_apply, map_zero]

theorem coeff_X_mul_binom_mul_iterQ {f : M₄ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {a b : ℂ}
    (hb : IsBase Y₄ w₁ w₂ b) (r : ℂ) (k n I : ℕ) (hI : n < I) :
    coeff n (X * HuangODEAlgebra.binomSeries r k * iterQ Y₃ Y₄ f w₁ w₂ w₃ a b)
      = ∑ i ∈ Finset.range I, ((i.choose k : ℂ) * r ^ (i - k)) *
          f (Y₃ (a + n - 1 - i) (Y₄ (b - n + 1 + i) w₁ w₂) w₃) := by
  have e : X * HuangODEAlgebra.binomSeries r k * iterQ Y₃ Y₄ f w₁ w₂ w₃ a b
      = HuangODEAlgebra.binomSeries r k * X ^ 1 * iterQ Y₃ Y₄ f w₁ w₂ w₃ a b := by ring
  rw [e, HuangODEAlgebra.binomSeries, coeff_conv _ _ _ hI]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [coeff_iterQ]
    have e1 : a + ((n - 1 - i : ℕ) : ℂ) = a + n - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have e2 : b - ((n - 1 - i : ℕ) : ℂ) = b - n + 1 + i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e1, e2]
  · have e3 : b - n + 1 + i = b + (((i - n : ℕ) : ℂ) + 1) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [e3, hb, map_zero, LinearMap.zero_apply, map_zero, mul_zero]

/-- The vector of an iterate lies on one weight. -/
theorem iter_mem_weight (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) {α₁ α₂ α₃ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂) (h₃ : w₃ ∈ A₃.weight α₃) (p q : ℂ) :
    Y₃ p (Y₄ q w₁ w₂) w₃ ∈ A₄.weight (α₁ + α₂ + α₃ - p - q - 2) := by
  have hin := VOA.Huang.FusionTop.mem_weight hY₄ h₁ h₂ q
  have hout := VOA.Huang.FusionTop.mem_weight hY₃ hin h₃ p
  have e : α₁ + α₂ - q - 1 + α₃ - p - 1 = α₁ + α₂ + α₃ - p - q - 2 := by ring
  rw [e] at hout
  exact hout

/-- The normalized series of an iterate tuple (same normalization as `QT`). -/
noncomputable def QI (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (c ν : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (N₄ s : ℕ) : PowerSeries ℂ :=
  iterQ Y₃ Y₄ f w₁ w₂ w₃ (c - ν - 2 * N₄) (ν + s)

section Moves

variable {h₁ h₂ h₃ h₄ ν : ℂ}

/-- **Iterate move, innermost-right vector `u₋₁w₃`** (Huang's `𝒞` for `ψ`): a relation
regular at `x = 0` with poles only at `x = −1`. -/
theorem moveIC (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₄ : IsLowestWeight A₄ h₄)
    (hUB : UnifBase A₁ A₂ Y₄ h₁ h₂ ν) {d : ℕ} {u : 𝒱} (hu : u ∈ W.grading (d : ℤ))
    (f : M₄ →ₗ[ℂ] ℂ) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) :
    QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ (mode (A₃.YM u) (-1) w₃) N₄
        (N₁ + N₂ + N₃ + d + N₄)
      = (if d ≤ N₄ then X ^ (2 * d) *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν (f ∘ₗ mode (A₄.YM u) (-1)) w₁ w₂ w₃
            (N₄ - d) (N₁ + N₂ + N₃ + (N₄ - d)) else 0)
        - ∑ k ∈ Finset.range (N₂ + d), ((-1 : ℂ) ^ k) • (X ^ (k + 1) *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ (mode (A₂.YM u) (k : ℤ) w₂) w₃ N₄
            (N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))
        - ∑ j ∈ Finset.range (N₁ + d), ((-1 : ℂ) ^ j) • (X * HuangODEAlgebra.binomSeries (-1) j *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f (mode (A₁.YM u) (j : ℤ) w₁) w₂ w₃ N₄
            (N₁ + d - (j + 1) + N₂ + N₃ + N₄)) := by
  ext n
  rw [map_sub, map_sub, map_sum, map_sum, QI, coeff_iterQ]
  obtain ⟨T, hT⟩ := A₅.truncation u (Y₄ (ν + ((N₁ + N₂ + N₃ + d + N₄ : ℕ) : ℂ) - n) w₁ w₂)
  have hT' := Int.self_le_toNat T
  rw [comm_range hY₃ u _ w₃ (-1) _ (T.toNat + n + N₂ + N₁ + d + 1)
    (fun k hk => hT k (by push_cast at hk; omega))]
  rw [map_sub, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hsplit : ∀ k ∈ Finset.range (T.toNat + n + N₂ + N₁ + d + 1),
      cbz (-1) (k : ℤ) * f (Y₃ (((-1 : ℤ) : ℂ) + (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n) - k)
        (mode (A₅.YM u) (k : ℤ) (Y₄ (ν + ((N₁ + N₂ + N₃ + d + N₄ : ℕ) : ℂ) - n) w₁ w₂)) w₃)
      = (-1 : ℂ) ^ k * f (Y₃ (((-1 : ℤ) : ℂ) + (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n) - k)
          (Y₄ (ν + ((N₁ + N₂ + N₃ + d + N₄ : ℕ) : ℂ) - n) w₁ (mode (A₂.YM u) (k : ℤ) w₂)) w₃)
        + ∑ j ∈ Finset.range (N₁ + d), (-1 : ℂ) ^ k * ((k.choose j : ℂ) *
          f (Y₃ (((-1 : ℤ) : ℂ) + (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n) - k)
            (Y₄ ((k : ℤ) + (ν + ((N₁ + N₂ + N₃ + d + N₄ : ℕ) : ℂ) - n) - j)
              (mode (A₁.YM u) (j : ℤ) w₁) w₂) w₃)) := by
    intro k _
    have hc := comm_range hY₄ u w₁ w₂ (k : ℤ) (ν + ((N₁ + N₂ + N₃ + d + N₄ : ℕ) : ℂ) - n)
      (N₁ + d) (fun j hj => mode_eq_zero_of_le hl₁ hu hw₁ (by push_cast at hj ⊢; omega))
    rw [eq_sub_iff_add_eq] at hc
    rw [← hc, cbz_neg_one_nat]
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.coeFn_sum,
      Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, cbz_nat]
    rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  refine Eq.trans ?_ (sub_sub _ _ _).symm
  refine congrArg₂ (· - ·) ?_ (congrArg₂ (· + ·) ?_ ?_)
  · split_ifs with hd
    · rw [QI, coeff_X_pow_mul_iterQ (hUB.base hw₁ hw₂ (by omega)), LinearMap.comp_apply]
      obtain ⟨r, rfl⟩ : ∃ r, N₄ = d + r := ⟨N₄ - d, by omega⟩
      have e : d + r - d = r := by omega
      rw [e]
      congr 3 <;> push_cast <;> ring
    · rw [map_zero, eq_zero_of_mem_weight_neg hl₄ (iter_mem_weight hY₃ hY₄ hw₁ hw₂ hw₃ _ _)
        (j := (N₄ : ℤ) - d) (by push_cast; ring) (by omega), map_zero, map_zero]
  · rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega), map_zero, map_zero, LinearMap.zero_apply,
        map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [QI, coeff_X_pow_mul_iterQ (hUB.base hw₁ (mode_mem_weight_nat hu hw₂ hk)
      (by omega))]
    obtain ⟨r, hr⟩ : ∃ r, N₂ + d = k + 1 + r := ⟨N₂ + d - (k + 1), by omega⟩
    have e : N₂ + d - (k + 1) = r := by omega
    rw [e]
    have hr' : (N₂ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    exact congrArg _ (iterQ_congr (by push_cast; ring) (by push_cast; linear_combination hr'))
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    rw [QI, coeff_X_mul_binom_mul_iterQ (hUB.base (mode_mem_weight_nat hu hw₁ hj) hw₂
      (by omega)) (-1) j n (T.toNat + n + N₂ + N₁ + d + 1) (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc ((-1 : ℂ) ^ j), neg_one_pow_binom]
    obtain ⟨r, hr⟩ : ∃ r, N₁ + d = j + 1 + r := ⟨N₁ + d - (j + 1), by omega⟩
    have e : N₁ + d - (j + 1) = r := by omega
    rw [e]
    have hr' : (N₁ : ℂ) + d = j + 1 + r := by exact_mod_cast hr
    rw [← mul_assoc]
    refine congrArg _ (iterQ_congr ?_ ?_)
    · push_cast; ring
    · push_cast; linear_combination hr'

/-- **Iterate move, inner-right vector `u₋₁w₂`** (Huang's `ℬ` for `ψ`). -/
theorem moveIB (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hUB : UnifBase A₁ A₂ Y₄ h₁ h₂ ν) {d : ℕ} {u : 𝒱} (hu : u ∈ W.grading (d : ℤ))
    (f : M₄ →ₗ[ℂ] ℂ) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) :
    QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ (mode (A₂.YM u) (-1) w₂) w₃ N₄
        (N₁ + N₂ + d + N₃ + N₄)
      = ∑ i ∈ Finset.range (N₄ + 1 - d), X ^ (2 * d + i) *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν (f ∘ₗ mode (A₄.YM u) (-1 - (i : ℤ))) w₁ w₂ w₃
            (N₄ - (d + i)) (N₁ + N₂ + N₃ + (N₄ - (d + i)))
        + ∑ i ∈ Finset.range (N₃ + d), X ^ (i + 1) *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ (mode (A₃.YM u) (i : ℤ) w₃) N₄
            (N₁ + N₂ + (N₃ + d - (i + 1)) + N₄)
        - ∑ k ∈ Finset.range (N₁ + d), ((-1 : ℂ) ^ k) •
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f (mode (A₁.YM u) (k : ℤ) w₁) w₂ w₃ N₄
            (N₁ + d - (k + 1) + N₂ + N₃ + N₄) := by
  ext n
  rw [map_sub, map_add, map_sum, map_sum, map_sum, QI, coeff_iterQ]
  rw [comm_range hY₄ u w₁ w₂ (-1) _ (N₁ + d)
    (fun k hk => mode_eq_zero_of_le hl₁ hu hw₁ (by push_cast at hk ⊢; omega))]
  rw [map_sub, LinearMap.sub_apply, map_sub]
  obtain ⟨T, hT⟩ := hY₃.truncation (Y₄ (ν + ((N₁ + N₂ + d + N₃ + N₄ : ℕ) : ℂ) - n) w₁ w₂) w₃
    (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n)
  have hT' := Int.self_le_toNat T
  rw [negOneLeft_range hY₃ u _ w₃ _ (T.toNat + n + N₄ + N₃ + d + 1)
    (fun i hi => ⟨hT i (by push_cast at hi; omega),
      mode_eq_zero_of_le hl₃ hu hw₃ (by push_cast at hi ⊢; omega)⟩)]
  simp only [map_add, map_sum, LinearMap.coeFn_sum, Finset.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · rw [sum_range_trim (J := N₄ + 1 - d) (by omega) (fun i hi => by
      rw [eq_zero_of_mem_weight_neg hl₄ (iter_mem_weight hY₃ hY₄ hw₁ hw₂ hw₃ _ _)
        (j := (N₄ : ℤ) - d - i) (by push_cast; ring) (by omega), map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [QI, coeff_X_pow_mul_iterQ (hUB.base hw₁ hw₂ (by omega)), LinearMap.comp_apply]
    obtain ⟨r, rfl⟩ : ∃ r, N₄ = d + i + r := ⟨N₄ - (d + i), by omega⟩
    have e : d + i + r - (d + i) = r := by omega
    rw [e]
    congr 3 <;> push_cast <;> ring
  · rw [sum_range_trim (J := N₃ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega), map_zero, map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [QI, coeff_X_pow_mul_iterQ (hUB.base hw₁ hw₂ (by omega))]
    obtain ⟨r, hr⟩ : ∃ r, N₃ + d = i + 1 + r := ⟨N₃ + d - (i + 1), by omega⟩
    have e : N₃ + d - (i + 1) = r := by omega
    rw [e]
    have hr' : (N₃ : ℂ) + d = i + 1 + r := by exact_mod_cast hr
    refine iterQ_congr ?_ ?_
    · push_cast; ring
    · push_cast; linear_combination hr'
  · refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [QI, coeff_iterQ, cbz_neg_one_nat]
    obtain ⟨r, hr⟩ : ∃ r, N₁ + d = k + 1 + r := ⟨N₁ + d - (k + 1), by omega⟩
    have e : N₁ + d - (k + 1) = r := by omega
    rw [e]
    have hr' : (N₁ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    refine congrArg _ (iterQ_congr ?_ ?_)
    · push_cast; ring
    · push_cast; linear_combination hr'

/-- The iterate formula for `u₍₋₁₋ᵢ₎` in the first slot of `𝒴₃`, with its signs evaluated:
`C(−1−i, j)(−1)ʲ = C(i+j, j)` and `−(−1)^{−1−i} = (−1)ⁱ`. -/
theorem iter_neg_left_expand (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃) (u : 𝒱)
    (f : M₄ →ₗ[ℂ] ℂ) (m : M₅) (w₃ : M₃) (p : ℂ) (i I : ℕ)
    (hI : ∀ j : ℤ, (I : ℤ) ≤ j → Y₃ (p + j) m w₃ = 0 ∧ mode (A₃.YM u) j w₃ = 0) :
    f (Y₃ p (mode (A₅.YM u) (-1 - (i : ℤ)) m) w₃)
      = ∑ j ∈ Finset.range I, ((i + j).choose j : ℂ) *
          f (mode (A₄.YM u) (-1 - (i : ℤ) - (j : ℤ)) (Y₃ (p + j) m w₃))
        + ∑ j ∈ Finset.range I, ((i + j).choose j : ℂ) * (-1 : ℂ) ^ i *
          f (Y₃ (((-1 - (i : ℤ) : ℤ) : ℂ) + p - j) m (mode (A₃.YM u) (j : ℤ) w₃)) := by
  rw [iterate_range hY₃ u m w₃ (-1 - (i : ℤ)) p I hI, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul, negOnePow_natCast,
    cbz_neg_one_sub, negOnePow_neg_one_sub]
  have h2 : ((-1 : ℂ) ^ j) * ((-1 : ℂ) ^ j) = 1 := by rw [← mul_pow]; norm_num
  linear_combination (((i + j).choose j : ℂ) * f (mode (A₄.YM u) (-1 - (i : ℤ) - (j : ℤ))
      (Y₃ (p + j) m w₃)) + ((i + j).choose j : ℂ) * (-1 : ℂ) ^ i *
      f (Y₃ (((-1 - (i : ℤ) : ℤ) : ℂ) + p - j) m (mode (A₃.YM u) (j : ℤ) w₃))) * h2

/-- **Iterate move, inner-left vector `u₋₁w₁`** (Huang's `𝒜` for `ψ`): the hardest one —
`u₋₁` passes through `𝒴₄` (iterate formula) and then through `𝒴₃` (iterate formula with
`ℓ = −1−i`); the resulting coefficients are `C(i+j, j) x^{2d+2i+j}` (polynomials) and
`Σᵢ C(i+j,j)(−x)ⁱ = (1+x)^{−j−1}` (pole at `x = −1` only). -/
theorem moveIA (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) (hl₂ : IsLowestWeight A₂ h₂)
    (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hUB : UnifBase A₁ A₂ Y₄ h₁ h₂ ν) {d : ℕ} {u : 𝒱} (hu : u ∈ W.grading (d : ℤ))
    (f : M₄ →ₗ[ℂ] ℂ) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) :
    QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f (mode (A₁.YM u) (-1) w₁) w₂ w₃ N₄
        (N₁ + d + N₂ + N₃ + N₄)
      = ∑ i ∈ Finset.range (N₄ + 1), ∑ j ∈ Finset.range (N₄ + 1),
          (if d + i + j ≤ N₄ then ((i + j).choose j : ℂ) • (X ^ (2 * d + 2 * i + j) *
            QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν
              (f ∘ₗ mode (A₄.YM u) (-1 - (i : ℤ) - (j : ℤ))) w₁ w₂ w₃
              (N₄ - (d + i + j)) (N₁ + N₂ + N₃ + (N₄ - (d + i + j)))) else 0)
        + ∑ j ∈ Finset.range (N₃ + d), X * HuangODEAlgebra.binomSeries (-1) j *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ (mode (A₃.YM u) (j : ℤ) w₃) N₄
            (N₁ + N₂ + (N₃ + d - (j + 1)) + N₄)
        + ∑ i ∈ Finset.range (N₂ + d),
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ (mode (A₂.YM u) (i : ℤ) w₂) w₃ N₄
            (N₁ + (N₂ + d - (i + 1)) + N₃ + N₄) := by
  ext n
  simp only [map_add, map_sum]
  rw [QI, coeff_iterQ]
  generalize hP : h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * (N₄ : ℂ) + n = P
  generalize hQ : ν + ((N₁ + d + N₂ + N₃ + N₄ : ℕ) : ℂ) - n = Q
  -- the vectors that vanish for weight reasons
  have hvan : ∀ i j : ℕ, N₄ < d + i + j → Y₃ (P + j) (Y₄ (Q + i) w₁ w₂) w₃ = 0 := by
    intro i j hij
    refine eq_zero_of_mem_weight_neg hl₄ (iter_mem_weight hY₃ hY₄ hw₁ hw₂ hw₃ _ _)
      (j := (N₄ : ℤ) - d - i - j) ?_ (by omega)
    rw [← hP, ← hQ]; push_cast; ring
  obtain ⟨T, hT⟩ := hY₄.truncation w₁ w₂ Q
  have hT' := Int.self_le_toNat T
  set I₁ := T.toNat + n + N₂ + d + N₄ + N₃ + 1 with hI₁
  set I₂ := N₄ + N₃ + d + 1 with hI₂
  rw [negOneLeft_range hY₄ u w₁ w₂ Q I₁ (fun i hi => ⟨hT i (by push_cast at hi; omega),
    mode_eq_zero_of_le hl₂ hu hw₂ (by push_cast at hi ⊢; omega)⟩)]
  simp only [map_sum, map_add, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.add_apply,
    Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun (i : ℕ) _ => iter_neg_left_expand hY₃ u f
    (Y₄ (Q + (i : ℂ)) w₁ w₂) w₃ P i I₂
    (fun j hj => ⟨by
      obtain ⟨jn, rfl⟩ : ∃ jn : ℕ, j = jn := ⟨j.toNat, by omega⟩
      exact hvan i jn (by push_cast at hj; omega),
      mode_eq_zero_of_le hl₃ hu hw₃ (by push_cast at hj ⊢; omega)⟩)),
    Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · -- the functional terms
    rw [sum_range_trim (J := N₄ + 1) (by omega) (fun i hi => Finset.sum_eq_zero fun j _ => by
      rw [hvan i j (by omega), map_zero, map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [sum_range_trim (J := N₄ + 1) (by omega) (fun j hj => by
      rw [hvan i j (by omega), map_zero, map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    split_ifs with hij
    · rw [map_smul, smul_eq_mul, QI, coeff_X_pow_mul_iterQ (hUB.base hw₁ hw₂ (by omega)),
        LinearMap.comp_apply]
      obtain ⟨r, rfl⟩ : ∃ r, N₄ = d + i + j + r := ⟨N₄ - (d + i + j), by omega⟩
      have e : d + i + j + r - (d + i + j) = r := by omega
      rw [e]
      refine congrArg _ (congrArg _ (congrArg _ (iterV_congr ?_ ?_)))
      · rw [← hP]; push_cast; ring
      · rw [← hQ]; push_cast; ring
    · rw [hvan i j (by omega), map_zero, map_zero, mul_zero, map_zero]
  · -- the `u_j w₃` terms: a binomial series in `x` with pole at `x = −1`
    rw [Finset.sum_comm, sum_range_trim (J := N₃ + d) (by omega) (fun j hj =>
      Finset.sum_eq_zero fun i _ => by
        rw [mode_eq_zero_of_le hl₃ hu hw₃ (by omega), map_zero, map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    rw [QI, coeff_X_mul_binom_mul_iterQ (hUB.base hw₁ hw₂ (by omega)) (-1) j n (j + I₁)
      (by omega), Finset.sum_range_add _ j I₁]
    rw [Finset.sum_eq_zero (s := Finset.range j) (fun t ht => by
      simp only [Finset.mem_range] at ht
      rw [Nat.choose_eq_zero_of_lt ht, Nat.cast_zero, zero_mul, zero_mul]), zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_sub_cancel_left, add_comm j i]
    obtain ⟨r, hr⟩ : ∃ r, N₃ + d = j + 1 + r := ⟨N₃ + d - (j + 1), by omega⟩
    have e : N₃ + d - (j + 1) = r := by omega
    rw [e]
    have hr' : (N₃ : ℂ) + d = j + 1 + r := by exact_mod_cast hr
    refine congrArg _ (iterQ_congr ?_ ?_)
    · rw [← hP]; push_cast; ring
    · rw [← hQ]; push_cast; linear_combination hr'
  · -- the `u_i w₂` terms
    rw [sum_range_trim (J := N₂ + d) (by omega) (fun i hi => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega), map_zero, map_zero, LinearMap.zero_apply,
        map_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [QI, coeff_iterQ]
    obtain ⟨r, hr⟩ : ∃ r, N₂ + d = i + 1 + r := ⟨N₂ + d - (i + 1), by omega⟩
    have e : N₂ + d - (i + 1) = r := by omega
    rw [e]
    have hr' : (N₂ : ℂ) + d = i + 1 + r := by exact_mod_cast hr
    refine iterQ_congr ?_ ?_
    · rw [← hP]
    · rw [← hQ]; push_cast; linear_combination hr'

/-- **Iterate move on the functional** `g ∘ u₍ₘ₎`, `m ≥ 2 wt u − 1` (Huang's `𝒟` for `ψ`):
polynomial coefficients only. -/
theorem moveID (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃)
    (hUB : UnifBase A₁ A₂ Y₄ h₁ h₂ ν) {d m : ℕ} (hm : 2 * d ≤ m + 1) {u : 𝒱}
    (hu : u ∈ W.grading (d : ℤ)) (g : M₄ →ₗ[ℂ] ℂ) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂}
    {w₃ : M₃} (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) :
    QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν (g ∘ₗ mode (A₄.YM u) (m : ℤ)) w₁ w₂ w₃
        (N₄ + (m + 1 - d)) (N₁ + N₂ + N₃ + N₄ + (m + 1 - d))
      = (if m + 1 - d ≤ N₃ then X ^ (2 * (m + 1 - d)) *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν g w₁ w₂ (mode (A₃.YM u) (m : ℤ) w₃) N₄
            (N₁ + N₂ + (N₃ - (m + 1 - d)) + N₄) else 0)
        + ∑ k ∈ Finset.range (N₂ + d), ((m.choose k : ℂ)) • (X ^ (m + 2 + k - 2 * d) *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν g w₁ (mode (A₂.YM u) (k : ℤ) w₂) w₃ N₄
            (N₁ + (N₂ + d - (k + 1)) + N₃ + N₄))
        + ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (N₁ + d),
          ((m.choose k : ℂ) * (k.choose j : ℂ)) • (X ^ (m + 2 + k - 2 * d) *
          QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν g (mode (A₁.YM u) (j : ℤ) w₁) w₂ w₃ N₄
            (N₁ + d - (j + 1) + N₂ + N₃ + N₄)) := by
  ext n
  simp only [map_add, map_sum]
  rw [QI, coeff_iterQ, LinearMap.comp_apply]
  generalize hP : h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * ((N₄ + (m + 1 - d) : ℕ) : ℂ) + n = P
  generalize hQ : ν + ((N₁ + N₂ + N₃ + N₄ + (m + 1 - d) : ℕ) : ℂ) - n = Q
  obtain ⟨T, hT⟩ := A₅.truncation u (Y₄ Q w₁ w₂)
  have hT' := Int.self_le_toNat T
  have h1 := comm_range hY₃ u (Y₄ Q w₁ w₂) w₃ (m : ℤ) P (T.toNat + m + N₂ + d + 1)
    (fun k hk => hT k (by push_cast at hk; omega))
  have h1' : mode (A₄.YM u) (m : ℤ) (Y₃ P (Y₄ Q w₁ w₂) w₃)
      = Y₃ P (Y₄ Q w₁ w₂) (mode (A₃.YM u) (m : ℤ) w₃)
        + ∑ k ∈ Finset.range (T.toNat + m + N₂ + d + 1), cbz (m : ℤ) (k : ℤ) •
            Y₃ ((m : ℂ) + P - k) (mode (A₅.YM u) (k : ℤ) (Y₄ Q w₁ w₂)) w₃ := by
    rw [h1]; push_cast; abel
  rw [h1', map_add, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hsplit : ∀ k ∈ Finset.range (T.toNat + m + N₂ + d + 1),
      cbz (m : ℤ) (k : ℤ) * g (Y₃ ((m : ℂ) + P - k) (mode (A₅.YM u) (k : ℤ) (Y₄ Q w₁ w₂)) w₃)
      = (m.choose k : ℂ) * g (Y₃ ((m : ℂ) + P - k) (Y₄ Q w₁ (mode (A₂.YM u) (k : ℤ) w₂)) w₃)
        + ∑ j ∈ Finset.range (N₁ + d), (m.choose k : ℂ) * (k.choose j : ℂ) *
          g (Y₃ ((m : ℂ) + P - k) (Y₄ ((k : ℤ) + Q - j) (mode (A₁.YM u) (j : ℤ) w₁) w₂) w₃) := by
    intro k _
    have hc := comm_range hY₄ u w₁ w₂ (k : ℤ) Q (N₁ + d)
      (fun j hj => mode_eq_zero_of_le hl₁ hu hw₁ (by push_cast at hj ⊢; omega))
    rw [eq_sub_iff_add_eq] at hc
    rw [← hc, cbz_nat]
    simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.coeFn_sum,
      Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, cbz_nat]
    rw [mul_add, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  obtain ⟨e₀, he₀⟩ : ∃ e₀, m + 1 = d + e₀ := ⟨m + 1 - d, by omega⟩
  have hme : m + 1 - d = e₀ := by omega
  have he₀' : (m : ℂ) + 1 = d + e₀ := by exact_mod_cast he₀
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, m + 2 = 2 * d + t₀ := ⟨m + 2 - 2 * d, by omega⟩
  have ht₀' : (m : ℂ) + 2 = 2 * d + t₀ := by exact_mod_cast ht₀
  simp only [hme] at hP hQ ⊢
  refine Eq.trans ?_ (add_assoc _ _ _).symm
  refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ ?_)
  · split_ifs with h3
    · rw [QI, coeff_X_pow_mul_iterQ (hUB.base hw₁ hw₂ (by omega))]
      obtain ⟨r, rfl⟩ : ∃ r, N₃ = e₀ + r := ⟨N₃ - e₀, by omega⟩
      have e : e₀ + r - e₀ = r := by omega
      rw [e]
      refine iterQ_congr ?_ ?_
      · rw [← hP]; push_cast; ring
      · rw [← hQ]; push_cast; ring
    · rw [map_zero, mode_eq_zero_of_le hl₃ hu hw₃ (by push_cast; omega), map_zero, map_zero]
  · rw [sum_range_trim (J := N₂ + d) (by omega) (fun k hk => by
      rw [mode_eq_zero_of_le hl₂ hu hw₂ (by omega), map_zero, map_zero, LinearMap.zero_apply,
        map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [QI, coeff_X_pow_mul_iterQ
      (hUB.base hw₁ (mode_mem_weight_nat hu hw₂ hk) (by omega))]
    obtain ⟨r, hr⟩ : ∃ r, N₂ + d = k + 1 + r := ⟨N₂ + d - (k + 1), by omega⟩
    have e : N₂ + d - (k + 1) = r := by omega
    have e' : m + 2 + k - 2 * d = t₀ + k := by omega
    rw [e, e']
    have hr' : (N₂ : ℂ) + d = k + 1 + r := by exact_mod_cast hr
    refine congrArg _ (iterQ_congr ?_ ?_)
    · rw [← hP]; push_cast; linear_combination -ht₀' + 2 * he₀'
    · rw [← hQ]; push_cast; linear_combination hr' + ht₀' - he₀'
  · rw [sum_range_trim (J := m + 1) (by omega) (fun k hk => Finset.sum_eq_zero fun j _ => by
      rw [Nat.choose_eq_zero_of_lt (by omega : m < k), Nat.cast_zero, zero_mul, zero_mul])]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    rw [QI, coeff_X_pow_mul_iterQ
      (hUB.base (mode_mem_weight_nat hu hw₁ hj) hw₂ (by omega))]
    obtain ⟨r, hr⟩ : ∃ r, N₁ + d = j + 1 + r := ⟨N₁ + d - (j + 1), by omega⟩
    have e : N₁ + d - (j + 1) = r := by omega
    have e' : m + 2 + k - 2 * d = t₀ + k := by omega
    rw [e, e']
    have hr' : (N₁ : ℂ) + d = j + 1 + r := by exact_mod_cast hr
    refine congrArg _ (iterQ_congr ?_ ?_)
    · rw [← hP]; push_cast; linear_combination -ht₀' + 2 * he₀'
    · rw [← hQ]; push_cast; linear_combination hr' + ht₀' - he₀'

end Moves

/-! ## Linearity of the normalized series -/

section Linear

variable (c ν : ℂ) (N₄ s : ℕ)

theorem QI_add_f (f f' : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν (f + f') w₁ w₂ w₃ N₄ s = QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s
      + QI Y₃ Y₄ c ν f' w₁ w₂ w₃ N₄ s := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_smul_f (a : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν (a • f) w₁ w₂ w₃ N₄ s = a • QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_zero_f (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν (0 : M₄ →ₗ[ℂ] ℂ) w₁ w₂ w₃ N₄ s = 0 := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_add_w₁ (f : M₄ →ₗ[ℂ] ℂ) (w₁ w₁' : M₁) (w₂ : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν f (w₁ + w₁') w₂ w₃ N₄ s = QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s
      + QI Y₃ Y₄ c ν f w₁' w₂ w₃ N₄ s := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_smul_w₁ (a : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν f (a • w₁) w₂ w₃ N₄ s = a • QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_zero_w₁ (f : M₄ →ₗ[ℂ] ℂ) (w₂ : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν f (0 : M₁) w₂ w₃ N₄ s = 0 := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_add_w₂ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ w₂' : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν f w₁ (w₂ + w₂') w₃ N₄ s = QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s
      + QI Y₃ Y₄ c ν f w₁ w₂' w₃ N₄ s := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_smul_w₂ (a : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν f w₁ (a • w₂) w₃ N₄ s = a • QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_zero_w₂ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₃ : M₃) :
    QI Y₃ Y₄ c ν f w₁ (0 : M₂) w₃ N₄ s = 0 := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_add_w₃ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ w₃' : M₃) :
    QI Y₃ Y₄ c ν f w₁ w₂ (w₃ + w₃') N₄ s = QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s
      + QI Y₃ Y₄ c ν f w₁ w₂ w₃' N₄ s := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_smul_w₃ (a : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) :
    QI Y₃ Y₄ c ν f w₁ w₂ (a • w₃) N₄ s = a • QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s := by
  ext n; simp [QI, coeff_iterQ]

theorem QI_zero_w₃ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) :
    QI Y₃ Y₄ c ν f w₁ w₂ (0 : M₃) N₄ s = 0 := by
  ext n; simp [QI, coeff_iterQ]

end Linear

/-- `QI` only sees the functional on the weight space `h₄ + N₄`. -/
theorem QI_congr_f {h₁ h₂ h₃ h₄ ν : ℂ} (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) {N₁ N₂ N₃ N₄ : ℕ} {w₁ : M₁} {w₂ : M₂}
    {w₃ : M₃} (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) {f f' : M₄ →ₗ[ℂ] ℂ}
    (hff : f.domRestrict (A₄.weight (h₄ + N₄)) = f'.domRestrict (A₄.weight (h₄ + N₄))) :
    QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
      = QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f' w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) := by
  ext n
  rw [QI, QI, coeff_iterQ, coeff_iterQ]
  have hx := iter_mem_weight hY₃ hY₄ hw₁ hw₂ hw₃
    (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n) (ν + ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) - n)
  have e : h₁ + N₁ + (h₂ + N₂) + (h₃ + N₃) - (h₁ + h₂ + h₃ - h₄ - 2 - ν - 2 * N₄ + n)
      - (ν + ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) - n) - 2 = h₄ + N₄ := by push_cast; ring
  rw [e] at hx
  exact LinearMap.congr_fun hff ⟨_, hx⟩

/-! ## Finite generation of the base module -/

section Finite

variable (c ν : ℂ) (N₄ s : ℕ)

/-- `QI` as a linear map in the functional. -/
noncomputable def QIf (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) : (M₄ →ₗ[ℂ] ℂ) →ₗ[ℂ] PowerSeries ℂ where
  toFun f := QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s
  map_add' f f' := QI_add_f c ν N₄ s f f' w₁ w₂ w₃
  map_smul' a f := QI_smul_f c ν N₄ s a f w₁ w₂ w₃

/-- `QI` as a linear map in `w₁`. -/
noncomputable def QI₁ (f : M₄ →ₗ[ℂ] ℂ) (w₂ : M₂) (w₃ : M₃) : M₁ →ₗ[ℂ] PowerSeries ℂ where
  toFun w₁ := QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s
  map_add' x y := QI_add_w₁ c ν N₄ s f x y w₂ w₃
  map_smul' a x := QI_smul_w₁ c ν N₄ s a f x w₂ w₃

/-- `QI` as a linear map in `w₂`. -/
noncomputable def QI₂ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₃ : M₃) : M₂ →ₗ[ℂ] PowerSeries ℂ where
  toFun w₂ := QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s
  map_add' x y := QI_add_w₂ c ν N₄ s f w₁ x y w₃
  map_smul' a x := QI_smul_w₂ c ν N₄ s a f w₁ x w₃

/-- `QI` as a linear map in `w₃`. -/
noncomputable def QI₃ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) : M₃ →ₗ[ℂ] PowerSeries ℂ where
  toFun w₃ := QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s
  map_add' x y := QI_add_w₃ c ν N₄ s f w₁ w₂ x y
  map_smul' a x := QI_smul_w₃ c ν N₄ s a f w₁ w₂ x

end Finite

/-- **Finitely many tuples suffice at fixed levels**: all `QI` of a fixed level vector lie in the
`ℂ`-span of a finite set (bases of the four finite-dimensional weight spaces). -/
theorem exists_finite_span_iter {h₁ h₂ h₃ h₄ ν : ℂ} (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) (N₁ N₂ N₃ N₄ : ℕ) :
    ∃ T : Set (PowerSeries ℂ), T.Finite ∧ ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃),
      w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
      QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
        ∈ Submodule.span ℂ T := by
  classical
  haveI := A₁.finrank (h₁ + N₁)
  haveI := A₂.finrank (h₂ + N₂)
  haveI := A₃.finrank (h₃ + N₃)
  haveI := A₄.finrank (h₄ + N₄)
  set E₄ := A₄.weight (h₄ + N₄)
  obtain ⟨E', hE'⟩ := Submodule.exists_isCompl E₄
  set π := Submodule.projectionOnto E₄ E' hE'
  set b₁ := Module.finBasis ℂ (A₁.weight (h₁ + N₁))
  set b₂ := Module.finBasis ℂ (A₂.weight (h₂ + N₂))
  set b₃ := Module.finBasis ℂ (A₃.weight (h₃ + N₃))
  set b₄ := Module.finBasis ℂ (Module.Dual ℂ E₄)
  set c := h₁ + h₂ + h₃ - h₄ - 2
  set s := N₁ + N₂ + N₃ + N₄
  refine ⟨Set.range fun q : _ × _ × _ × _ =>
    QI Y₃ Y₄ c ν ((b₄ q.1).comp π) (b₁ q.2.1 : M₁) (b₂ q.2.2.1 : M₂) (b₃ q.2.2.2 : M₃) N₄ s,
    Set.finite_range _, ?_⟩
  intro f w₁ w₂ w₃ hw₁ hw₂ hw₃
  -- the functional only matters on `E₄`
  have hres : f.domRestrict E₄ = ((f.domRestrict E₄).comp π).domRestrict E₄ := by
    ext x
    simp [π, Submodule.projectionOnto_apply_left]
  rw [QI_congr_f hY₃ hY₄ hw₁ hw₂ hw₃ hres]
  have hψ := b₄.sum_repr (f.domRestrict E₄)
  have hcomp : (f.domRestrict E₄).comp π
      = ∑ a, b₄.repr (f.domRestrict E₄) a • (b₄ a).comp π := by
    ext x
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← hψ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change QIf (Y₃ := Y₃) (Y₄ := Y₄) c ν N₄ s w₁ w₂ w₃ ((f.domRestrict E₄).comp π) ∈ _
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  change QI₁ (Y₃ := Y₃) (Y₄ := Y₄) c ν N₄ s ((b₄ a).comp π) w₂ w₃ w₁ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₁ _ fun i => ?_
  change QI₂ (Y₃ := Y₃) (Y₄ := Y₄) c ν N₄ s ((b₄ a).comp π) (b₁ i : M₁) w₃ w₂ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₂ _ fun j => ?_
  change QI₃ (Y₃ := Y₃) (Y₄ := Y₄) c ν N₄ s ((b₄ a).comp π) (b₁ i : M₁) (b₂ j : M₂) w₃ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₃ _ fun k => ?_
  exact Submodule.subset_span ⟨(a, i, j, k), rfl⟩



/-! ## The induction for iterates (Huang's Prop. 2.1 at `z₁ = z₂`, one variable) -/

section Induction

variable {h₁ h₂ h₃ h₄ ν : ℂ} {B₁ B₂ B₃ B₄ : ℕ}

/-- **Huang's Prop. 1.1/2.1 for iterates (regular at `x = z₀/z₂ = 0`).** -/
theorem qi_mem (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hUB : UnifBase A₁ A₂ Y₄ h₁ h₂ ν) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hD₄ : DualC1Graded A₄ h₄ B₄)
    (NN : Submodule (ratRing (-1)) (PowerSeries ℂ))
    (hbase : ∀ (N₁ N₂ N₃ N₄ : ℕ), N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃), w₁ ∈ A₁.weight (h₁ + N₁) →
        w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN) :
    ∀ (s N₁ N₂ N₃ N₄ : ℕ), N₁ + N₂ + N₃ + N₄ = s →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃), w₁ ∈ A₁.weight (h₁ + N₁) →
        w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ s ∈ NN := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
  intro N₁ N₂ N₃ N₄ hs f w₁ w₂ w₃ hw₁ hw₂ hw₃
  have IH' : ∀ (N₁ N₂ N₃ N₄ : ℕ), N₁ + N₂ + N₃ + N₄ < s →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃), w₁ ∈ A₁.weight (h₁ + N₁) →
        w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN :=
    fun N₁ N₂ N₃ N₄ hlt f w₁ w₂ w₃ h1 h2 h3 => IH _ hlt N₁ N₂ N₃ N₄ rfl f w₁ w₂ w₃ h1 h2 h3
  subst hs
  by_cases c1 : B₁ < N₁
  · refine Submodule.span_induction
      (p := fun x _ => QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f x w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hC₁ N₁ c1 w₁ hw₁)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₁ + N₂ + N₃ + N₄ = (N₁ - d) + d + N₂ + N₃ + N₄ by omega,
        moveIA hY₃ hY₄ hl₂ hl₃ hl₄ hUB hu f hw' hw₂ hw₃]
      refine NN.add_mem (NN.add_mem ?_ ?_) ?_
      · refine NN.sum_mem fun i _ => NN.sum_mem fun j _ => ?_
        split_ifs with hij
        · exact smul_mem_of_ratRing NN _ (mul_mem_of_ratRing NN (X_pow_mem _ _)
            (IH' _ _ _ _ (by omega) _ _ _ _ hw' hw₂ hw₃))
        · exact NN.zero_mem
      · refine NN.sum_mem fun j hj => mul_mem_of_ratRing NN (X_mul_binom_mem' _ j) ?_
        simp only [Finset.mem_range] at hj
        exact IH' _ _ _ _ (by omega) _ _ _ _ hw' hw₂ (mode_mem_weight_nat hu hw₃ hj)
      · refine NN.sum_mem fun i hi => ?_
        simp only [Finset.mem_range] at hi
        exact IH' _ _ _ _ (by omega) _ _ _ _ hw' (mode_mem_weight_nat hu hw₂ hi) hw₃
    · simp only []; rw [QI_zero_w₁]; exact NN.zero_mem
    · intro x y _ _ hx hy; rw [QI_add_w₁]; exact NN.add_mem hx hy
    · intro a x _ hx; rw [QI_smul_w₁]; exact smul_mem_of_ratRing NN a hx
  by_cases c2 : B₂ < N₂
  · refine Submodule.span_induction
      (p := fun x _ => QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ x w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hC₂ N₂ c2 w₂ hw₂)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₁ + N₂ + N₃ + N₄ = N₁ + (N₂ - d) + d + N₃ + N₄ by omega,
        moveIB hY₃ hY₄ hl₁ hl₃ hl₄ hUB hu f hw₁ hw' hw₃]
      refine NN.sub_mem (NN.add_mem ?_ ?_) ?_
      · refine NN.sum_mem fun i hi => mul_mem_of_ratRing NN (X_pow_mem _ _) ?_
        simp only [Finset.mem_range] at hi
        exact IH' _ _ _ _ (by omega) _ _ _ _ hw₁ hw' hw₃
      · refine NN.sum_mem fun i hi => mul_mem_of_ratRing NN (X_pow_mem _ _) ?_
        simp only [Finset.mem_range] at hi
        exact IH' _ _ _ _ (by omega) _ _ _ _ hw₁ hw' (mode_mem_weight_nat hu hw₃ hi)
      · refine NN.sum_mem fun k hk => smul_mem_of_ratRing NN _ ?_
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ (by omega) _ _ _ _ (mode_mem_weight_nat hu hw₁ hk) hw' hw₃
    · simp only []; rw [QI_zero_w₂]; exact NN.zero_mem
    · intro x y _ _ hx hy; rw [QI_add_w₂]; exact NN.add_mem hx hy
    · intro a x _ hx; rw [QI_smul_w₂]; exact smul_mem_of_ratRing NN a hx
  by_cases c3 : B₃ < N₃
  · refine Submodule.span_induction
      (p := fun x _ => QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ x N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hC₃ N₃ c3 w₃ hw₃)
    · rintro x ⟨d, u, w', hd1, hdN, hu, hw', rfl⟩
      rw [show N₁ + N₂ + N₃ + N₄ = N₁ + N₂ + (N₃ - d) + d + N₄ by omega,
        moveIC hY₃ hY₄ hl₁ hl₂ hl₄ hUB hu f hw₁ hw₂ hw']
      refine NN.sub_mem (NN.sub_mem ?_ ?_) ?_
      · split_ifs with hd
        · exact mul_mem_of_ratRing NN (X_pow_mem _ _)
            (IH' _ _ _ _ (by omega) _ _ _ _ hw₁ hw₂ hw')
        · exact NN.zero_mem
      · refine NN.sum_mem fun k hk => smul_mem_of_ratRing NN _
          (mul_mem_of_ratRing NN (X_pow_mem _ _) ?_)
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ (by omega) _ _ _ _ hw₁ (mode_mem_weight_nat hu hw₂ hk) hw'
      · refine NN.sum_mem fun j hj => smul_mem_of_ratRing NN _
          (mul_mem_of_ratRing NN (X_mul_binom_mem' _ j) ?_)
        simp only [Finset.mem_range] at hj
        exact IH' _ _ _ _ (by omega) _ _ _ _ (mode_mem_weight_nat hu hw₁ hj) hw₂ hw'
    · simp only []; rw [QI_zero_w₃]; exact NN.zero_mem
    · intro x y _ _ hx hy; rw [QI_add_w₃]; exact NN.add_mem hx hy
    · intro a x _ hx; rw [QI_smul_w₃]; exact smul_mem_of_ratRing NN a hx
  by_cases c4 : B₄ < N₄
  · refine Submodule.span_induction
      (p := fun φ _ => ∀ f' : M₄ →ₗ[ℂ] ℂ, f'.domRestrict (A₄.weight (h₄ + N₄)) = φ →
        QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f' w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN)
      ?_ ?_ ?_ ?_ (hD₄ N₄ c4 f) f rfl
    · rintro φ ⟨d, m, u, g, hd1, hm, hmN, hu, rfl⟩ f' hf'
      rw [QI_congr_f hY₃ hY₄ hw₁ hw₂ hw₃ hf']
      obtain ⟨r, rfl⟩ : ∃ r, N₄ = r + (m + 1 - d) := ⟨N₄ - (m + 1 - d), by omega⟩
      rw [show N₁ + N₂ + N₃ + (r + (m + 1 - d)) = N₁ + N₂ + N₃ + r + (m + 1 - d) by ring,
        moveID hY₃ hY₄ hl₁ hl₂ hl₃ hUB hm hu g hw₁ hw₂ hw₃]
      refine NN.add_mem (NN.add_mem ?_ ?_) ?_
      · split_ifs with h3
        · refine mul_mem_of_ratRing NN (X_pow_mem _ _)
            (IH' _ _ _ _ (by omega) _ _ _ _ hw₁ hw₂ ?_)
          have hm3 := mode_mem_weight A₃ hu hw₃ (m : ℤ)
          have e : h₃ + (N₃ : ℂ) + ((d : ℤ) : ℂ) - ((m : ℤ) : ℂ) - 1
              = h₃ + ((N₃ - (m + 1 - d) : ℕ) : ℂ) := by
            rw [Nat.cast_sub h3, Nat.cast_sub (by omega)]; push_cast; ring
          rw [e] at hm3
          exact hm3
        · exact NN.zero_mem
      · refine NN.sum_mem fun k hk => smul_mem_of_ratRing NN _
          (mul_mem_of_ratRing NN (X_pow_mem _ _) ?_)
        simp only [Finset.mem_range] at hk
        exact IH' _ _ _ _ (by omega) _ _ _ _ hw₁ (mode_mem_weight_nat hu hw₂ hk) hw₃
      · refine NN.sum_mem fun k _ => NN.sum_mem fun j hj => smul_mem_of_ratRing NN _
          (mul_mem_of_ratRing NN (X_pow_mem _ _) ?_)
        simp only [Finset.mem_range] at hj
        exact IH' _ _ _ _ (by omega) _ _ _ _ (mode_mem_weight_nat hu hw₁ hj) hw₂ hw₃
    · intro f' hf'
      rw [QI_congr_f hY₃ hY₄ hw₁ hw₂ hw₃ (f' := 0) (by rw [hf']; ext; simp), QI_zero_f]
      exact NN.zero_mem
    · intro φ₁ φ₂ _ _ h1 h2 f' hf'
      obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend φ₁
      have hsplit : f' = g₁ + (f' - g₁) := by abel
      rw [hsplit, QI_add_f]
      refine NN.add_mem (h1 g₁ hg₁) (h2 _ ?_)
      ext x
      have hx := LinearMap.congr_fun hf' x
      have hx1 := LinearMap.congr_fun hg₁ x
      simp only [LinearMap.domRestrict_apply, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, Submodule.subtype_apply] at hx hx1 ⊢
      rw [hx, hx1]; ring
    · intro a φ _ h1 f' hf'
      obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend φ
      rw [QI_congr_f hY₃ hY₄ hw₁ hw₂ hw₃ (f' := a • g₁) (by
        rw [hf']; ext x
        have hx1 := LinearMap.congr_fun hg₁ x
        simp only [LinearMap.domRestrict_apply, LinearMap.smul_apply, LinearMap.comp_apply,
          Submodule.subtype_apply] at hx1 ⊢
        rw [hx1]), QI_smul_f]
      exact smul_mem_of_ratRing NN a (h1 g₁ hg₁)
  exact hbase N₁ N₂ N₃ N₄ (by omega) (by omega) (by omega) (by omega) f w₁ w₂ w₃ hw₁ hw₂ hw₃

end Induction

/-! ## The Euler operator and the assembly (iterates) -/

/-- `L₋₁` on the inner-left vector is the twisted Euler operator in `x = z₀/z₂`. -/
theorem QI_Lm1 (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) (c ν : ℂ) (f : M₄ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (N₄ s : ℕ) :
    QI Y₃ Y₄ c ν f (A₁.Lm1 w₁) w₂ w₃ N₄ (s + 1)
      = thetaShift (-(ν + s + 1)) (QI Y₃ Y₄ c ν f w₁ w₂ w₃ N₄ s) := by
  ext n
  rw [coeff_thetaShift, QI, QI, coeff_iterQ, coeff_iterQ, hY₄.L_neg_one, LinearMap.smul_apply,
    map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  have e : ν + ((s + 1 : ℕ) : ℂ) - n - 1 = ν + s - n := by push_cast; ring
  rw [e]
  push_cast
  ring

/-- The normalized series of the target tuple is `x^K` times the coset series of the iterate. -/
theorem QI_eq_X_pow_mul_iterSeries {h₁ h₂ h₃ h₄ ν₀ : ℂ} {N₁ N₂ N₃ N₄ K : ℕ}
    {f : M₄ →ₗ[ℂ] ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} (hb : IsBase Y₄ w₁ w₂ ν₀) :
    QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) (ν₀ - ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) + K) f w₁ w₂ w₃ N₄
        (N₁ + N₂ + N₃ + N₄)
      = X ^ K * iterSeries Y₃ Y₄ f w₁ w₂ w₃
          ((h₁ + N₁) + (h₂ + N₂) + (h₃ + N₃) - (h₄ + N₄) - 2) ν₀ := by
  ext n
  rw [coeff_X_pow_mul', QI, coeff_iterQ]
  split_ifs with h
  · rw [coeff_iterSeries, iterCoeff]
    apply iterQ_congr
    · rw [Nat.cast_sub h]; push_cast; ring
    · rw [Nat.cast_sub h]; push_cast; ring
  · have e : ν₀ - ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) + K + ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) - n
        = ν₀ + (((K - n - 1 : ℕ) : ℂ) + 1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e, hb, map_zero, LinearMap.zero_apply, map_zero]

/-- **Huang's regular equation for iterates (one-variable form), from graded
`C₁`-cofiniteness**: the coset series of `⟨f, 𝒴₃(𝒴₄(w₁, z₀)w₂, z₂)w₃⟩` in `x = z₀/z₂` satisfies a
monic `θ_λ`-equation with coefficients in `ℂ[x, (1 + x)⁻¹]` (Huang's Thm 2.3 at
`z₂⁻¹(z₁ − z₂) = 0`, after the degree-0 reduction). -/
theorem ratFuchsian_iterSeries_of_C1 {h₁ h₂ h₃ h₄ : ℂ} {B₁ B₂ B₃ B₄ : ℕ}
    (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃) (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄)
    (hl₁ : IsLowestWeight A₁ h₁) (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃)
    (hl₄ : IsLowestWeight A₄ h₄) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hD₄ : DualC1Graded A₄ h₄ B₄)
    {α₁ α₂ α₃ h₄' : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} (f : M₄ →ₗ[ℂ] ℂ)
    (hw₁ : w₁ ∈ A₁.weight α₁) (hw₂ : w₂ ∈ A₂.weight α₂) (hw₃ : w₃ ∈ A₃.weight α₃)
    {ν₀ : ℂ} (hb : IsBase Y₄ w₁ w₂ ν₀) (lam : ℂ) :
    RatFuchsian (-1) lam (iterSeries Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄' - 2) ν₀) := by
  classical
  by_cases z₁ : A₁.weight α₁ = ⊥
  · have : w₁ = 0 := by rw [z₁] at hw₁; exact (Submodule.mem_bot ℂ).mp hw₁
    subst this
    convert ratFuchsian_zero (-1) lam using 1
    ext k; simp [coeff_iterSeries, iterCoeff]
  by_cases z₂ : A₂.weight α₂ = ⊥
  · have : w₂ = 0 := by rw [z₂] at hw₂; exact (Submodule.mem_bot ℂ).mp hw₂
    subst this
    convert ratFuchsian_zero (-1) lam using 1
    ext k; simp [coeff_iterSeries, iterCoeff]
  by_cases z₃ : A₃.weight α₃ = ⊥
  · have : w₃ = 0 := by rw [z₃] at hw₃; exact (Submodule.mem_bot ℂ).mp hw₃
    subst this
    convert ratFuchsian_zero (-1) lam using 1
    ext k; simp [coeff_iterSeries, iterCoeff]
  by_cases z₄ : A₄.weight h₄' = ⊥
  · convert ratFuchsian_zero (-1) lam using 1
    ext k
    rw [coeff_iterSeries, iterCoeff, map_zero]
    have hx := iter_mem_weight hY₃ hY₄ hw₁ hw₂ hw₃
      (α₁ + α₂ + α₃ - h₄' - 2 - ν₀ + k) (ν₀ - k)
    have e : α₁ + α₂ + α₃ - (α₁ + α₂ + α₃ - h₄' - 2 - ν₀ + k) - (ν₀ - k) - 2 = h₄' := by ring
    rw [e, z₄] at hx
    rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
  obtain ⟨N₁, rfl⟩ := hl₁ α₁ z₁
  obtain ⟨N₂, rfl⟩ := hl₂ α₂ z₂
  obtain ⟨N₃, rfl⟩ := hl₃ α₃ z₃
  obtain ⟨N₄, rfl⟩ := hl₄ h₄' z₄
  obtain ⟨K, hUB⟩ := exists_unifBase hY₄ h₁ h₂ ν₀ (N₁ + N₂ + N₃ + N₄)
  set ν := ν₀ - ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) + K with hν
  choose T hTfin hT using fun q : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) =>
    exists_finite_span_iter (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄) (ν := ν) hY₃ hY₄
      q.1 q.2.1 q.2.2.1 q.2.2.2
  set NN : Submodule (ratRing (-1)) (PowerSeries ℂ) :=
    Submodule.span (ratRing (-1)) (⋃ q, T q)
  have hFG : NN.FG := Submodule.fg_span (Set.finite_iUnion hTfin)
  have hbase : ∀ (N₁ N₂ N₃ N₄ : ℕ), N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃), w₁ ∈ A₁.weight (h₁ + N₁) →
        w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
        QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ NN := by
    intro N₁ N₂ N₃ N₄ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃
    have hq := hT (⟨N₁, by omega⟩, ⟨N₂, by omega⟩, ⟨N₃, by omega⟩, ⟨N₄, by omega⟩) f w₁ w₂ w₃
      hw₁ hw₂ hw₃
    have hle : Submodule.span ℂ (T (⟨N₁, by omega⟩, ⟨N₂, by omega⟩, ⟨N₃, by omega⟩,
        ⟨N₄, by omega⟩)) ≤ NN.restrictScalars ℂ :=
      (Submodule.span_mono (Set.subset_iUnion T _)).trans
        (Submodule.span_le_restrictScalars ℂ (ratRing (-1)) _)
    exact hle hq
  have hall := qi_mem hY₃ hY₄ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄ NN hbase
  set Q : ℕ → PowerSeries ℂ := fun j =>
    QI Y₃ Y₄ (h₁ + h₂ + h₃ - h₄ - 2) ν f ((⇑A₁.Lm1)^[j] w₁) w₂ w₃ N₄
      (N₁ + N₂ + N₃ + N₄ + j) with hQdef
  have hQmem : ∀ j, Q j ∈ NN := fun j =>
    hall _ (N₁ + j) N₂ N₃ N₄ (by omega) f _ w₂ w₃ (Lm1_iterate_mem_weight hw₁ j) hw₂ hw₃
  have hQ : ∀ j, Q (j + 1) = thetaShift (-(ν + ((N₁ + N₂ + N₃ + N₄ + j : ℕ) : ℂ) + 1)) (Q j) := by
    intro j
    simp only [hQdef]
    rw [Function.iterate_succ_apply', show N₁ + N₂ + N₃ + N₄ + (j + 1)
      = N₁ + N₂ + N₃ + N₄ + j + 1 from rfl, QI_Lm1 hY₄]
  have hθ := theta_iter_mem NN Q _ hQ hQmem 0
  have hQ0 : Q 0 = X ^ K * iterSeries Y₃ Y₄ f w₁ w₂ w₃
      ((h₁ + N₁) + (h₂ + N₂) + (h₃ + N₃) - (h₄ + N₄) - 2) ν₀ := by
    simp only [hQdef, Function.iterate_zero, id, add_zero]
    exact QI_eq_X_pow_mul_iterSeries hb
  exact ratFuchsian_of_fg NN hFG (K := K) (μ := 0) (fun j => by
    have := hθ j 0; rwa [hQ0] at this) lam

end Iterate

/-! ## The named input `HuangIterateODE` and `HuangODEInput` -/

/-- **`HuangIterateODE` from the graded `C₁`-data.** -/
theorem huangIterateODE_of_moduleC1Data (hC : ModuleC1Data W) : HuangIterateODE W := by
  intro P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ M₅ _ _ A₅ Y₃ Y₄ hY₃ hY₄ α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ _ ν₀ hb
  obtain ⟨⟨B₁, c₁⟩, -⟩ := hC P₁ i₁
  obtain ⟨⟨B₂, c₂⟩, -⟩ := hC P₂ i₂
  obtain ⟨⟨B₃, c₃⟩, -⟩ := hC P₃ i₃
  obtain ⟨-, ⟨B₄, d₄⟩⟩ := hC P₄ i₄
  exact ratFuchsian_iterSeries_of_C1 hY₃ hY₄ P₁.isLow P₂.isLow P₃.isLow P₄.isLow c₁ c₂ c₃ d₄ f
    h₁ h₂ h₃ hb _

/-- **The graded `C₁`-input** (TRUE: Abe–Buhl–Dong + FHL; see `ModuleC1Data`). -/
def ModuleC1Input : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱),
    StronglyRational W → ModuleC1Data W

/-- **`HuangODEInput` reduces to the graded `C₁`-input.** -/
theorem huangODEInput_of_moduleC1Input (h : ModuleC1Input.{u}) : HuangODEInput.{u} :=
  fun 𝒱 _ _ W hV => ⟨huangProductODE_of_moduleC1Data (h 𝒱 W hV),
    huangIterateODE_of_moduleC1Data (h 𝒱 W hV)⟩

end VOA.Huang.HuangODEIterate
