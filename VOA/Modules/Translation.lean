/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.WeakModule
import VOA.Core.WeakAssoc
import VOA.Core.Identities

/-!
# Module translation covariance  (Gannon §5.3.1, eq. 5.1.8a for modules)

The module mirror of the `𝒱`-level derivative property `Y(L₋₁a, z) = ∂_z Y(a,z)`
(`Core.Identities.mode_Y_T`): for a weak `𝒱`-module `(M, Y_M)`,

  `(L₋₁a)₍n₎ᴹ x = −n · a₍n−1₎ᴹ x`   (`act_T_covariance`).

Unlike the `𝒱`-level statement (which is the VOA axiom VOA3), the module version is *derived*
from the module Jacobi identity (`WeakModule.jacobi`). The route is:

* **`module_iterate0`** — the `m = 0` slice of the module Jacobi, i.e. the module *iterate
  formula* `(u₍ℓ₎v)₍n₎ᴹ = ∑ᵢ (-1)ⁱC(ℓ,i)(u₍ℓ₋ᵢ₎ᴹ v₍n+i₎ᴹ − (-1)^ℓ v₍ℓ+n−i₎ᴹ u₍i₎ᴹ)` (`C(0,i) = δ`
  collapses the right-hand `∑ᶠ`);
* with `L₋₁a = a₍₋₂₎𝟙` (`creation_pow`) we set `u = a`, `v = 𝟙`, `ℓ = −2`; the **vacuum**
  `𝟙₍k₎ᴹ x = δ_{k,−1} x` collapses the iterate `∑ᶠ` to the two terms `i = −1−n` and `i = n−1`;
* their coefficients `C(−2,·)` and signs combine to exactly `−n` (`cov_scalar`, off
  `gBinom_neg_two : C(−2,j) = (−1)ʲ(j+1)`).

This is the engine for the **zero-mode descent 5.3.9b** (`Modules.ZhuAlgebra.oMod_L_translation`,
`o(L₋₁u+L₀u)=0`) and for the contragredient module action.

## Status
`sorry`-free, with no project axioms. `gBinom_neg_two`, `cov_scalar`,
`module_iterate0`, and **`act_T_covariance`** are all
`[propext, Classical.choice, Quot.sound]`.

## References
* Gannon §5.3.1, eq. (5.1.8a); Frenkel–Huang–Lepowsky [199]; Lepowsky–Li Ch. 4.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical
open VertexOperatorAlgebra

universe u v
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Binomial/sign scalar core -/

/-- `C(-2, j) = (-1)ʲ (j+1)` (the descending product `(-2)(-3)⋯(-2-j+1)/j!`). -/
theorem gBinom_neg_two (j : ℕ) : gBinom (-2 : ℤ) j = (-1 : ℂ) ^ j * (1 + j) := by
  have h := gBinom_negsucc 1 j
  rw [show (-((1 : ℕ) : ℤ) - 1) = -2 from by norm_num, Nat.factorial_one] at h
  have hj : ((1 + j).factorial : ℂ) = (1 + (j : ℂ)) * (j.factorial : ℂ) := by
    rw [show 1 + j = j + 1 from by ring, Nat.factorial_succ]; push_cast; ring
  have hjne : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [h, hj]; field_simp; ring

/-- The scalar core of the module translation covariance: for all `n`,
`(-1)^{-1-n}·C(-2,-1-n) − (-1)^{n-1}·C(-2,n-1)·(-1)^{-2} = -n`. -/
theorem cov_scalar (n : ℤ) :
    negOnePow (-1 - n) * cbz (-2) (-1 - n)
      - negOnePow (n - 1) * cbz (-2) (n - 1) * negOnePow (-2) = (-(n : ℂ)) := by
  have hsign : ∀ m : ℤ, (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := fun m => by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), show m + m = 2 * m from by ring, zpow_mul,
      show ((-1 : ℂ) ^ (2 : ℤ)) = 1 from by norm_num, one_zpow]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hto : ((-1 - n).toNat : ℤ) = -1 - n := Int.toNat_of_nonneg (by omega)
    have htoC : ((-1 - n).toNat : ℂ) = -1 - (n : ℂ) := by exact_mod_cast hto
    rw [cbz_apply_neg (-2) (by omega : (n - 1 : ℤ) < 0), mul_zero, zero_mul, sub_zero,
      cbz_apply_nonneg (-2) (by omega : (0 : ℤ) ≤ -1 - n), gBinom_neg_two,
      negOnePow_eq_zpow, ← zpow_natCast (-1 : ℂ) (-1 - n).toNat, hto, ← mul_assoc,
      hsign, one_mul, htoC]
    ring
  · subst hn
    rw [cbz_apply_neg (-2) (by norm_num : (-1 - 0 : ℤ) < 0),
      cbz_apply_neg (-2) (by norm_num : ((0 : ℤ) - 1) < 0)]
    simp
  · have hto : ((n - 1).toNat : ℤ) = n - 1 := Int.toNat_of_nonneg (by omega)
    have htoC : ((n - 1).toNat : ℂ) = (n : ℂ) - 1 := by exact_mod_cast hto
    rw [cbz_apply_neg (-2) (by omega : (-1 - n : ℤ) < 0), mul_zero, zero_sub,
      cbz_apply_nonneg (-2) (by omega : (0 : ℤ) ≤ n - 1), gBinom_neg_two,
      show negOnePow (-2 : ℤ) = 1 from by rw [negOnePow_eq_zpow]; norm_num, mul_one,
      negOnePow_eq_zpow, ← zpow_natCast (-1 : ℂ) (n - 1).toNat, hto, ← mul_assoc,
      hsign, one_mul, htoC]
    ring

/-! ## The module iterate formula and translation covariance -/

variable {M : Type v} [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra 𝒱}

/-- The **`m = 0` slice of the module Jacobi** (module iterate formula):
`(u₍ℓ₎v)₍n₎ᴹ x = ∑ᵢ (-1)ⁱC(ℓ,i)(u₍ℓ₋ᵢ₎ᴹ v₍n+i₎ᴹ x − (-1)^ℓ v₍ℓ+n−i₎ᴹ u₍i₎ᴹ x)`.
The right-hand `∑ᶠ` of the Jacobi identity collapses since `C(0,i) = δ_{i,0}`. -/
theorem module_iterate0 (A : WeakModule W M) (u v : 𝒱) (x : M) (ℓ n : ℤ) :
    mode (A.YM (W.smul u ℓ v)) n x
      = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (mode (A.YM u) (ℓ - i) (mode (A.YM v) (n + i) x)
            - negOnePow ℓ • mode (A.YM v) (ℓ + n - i) (mode (A.YM u) i x)) := by
  have hjac := A.jacobi u v x ℓ 0 n
  have hrhs : (∑ᶠ i : ℤ, cbz 0 i • mode (A.YM (W.smul u (ℓ + i) v)) (0 + n - i) x)
      = mode (A.YM (W.smul u ℓ v)) n x := by
    rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
    simp
  rw [hrhs] at hjac
  rw [← hjac]
  simp only [add_zero, zero_add]

/-- **Module translation covariance** (Gannon 5.1.8a for modules): for a weak `𝒱`-module,
`(L₋₁a)₍n₎ᴹ x = −n · a₍n−1₎ᴹ x`. Off `module_iterate0` with `v = 𝟙`, `ℓ = −2`
(`L₋₁a = a₍₋₂₎𝟙`); the vacuum collapses the finsum to `i = −1−n` and `i = n−1`, whose
`C(−2,·)`/sign coefficients combine to `−n` (`cov_scalar`). -/
theorem act_T_covariance (A : WeakModule W M) (a : 𝒱) (n : ℤ) (x : M) :
    A.act (W.L (-1) a) n x = (-(n : ℂ)) • A.act a (n - 1) x := by
  have hL : W.L (-1) a = W.smul a (-2) W.vacuum := by
    have hc := creation_pow W a 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] at hc
    rw [T_eq_Lneg1, show (-(1 : ℤ) - 1) = -2 from by norm_num] at hc
    exact hc.symm
  have hvac : ∀ (k : ℤ) (y : M), mode (A.YM W.vacuum) k y = if k = -1 then y else 0 := by
    intro k y; rw [← WeakModule.act_def]; exact A.act_vacuum k y
  simp only [WeakModule.act_def]
  rw [hL, module_iterate0 A a W.vacuum x (-2) n]
  simp only [hvac, smul_sub]
  rw [finsum_sub_distrib ?_ ?_, finsum_eq_single _ (-1 - n) ?_, finsum_eq_single _ (n - 1) ?_]
  · rw [show (n + (-1 - n) : ℤ) = -1 from by ring, if_pos rfl,
      show (-2 - (-1 - n) : ℤ) = n - 1 from by ring,
      show (-2 + n - (n - 1) : ℤ) = -1 from by ring, if_pos rfl, smul_smul, ← sub_smul,
      cov_scalar]
  · intro i hi
    rw [if_neg (show ¬(-2 + n - i = -1) by omega), smul_zero, smul_zero]
  · intro i hi
    rw [if_neg (show ¬(n + i = -1) by omega), map_zero, smul_zero]
  · apply Set.Finite.subset (Set.finite_singleton (-1 - n))
    intro i hi
    simp only [Function.mem_support, Set.mem_singleton_iff] at hi ⊢
    by_contra hne
    exact hi (by rw [if_neg (show ¬(n + i = -1) by omega), map_zero, smul_zero])
  · apply Set.Finite.subset (Set.finite_singleton (n - 1))
    intro i hi
    simp only [Function.mem_support, Set.mem_singleton_iff] at hi ⊢
    by_contra hne
    exact hi (by rw [if_neg (show ¬(-2 + n - i = -1) by omega), smul_zero, smul_zero])

end VOA
