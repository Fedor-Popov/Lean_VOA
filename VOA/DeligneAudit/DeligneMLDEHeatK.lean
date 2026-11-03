/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.JacobiTriple
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The heat equation for the Jacobi triple product over `K⟦x⟧` (any field of characteristic zero)

Let `A = ℚ⟦x⟧` and `u = ε·eˣ ∈ (PowerSeries K)ˣ` (`ε = ±1`).  In `A⟦q⟧` the Jacobi triple product
(`VOA.QSeries.JTP.jacobiTriple`) reads `Θ = (1 - u)·P`, with

  `Θ = ∑_{j ∈ ℤ} (-1)^j u^j q^{j(j-1)/2}`,   `P = ∏_{m ≥ 1}(1 - u q^m)(1 - u⁻¹ q^m)(1 - q^m)`.

Write `D = d/dx` (acting on coefficients) and `θ = q d/dq`.  Since `D u = u`:

* the sum side satisfies the **heat equation** `D²Θ - DΘ = 2θΘ` (`heat_tripleSum`);
* the product side has logarithmic derivatives `DP = P·R`, `θP = P·T` with explicit Lambert-type
  series `R`, `T` (`liftD_P`, `eulerOp_P`);

and therefore (`star_identity`), `P` being a unit,

  `(1 - u)(DR + R² - 2T) = (1 + u) R`.                                             (*)

Expanding (*) in `x` at `ε = 1` gives Ramanujan's identity `12P₁² = 5P₃ + P₁ - 6θP₁`, and at
`ε = -1` its level-two companion (`DeligneMLDERamanujan`).
-/

namespace VOA.DeligneAudit.DeligneMLDE.HeatK

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient ring `K⟦x⟧`. -/
local notation "A" => (PowerSeries K)

/-- The `x`-derivative. -/
local notation "dx" => PowerSeries.derivative K

/-! ## The coefficientwise `x`-derivative on `A⟦q⟧` -/

/-- `D`: differentiate every `q`-coefficient in `x`. -/
def liftD (F : PowerSeries A) : PowerSeries A := mk fun n => dx (coeff n F)

@[simp] theorem coeff_liftD (F : PowerSeries A) (n : ℕ) : coeff n (liftD F) = dx (coeff n F) := by
  simp [liftD]

theorem liftD_add (F G : PowerSeries A) : liftD (F + G) = liftD F + liftD G := by
  refine PowerSeries.ext fun n => ?_; simp

theorem liftD_sub (F G : PowerSeries A) : liftD (F - G) = liftD F - liftD G := by
  refine PowerSeries.ext fun n => ?_; simp

theorem liftD_neg (F : PowerSeries A) : liftD (-F) = -liftD F := by
  refine PowerSeries.ext fun n => ?_; simp

theorem liftD_mul (F G : PowerSeries A) : liftD (F * G) = liftD F * G + F * liftD G := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_liftD, coeff_mul, map_add, map_sum, Derivation.leibniz, smul_eq_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

theorem liftD_zero : liftD (0 : PowerSeries A) = 0 := by
  refine PowerSeries.ext fun n => ?_; simp

theorem liftD_C (a : A) : liftD (C a) = C (dx a) := by
  refine PowerSeries.ext fun n => ?_; simp only [coeff_liftD, coeff_C]; split_ifs <;> simp

theorem liftD_one : liftD (1 : PowerSeries A) = 0 := by
  rw [← map_one (C (R := A)), liftD_C, Derivation.map_one_eq_zero _, map_zero]

theorem liftD_X_pow (d : ℕ) : liftD (X ^ d : PowerSeries A) = 0 := by
  refine PowerSeries.ext fun n => ?_; simp only [coeff_liftD, coeff_X_pow]
  split_ifs <;> simp

theorem liftD_natCast (k : ℕ) : liftD (k : PowerSeries A) = 0 := by
  rw [← map_natCast (C (R := A)), liftD_C, Derivation.map_natCast _, map_zero]

theorem AgreeTo.liftD {K : ℕ} {F G : PowerSeries A} (h : AgreeTo K F G) :
    AgreeTo K (liftD F) (liftD G) :=
  AgreeTo.of_coeff fun d hd => by simp [h.coeff_eq hd]

theorem liftD_eulerOp (F : PowerSeries A) : liftD (eulerOp F) = eulerOp (liftD F) := by
  refine PowerSeries.ext fun n => ?_; simp [Derivation.leibniz]

/-! ## The unit `u = ω eˣ` -/

section UnitW

variable (ω : K) (hω : ω ≠ 0)

/-- `u = ω eˣ` as a unit of `K⟦x⟧`. -/
def uW : (PowerSeries K)ˣ where
  val := ω • exp K
  inv := ω⁻¹ • evalNegHom (exp K)
  val_inv := by rw [smul_mul_smul_comm, exp_mul_exp_neg_eq_one, mul_inv_cancel₀ hω, one_smul]
  inv_val := by rw [smul_mul_smul_comm, mul_comm (evalNegHom _), exp_mul_exp_neg_eq_one,
    inv_mul_cancel₀ hω, one_smul]

theorem dx_uW : dx ((uW ω hω : (PowerSeries K)ˣ) : A) = (uW ω hω : A) := by
  change dx (ω • exp K) = ω • exp K
  rw [Derivation.map_smul, derivative_exp]

end UnitW

/-- A unit fixed by a derivation has `D(w^j) = j w^j` for every `j ∈ ℤ`. -/
theorem dx_zpow_of_fixed (w : (PowerSeries K)ˣ) (hw : dx (w : A) = w) (j : ℤ) :
    dx ((w ^ j : (PowerSeries K)ˣ) : A) = (j : A) * ((w ^ j : (PowerSeries K)ˣ) : A) := by
  have hinv : dx ((w⁻¹ : (PowerSeries K)ˣ) : A) = -((w⁻¹ : (PowerSeries K)ˣ) : A) := by
    have h := congrArg dx (Units.mul_inv w)
    rw [Derivation.leibniz, Derivation.map_one_eq_zero _, hw, smul_eq_mul, smul_eq_mul] at h
    have h2 : (w : A) * (dx ((w⁻¹ : (PowerSeries K)ˣ) : A) + ((w⁻¹ : (PowerSeries K)ˣ) : A)) = 0 := by
      linear_combination h
    have h3 := congrArg (fun t => ((w⁻¹ : (PowerSeries K)ˣ) : A) * t) h2
    simp only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] at h3
    linear_combination h3
  rcases j with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Derivation.leibniz_pow,
      hw, smul_eq_mul, Int.cast_natCast]
    rcases n with _ | n
    · simp
    · rw [pow_succ]; push_cast; ring
  · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val, Derivation.leibniz_pow, hinv,
      smul_eq_mul, nsmul_eq_mul, Int.cast_negSucc]
    rcases n with _ | n
    · simp
    · rw [pow_succ]; push_cast; ring

/-! ## The heat equation for the sum side -/

theorem dx_intCast (j : ℤ) : dx (j : A) = 0 := by
  have : (j : A) = algebraMap K A (j : K) := by simp
  rw [this, Derivation.map_algebraMap]

theorem dx_negSign (j : ℤ) : dx (negSign j : A) = 0 := by
  rw [negSign, Derivation.leibniz_pow, Derivation.map_neg _, Derivation.map_one_eq_zero _]; simp

/-- **The heat equation** `D²Θ - DΘ = 2θΘ`, for any unit `w` with `D w = w`. -/
theorem heat_tripleSum (w : (PowerSeries K)ˣ) (hw : dx (w : A) = w) :
    liftD (liftD (tripleSum w)) - liftD (tripleSum w) = 2 * eulerOp (tripleSum w) := by
  have hzp := dx_zpow_of_fixed w hw
  refine PowerSeries.ext fun n => ?_
  simp only [map_sub, coeff_liftD]
  rw [show (2 : PowerSeries A) = C 2 from rfl,
    coeff_C_mul, coeff_eulerOp, tripleSum, coeff_zSeries, map_sum, map_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjn : pentExp j = n := (Finset.mem_filter.mp hj).2
  have h2 := two_mul_cast_pentExp j
  rw [hjn] at h2
  have h2' : (2 : A) * (n : A) = (j : A) * ((j : A) - 1) := by
    have := congrArg (fun t : ℤ => (t : A)) h2
    push_cast at this
    exact this
  simp only [tripleCoeff, Derivation.leibniz, dx_negSign, smul_eq_mul, hzp, mul_zero, add_zero,
    dx_intCast]
  linear_combination (-(negSign j : A) * ((w ^ j : (PowerSeries K)ˣ) : A)) * h2'


/-! ## Geometric series and logarithmic derivatives of the product side -/

section Generic

variable {R : Type*} [CommRing R]

/-- `gs a d = ∑_{k ≥ 1} aᵏ q^{dk} = a qᵈ/(1 - a qᵈ)`. -/
def gs (a : R) (d : ℕ) : PowerSeries R :=
  mk fun n => if 0 < n ∧ d ∣ n then a ^ (n / d) else 0

theorem coeff_gs (a : R) (d n : ℕ) :
    coeff n (gs a d) = if 0 < n ∧ d ∣ n then a ^ (n / d) else 0 := by
  simp [gs]

theorem one_sub_mul_gs (a : R) {d : ℕ} (hd : 0 < d) :
    (1 - C a * X ^ d) * gs a d = C a * X ^ d := by
  refine PowerSeries.ext fun n => ?_
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow,
    coeff_gs]
  by_cases hnd : n = d
  · subst hnd
    rw [if_pos ⟨hd, dvd_refl _⟩, if_pos le_rfl, Nat.sub_self, coeff_gs, if_neg (by omega),
      if_pos rfl, Nat.div_self hd]
    ring
  rw [if_neg hnd, mul_zero]
  by_cases hle : d ≤ n
  · have hlt : d < n := lt_of_le_of_ne hle (Ne.symm hnd)
    rw [if_pos hle, coeff_gs]
    by_cases hdn : d ∣ n
    · obtain ⟨k, rfl⟩ := hdn
      have hk : 2 ≤ k := by
        by_contra hk
        have : d * k ≤ d * 1 := Nat.mul_le_mul_left d (by omega)
        omega
      have e : d * k - d = d * (k - 1) := by rw [Nat.mul_sub, mul_one]
      rw [if_pos ⟨by omega, dvd_mul_right d k⟩, e,
        if_pos ⟨Nat.mul_pos hd (by omega), dvd_mul_right _ _⟩, Nat.mul_div_cancel_left _ hd,
        Nat.mul_div_cancel_left _ hd]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    · have hdn' : ¬ d ∣ n - d := fun h' => hdn (by
        have := Nat.dvd_add h' (dvd_refl d); rwa [Nat.sub_add_cancel hle] at this)
      rw [if_neg (fun h => hdn h.2), if_neg (fun h => hdn' h.2)]
      ring
  · have h1 : ¬ (0 < n ∧ d ∣ n) := fun ⟨hn, hdn⟩ => hle (Nat.le_of_dvd hn hdn)
    rw [if_neg h1, if_neg hle]
    ring

theorem coeff_gs_eq_zero (a : R) {d n : ℕ} (h : n < d) : coeff n (gs a d) = 0 := by
  rw [coeff_gs, if_neg]
  rintro ⟨hn, hdn⟩
  exact absurd (Nat.le_of_dvd hn hdn) (by omega)

/-- Logarithmic derivatives of finite products. -/
theorem logDeriv_prod (L : PowerSeries R → PowerSeries R)
    (hmul : ∀ F G, L (F * G) = L F * G + F * L G)
    (f r : ℕ → PowerSeries R) (hf : ∀ m, L (f m) = f m * r m) (hone : L 1 = 0) :
    ∀ N, L (∏ m ∈ Finset.range N, f m) = (∏ m ∈ Finset.range N, f m) * ∑ m ∈ Finset.range N, r m
  | 0 => by simp [hone]
  | N + 1 => by
      rw [Finset.prod_range_succ, Finset.sum_range_succ, hmul, logDeriv_prod L hmul f r hf hone N,
        hf]
      ring

/-- An infinite sum of series `r m = O(q^{m+1})`. -/
def tailSum (r : ℕ → PowerSeries R) : PowerSeries R :=
  mk fun n => coeff n (∑ m ∈ Finset.range n, r m)

theorem agreeTo_tailSum (r : ℕ → PowerSeries R) (hr : ∀ m n, n ≤ m → coeff n (r m) = 0) (N : ℕ) :
    AgreeTo (N + 1) (tailSum r) (∑ m ∈ Finset.range N, r m) := by
  apply AgreeTo.of_coeff
  intro d hd
  rw [tailSum, coeff_mk, map_sum, map_sum]
  apply Finset.sum_subset
  · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
  · intro m _ hm; simp only [Finset.mem_range, not_lt] at hm; exact hr m d hm

end Generic

variable (w : (PowerSeries K)ˣ)

/-- The `D`-logarithmic derivative of the `m`-th factor: `u⁻¹qᵈ/(1-u⁻¹qᵈ) - uqᵈ/(1-uqᵈ)`. -/
def rho (d : ℕ) : PowerSeries A := gs ((w⁻¹ : (PowerSeries K)ˣ) : A) d - gs (w : A) d

/-- The `θ`-logarithmic derivative of the `m`-th factor. -/
def tau (d : ℕ) : PowerSeries A :=
  -C (d : A) * (gs (w : A) d + gs ((w⁻¹ : (PowerSeries K)ˣ) : A) d + gs 1 d)

/-- `R = ∑_m ρ_{m+1}`. -/
def Rser : PowerSeries A := tailSum fun m => rho w (m + 1)

/-- `T = ∑_m τ_{m+1}`. -/
def Tser : PowerSeries A := tailSum fun m => tau w (m + 1)

/-- The product side `P = ∏_{m ≥ 1}(1 - u q^m)(1 - u⁻¹ q^m)(1 - q^m)`. -/
def Pser : PowerSeries A := infProd (tripleFactor w)

theorem dx_inv_of_fixed (hw : dx (w : A) = w) : dx ((w⁻¹ : (PowerSeries K)ˣ) : A) = -((w⁻¹ : (PowerSeries K)ˣ) : A) := by
  have h := dx_zpow_of_fixed w hw (-1)
  simpa using h

theorem liftD_one_sub (a : A) (d : ℕ) : liftD (1 - C a * X ^ d) = -(C (dx a) * X ^ d) := by
  rw [liftD_sub, liftD_one, liftD_mul, liftD_C, liftD_X_pow]; ring

theorem eulerOp_one_sub (a : A) (d : ℕ) :
    eulerOp (1 - C a * X ^ d) = -(C (d : A) * (C a * X ^ d)) := by
  rw [eulerOp_sub, eulerOp_one, eulerOp_C_mul, eulerOp_X_pow, ← map_natCast (C (R := A))]; ring

theorem liftD_tripleFactor (hw : dx (w : A) = w) (m : ℕ) :
    liftD (tripleFactor w m) = tripleFactor w m * rho w (m + 1) := by
  have h1 := one_sub_mul_gs (w : A) (by omega : 0 < m + 1)
  have h2 := one_sub_mul_gs ((w⁻¹ : (PowerSeries K)ˣ) : A) (by omega : 0 < m + 1)
  have h3 : liftD (1 - X ^ (m + 1) : PowerSeries A) = 0 := by
    rw [liftD_sub, liftD_one, liftD_X_pow, sub_zero]
  rw [tripleFactor, liftD_mul, liftD_mul, h3, liftD_one_sub, liftD_one_sub, hw,
    dx_inv_of_fixed w hw, rho, map_neg]
  linear_combination (-(1 - X ^ (m + 1)) * (1 - C (w : A) * X ^ (m + 1))) * h2
    + ((1 - X ^ (m + 1)) * (1 - C ((w⁻¹ : (PowerSeries K)ˣ) : A) * X ^ (m + 1))) * h1

theorem eulerOp_tripleFactor (m : ℕ) :
    eulerOp (tripleFactor w m) = tripleFactor w m * tau w (m + 1) := by
  have h1 := one_sub_mul_gs (w : A) (by omega : 0 < m + 1)
  have h2 := one_sub_mul_gs ((w⁻¹ : (PowerSeries K)ˣ) : A) (by omega : 0 < m + 1)
  have h3 := one_sub_mul_gs (1 : A) (by omega : 0 < m + 1)
  rw [map_one, one_mul] at h3
  have e3 : eulerOp (1 - X ^ (m + 1) : PowerSeries A) = -(C ((m + 1 : ℕ) : A) * X ^ (m + 1)) := by
    have := eulerOp_one_sub (1 : A) (m + 1)
    rwa [map_one, one_mul] at this
  rw [tripleFactor, eulerOp_mul, eulerOp_mul, e3, eulerOp_one_sub, eulerOp_one_sub, tau]
  linear_combination
    (C ((m + 1 : ℕ) : A) * (1 - C ((w⁻¹ : (PowerSeries K)ˣ) : A) * X ^ (m + 1)) * (1 - X ^ (m + 1))) * h1
    + (C ((m + 1 : ℕ) : A) * (1 - C (w : A) * X ^ (m + 1)) * (1 - X ^ (m + 1))) * h2
    + (C ((m + 1 : ℕ) : A) * (1 - C (w : A) * X ^ (m + 1))
        * (1 - C ((w⁻¹ : (PowerSeries K)ˣ) : A) * X ^ (m + 1))) * h3

theorem rho_vanish (m n : ℕ) (h : n ≤ m) : coeff n (rho w (m + 1)) = 0 := by
  rw [rho, map_sub, coeff_gs_eq_zero _ (by omega), coeff_gs_eq_zero _ (by omega), sub_zero]

theorem tau_vanish (m n : ℕ) (h : n ≤ m) : coeff n (tau w (m + 1)) = 0 := by
  rw [tau, neg_mul, map_neg, coeff_C_mul, map_add, map_add, coeff_gs_eq_zero _ (by omega),
    coeff_gs_eq_zero _ (by omega), coeff_gs_eq_zero _ (by omega)]; simp

/-- `D P = P·R`. -/
theorem liftD_P (hw : dx (w : A) = w) : liftD (Pser w) = Pser w * Rser w := by
  apply eq_of_agreeTo
  intro N
  have hP := agreeTo_infProd (prodFactors_tripleFactor w) N
  have hR := agreeTo_tailSum _ (rho_vanish w) N
  have hfin := logDeriv_prod (liftD (K := K)) liftD_mul (tripleFactor w) (fun m => rho w (m + 1))
    (liftD_tripleFactor w hw) liftD_one N
  have h1 : AgreeTo (N + 1) (liftD (Pser w)) (liftD (∏ k ∈ Finset.range N, tripleFactor w k)) :=
    AgreeTo.liftD hP
  have h2 : AgreeTo (N + 1) ((∏ k ∈ Finset.range N, tripleFactor w k) *
      ∑ m ∈ Finset.range N, rho w (m + 1)) (Pser w * Rser w) := hP.symm.mul hR.symm
  exact (h1.trans (AgreeTo.of_eq hfin)).trans h2

/-- `θ P = P·T`. -/
theorem eulerOp_P : eulerOp (Pser w) = Pser w * Tser w := by
  apply eq_of_agreeTo
  intro N
  have hP := agreeTo_infProd (prodFactors_tripleFactor w) N
  have hT := agreeTo_tailSum _ (tau_vanish w) N
  have hfin := logDeriv_prod eulerOp eulerOp_mul (tripleFactor w) (fun m => tau w (m + 1))
    (eulerOp_tripleFactor w) eulerOp_one N
  exact (hP.eulerOp.trans (AgreeTo.of_eq hfin)).trans (hP.symm.mul hT.symm)

/-- **The identity (*)**: `(1 - u)(DR + R² - 2T) = (1 + u)R`. -/
theorem star_identity (hw : dx (w : A) = w) :
    (1 - C (w : A)) * (liftD (Rser w) + Rser w ^ 2 - 2 * Tser w) = (1 + C (w : A)) * Rser w := by
  have heat := heat_tripleSum w hw
  rw [← jacobiTriple w, ← Pser] at heat
  have hC : liftD (1 - C (w : A)) = -C (w : A) := by
    rw [liftD_sub, liftD_one, liftD_C, hw, zero_sub]
  have hCe : eulerOp (1 - C (w : A)) = 0 := by
    rw [eulerOp_sub, eulerOp_one, show C (w : A) = C (w : A) * 1 by rw [mul_one], eulerOp_C_mul,
      eulerOp_one, mul_zero, sub_zero]
  have hC2 : liftD (C (w : A)) = C (w : A) := by rw [liftD_C, hw]
  simp only [liftD_mul, liftD_add, liftD_sub, liftD_zero, liftD_one, hC2, liftD_P w hw, eulerOp_mul,
    hCe, eulerOp_P] at heat
  have hunit : IsUnit (Pser w) := isUnit_infProd _
  have key : Pser w * ((1 - C (w : A)) * (liftD (Rser w) + Rser w ^ 2 - 2 * Tser w)
      - (1 + C (w : A)) * Rser w) = 0 := by
    linear_combination heat
  have := (hunit.mul_right_eq_zero).mp key
  linear_combination this

end

end VOA.DeligneAudit.DeligneMLDE.HeatK
