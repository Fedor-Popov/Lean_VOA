import VOA.DeligneAudit.D4CharQY

/-! Integral Euler series and their q-difference equations, over a general coefficient ring. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

theorem pochhammerUnits_qDifferenceUnits (q : R) (h : PochhammerUnits q) :
    QDifferenceUnits q := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hk := h (k + 1)
  rw [CarrierChain.qpochGen_succ] at hk
  exact isUnit_of_mul_isUnit_right hk

/-- The inverse Euler factor, with x as a coefficient-ring variable. -/
def gtEulerInv (q : R) (h : PochhammerUnits q) (x : R) : PowerSeries R :=
  PowerSeries.mk fun n : ℕ => gtInvPoch q h n * x ^ n

/-- The Euler factor, with x as a coefficient-ring variable. -/
def gtEulerPos (q : R) (h : PochhammerUnits q) (x : R) : PowerSeries R :=
  PowerSeries.mk fun n : ℕ => (-1) ^ n * q ^ (n * (n - 1) / 2) * gtInvPoch q h n * x ^ n

@[simp] theorem constantCoeff_gtEulerInv (q : R) (h : PochhammerUnits q) (x : R) :
    constantCoeff (gtEulerInv q h x) = 1 := by simp [gtEulerInv]

@[simp] theorem constantCoeff_gtEulerPos (q : R) (h : PochhammerUnits q) (x : R) :
    constantCoeff (gtEulerPos q h x) = 1 := by simp [gtEulerPos]

/-- Euler's inverse series satisfies its defining q-difference equation. -/
theorem gtEulerInv_shift (q : R) (h : PochhammerUnits q) (x : R) :
    rescale q (gtEulerInv q h x) = gtEulerInv q h x * (1 - PowerSeries.C x * X) := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub, coeff_rescale]
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ n =>
      rw [coeff_succ_mul_X, coeff_mul_C]
      simp only [gtEulerInv, coeff_mk, Nat.cast_add, Nat.cast_one]
      rw [gtInvPoch_succ q h n, pow_succ x n]
      ring

theorem gtTriangular_succ (n : ℕ) :
    (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.add_sub_cancel]
      have he : (n + 1 + 1) * (n + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      rw [he, Nat.add_mul_div_left _ _ (by norm_num)]
      simp [mul_comm]

/-- Euler's positive series satisfies its defining q-difference equation. -/
theorem gtEulerPos_shift (q : R) (h : PochhammerUnits q) (x : R) :
    gtEulerPos q h x = (1 - PowerSeries.C x * X) * rescale q (gtEulerPos q h x) := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ n =>
      rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul, coeff_rescale, coeff_rescale]
      simp only [gtEulerPos, coeff_mk, Nat.cast_add, Nat.cast_one]
      rw [gtTriangular_succ, pow_add, gtInvPoch_succ q h n]
      simp only [pow_succ]
      ring

/-- The two integral Euler factors are inverses; uniqueness replaces field division. -/
theorem gtEulerPos_mul_inv (q : R) (h : PochhammerUnits q) (x : R) :
    gtEulerPos q h x * gtEulerInv q h x = 1 := by
  have hf : rescale q (gtEulerPos q h x * gtEulerInv q h x) =
      gtEulerPos q h x * gtEulerInv q h x := by
    rw [map_mul, gtEulerInv_shift]
    calc
      _ = ((1 - PowerSeries.C x * X) * rescale q (gtEulerPos q h x)) * gtEulerInv q h x := by
        ring
      _ = _ := by rw [← gtEulerPos_shift]
  apply qDifference_unique q (pochhammerUnits_qDifferenceUnits q h) 1 1
    (gtEulerPos q h x * gtEulerInv q h x) 1 (by simp) (by simp)
  · simpa using hf
  · simp
  · simp

/-- Multiplication of one-row Euler factors is compatible with the Cauchy q-difference. -/
theorem gtEulerInv_product_shift (q : R) (h : PochhammerUnits q)
    (u : ℕ → R) (N : ℕ) :
    rescale q (∏ i ∈ Finset.range N, gtEulerInv q h (u i)) =
      (∏ i ∈ Finset.range N, gtEulerInv q h (u i)) *
        ∏ i ∈ Finset.range N, (1 - PowerSeries.C (u i) * X) := by
  simp only [map_prod, gtEulerInv_shift, Finset.prod_mul_distrib]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pochhammerUnits_qDifferenceUnits
#print axioms VOA.DeligneAudit.D4Char.gtEulerInv_shift
#print axioms VOA.DeligneAudit.D4Char.gtEulerPos_shift
#print axioms VOA.DeligneAudit.D4Char.gtEulerPos_mul_inv
#print axioms VOA.DeligneAudit.D4Char.gtEulerInv_product_shift
