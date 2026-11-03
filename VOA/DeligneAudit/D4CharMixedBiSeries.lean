import VOA.DeligneAudit.D4CharMixedEulerCoeff

/-! Two formal y variables and coefficient maps for the stable mixed Euler kernel. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- The inner variable is y_1 and the outer variable is y_2. -/
abbrev GTBiSeries (R : Type*) := PowerSeries (PowerSeries R)

def gtBiC : R →+* GTBiSeries R := PowerSeries.C.comp PowerSeries.C

def gtBiCoeff (t v : ℕ) : GTBiSeries R →+ R :=
  (coeff t).toAddMonoidHom.comp (coeff v).toAddMonoidHom

theorem gtBiCoeff_C_mul (a : R) (F : GTBiSeries R) (t v : ℕ) :
    gtBiCoeff t v (gtBiC a * F) = a * gtBiCoeff t v F := by
  simp [gtBiCoeff, gtBiC, coeff_C_mul]

theorem gtBiCoeff_yFirst (F : GTBiSeries R) (t v : ℕ) :
    gtBiCoeff t v (PowerSeries.C X * F) =
      if 0 < t then gtBiCoeff (t - 1) v F else 0 := by
  cases t with
  | zero => simp [gtBiCoeff, coeff_C_mul, coeff_zero_eq_constantCoeff]
  | succ t => simp [gtBiCoeff, coeff_C_mul, coeff_succ_X_mul]

theorem gtBiCoeff_ySecond (F : GTBiSeries R) (t v : ℕ) :
    gtBiCoeff t v (X * F) = if 0 < v then gtBiCoeff t (v - 1) F else 0 := by
  cases v with
  | zero => simp [gtBiCoeff, coeff_zero_eq_constantCoeff]
  | succ v => simp [gtBiCoeff, coeff_succ_X_mul]

theorem gtBiCoeff_yBoth (F : GTBiSeries R) (t v : ℕ) :
    gtBiCoeff t v ((PowerSeries.C X * X) * F) =
      if 0 < t ∧ 0 < v then gtBiCoeff (t - 1) (v - 1) F else 0 := by
  rw [mul_assoc, gtBiCoeff_yFirst]
  by_cases ht : 0 < t
  · simp only [ht, ↓reduceIte, true_and, gtBiCoeff_ySecond]
  · simp [ht]

/-- Product of two identical one-variable series in independent y variables. -/
theorem gtBiCoeff_separate (A : PowerSeries R) (t v : ℕ) :
    gtBiCoeff t v (PowerSeries.C A * A.map PowerSeries.C) = coeff t A * coeff v A := by
  simp [gtBiCoeff, coeff_C_mul, coeff_map, coeff_mul_C]

/-- The two actual formal y variables, as coefficients for the next x-variable series. -/
def gtBiY (i : ℕ) : GTBiSeries R := if i = 0 then PowerSeries.C X else X

@[simp] theorem gtBiY_zero : gtBiY (R := R) 0 = PowerSeries.C X := by simp [gtBiY]

@[simp] theorem gtBiY_one : gtBiY (R := R) 1 = X := by simp [gtBiY]

theorem gtBiCoeff_yZero (F : GTBiSeries R) (t v : ℕ) :
    gtBiCoeff t v (gtBiY 0 * F) =
      if 0 < t then gtBiCoeff (t - 1) v F else 0 := by
  rw [gtBiY_zero, gtBiCoeff_yFirst]

theorem gtBiCoeff_yOne (F : GTBiSeries R) (t v : ℕ) :
    gtBiCoeff t v (gtBiY 1 * F) = if 0 < v then gtBiCoeff t (v - 1) F else 0 := by
  rw [gtBiY_one, gtBiCoeff_ySecond]

theorem gtBiCoeff_yZeroOne (F : GTBiSeries R) (t v : ℕ) :
    gtBiCoeff t v ((gtBiY 0 * gtBiY 1) * F) =
      if 0 < t ∧ 0 < v then gtBiCoeff (t - 1) (v - 1) F else 0 := by
  rw [gtBiY_zero, gtBiY_one, gtBiCoeff_yBoth]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_C_mul
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_yFirst
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_ySecond
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_yBoth
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_separate
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_yZero
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_yOne
#print axioms VOA.DeligneAudit.D4Char.gtBiCoeff_yZeroOne
