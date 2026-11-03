import VOA.DeligneAudit.D4CharPieriInteger

/-! The integer Gaussian weights of E-step, with genuine integer powers of a unit q. -/

namespace VOA.DeligneAudit.D4Char

variable {R : Type*} [CommRing R]

/-- Integer powers, without imposing a field structure on the coefficient ring. -/
def pieriPower (q : Rˣ) (a : ℤ) : R := ↑(q ^ a)

@[simp] theorem pieriPower_nat (q : Rˣ) (a : ℕ) :
    pieriPower q a = (q : R) ^ a := by
  simp [pieriPower]

theorem pieriPower_nonneg (q : Rˣ) (a : ℤ) (ha : 0 ≤ a) :
    pieriPower q a = (q : R) ^ a.toNat := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  simp

theorem pieriPower_add (q : Rˣ) (a b : ℤ) :
    pieriPower q (a + b) = pieriPower q a * pieriPower q b := by
  simp [pieriPower, zpow_add]

theorem intQbinom_unit_pascal (q : Rˣ) (a b : ℤ) (ha : 0 ≤ a) :
    intQbinom (q : R) (a + 1) (b + 1) =
      pieriPower q (a - b) * intQbinom (q : R) a b +
        intQbinom (q : R) a (b + 1) := by
  rw [intQbinom_pascal _ _ _ ha]
  by_cases hab : b ≤ a
  · rw [pieriPower_nonneg _ _ (by omega)]
  · rw [intQbinom_above _ _ _ (by omega)]
    simp

theorem intQbinom_unit_balance (q : Rˣ) (a b : ℤ) (ha : 0 ≤ a) :
    (1 - pieriPower q (a - b)) * intQbinom (q : R) a b =
      (1 - pieriPower q (b + 1)) * intQbinom (q : R) a (b + 1) := by
  by_cases hab : a < b
  · rw [intQbinom_above _ _ _ hab, intQbinom_above _ _ _ (by omega)]
    simp
  by_cases hb : b < -1
  · rw [intQbinom_lower_neg _ _ _ (by omega), intQbinom_lower_neg _ _ _ (by omega)]
    simp
  rw [pieriPower_nonneg _ _ (by omega), pieriPower_nonneg _ _ (by omega)]
  exact intQbinom_balance _ a b ha

theorem intQbinom_unit_lower (q : Rˣ) (a b : ℤ) (ha : 0 ≤ a) :
    intQbinom (q : R) (a - 1) b * (1 - pieriPower q a) =
      (1 - pieriPower q (a - b)) * intQbinom (q : R) a b := by
  by_cases hab : a < b
  · rw [intQbinom_above _ _ _ (by omega), intQbinom_above _ _ _ hab]
    simp
  rw [pieriPower_nonneg _ _ ha, pieriPower_nonneg _ _ (by omega)]
  exact intQbinom_lower _ a b ha

/-- Boolean states interpreted as integer box indicators. -/
def pieriBit (s : Bool) : ℤ := if s then 1 else 0

/-- The local left weight in E-step, including the E-factor at the next position. -/
def pieriW (q : Rˣ) (a b : ℤ) (s t : Bool) : R :=
  intQbinom (q : R) (a + pieriBit s - pieriBit t) (b + pieriBit s) *
    if t && !s then 1 - pieriPower q a else 1

/-- Exact four-entry identification, without assuming the lower index is in range. -/
theorem pieriW_entries (q : Rˣ) (a b : ℤ) (ha : 0 ≤ a) :
    pieriW q a b false false = intQbinom (q : R) a b ∧
    pieriW q a b true true = intQbinom (q : R) a (b + 1) ∧
    pieriW q a b true false =
      pieriPower q (a - b) * intQbinom (q : R) a b + intQbinom (q : R) a (b + 1) ∧
    pieriW q a b false true =
      (1 - pieriPower q (a - b)) * intQbinom (q : R) a b := by
  simp only [pieriW, pieriBit, Bool.false_eq_true, ↓reduceIte, add_zero, sub_zero,
    Bool.not_false, Bool.not_true, Bool.and_self, Bool.and_false, Bool.and_true,
    add_sub_cancel_right, mul_one]
  exact ⟨trivial, trivial, intQbinom_unit_pascal q a b ha, intQbinom_unit_lower q a b ha⟩

/-- A transfer edge for every integer lower index. -/
def intGaussianPieriEdge (q : Rˣ) (a b : ℤ) (ha : 0 ≤ a) : PieriEdge R where
  c := pieriPower q (a - b)
  beta := pieriPower q (b + 1)
  X := intQbinom (q : R) a b
  Y := intQbinom (q : R) a (b + 1)
  balance := intQbinom_unit_balance q a b ha

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriPower_add
#print axioms VOA.DeligneAudit.D4Char.intQbinom_unit_pascal
#print axioms VOA.DeligneAudit.D4Char.intQbinom_unit_balance
#print axioms VOA.DeligneAudit.D4Char.intQbinom_unit_lower
#print axioms VOA.DeligneAudit.D4Char.pieriW_entries
