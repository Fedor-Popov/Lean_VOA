import VOA.DeligneAudit.LeviConversionCore

/-! The noncommutative Wick identity for current power series. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A : Type*} [Ring A]

/-- The `f` current in the repository's `PowerSeries.mk` convention. -/
def fCurrent (f : ℕ → A) : PowerSeries A := PowerSeries.mk f

/-- The tail of the `b` current starting at mode `x`. -/
def bTail (b : ℕ → A) (x : ℕ) : PowerSeries A :=
  PowerSeries.mk fun i => b (x + i)

/-- A constant `a` mode. -/
def aConst (a : ℕ → A) (x : ℕ) : PowerSeries A := PowerSeries.C (a x)

theorem current_comm_a (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j)) (x : ℕ) :
    fCurrent f * aConst a x - aConst a x * fCurrent f = bTail b x := by
  apply PowerSeries.ext
  intro n
  simp only [map_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul,
    fCurrent, aConst, bTail, PowerSeries.coeff_mk]
  rw [hfa n x, Nat.add_comm]

theorem current_comm_b (f b : ℕ → A)
    (hfb : ∀ i j, f i * b j = b j * f i) (x : ℕ) :
    fCurrent f * bTail b x = bTail b x * fCurrent f := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mul, fCurrent, bTail, PowerSeries.coeff_mk]
  rw [← Finset.Nat.sum_antidiagonal_swap
    (f := fun p : ℕ × ℕ => b (x + p.1) * f p.2)]
  apply Finset.sum_congr rfl
  intro p hp
  exact hfb p.1 (x + p.2)

theorem const_comm_tail (a b : ℕ → A)
    (hab : ∀ i j, a i * b j = b j * a i) (x y : ℕ) :
    aConst a x * bTail b y = bTail b y * aConst a x := by
  apply PowerSeries.ext
  intro n
  simp only [aConst, bTail, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_C, PowerSeries.coeff_mk]
  exact hab x (y + n)

/-- The full ordered Wick identity in the power-series ring. -/
theorem wick_series (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k : ℕ) (xs : List ℕ) :
    (xs.map (aConst a)).prod * fCurrent f ^ k =
      wickSum (fCurrent f) (aConst a) (bTail b) k xs := by
  exact wick_identity (fCurrent f) (aConst a) (bTail b)
    (current_comm_a f a b hfa) (current_comm_b f b hfb)
    (const_comm_tail a b hab) k xs

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.wick_series
