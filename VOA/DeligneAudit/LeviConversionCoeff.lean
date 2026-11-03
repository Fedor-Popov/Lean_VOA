import VOA.DeligneAudit.LeviConversionSeries

/-! Coefficient form of the Wick summands. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A : Type*} [Ring A]

def aWord (a : ℕ → A) (xs : List ℕ) : A := (xs.map a).prod

def bWord (b : ℕ → A) (xs : List ℕ) : PowerSeries A :=
  (xs.map (bTail b)).prod

theorem aConst_word (a : ℕ → A) (xs : List ℕ) :
    (xs.map (aConst a)).prod = PowerSeries.C (aWord a xs) := by
  induction xs with
  | nil => simp [aWord]
  | cons x xs ih =>
      change PowerSeries.C (a x) * (xs.map (aConst a)).prod =
        PowerSeries.C (a x * aWord a xs)
      rw [ih, map_mul]

/-- A Wick summand as a convolution of current and contracted-tail coefficients. -/
theorem wickTerm_coeff (f a b : ℕ → A) (k s : ℕ) (p : List ℕ × List ℕ) :
    PowerSeries.coeff s
      (wickTerm (fCurrent f) (aConst a) (bTail b) k p) =
      (-1 : A) ^ p.2.length * (k.descFactorial p.2.length : A) *
        ∑ q ∈ Finset.antidiagonal s,
          (PowerSeries.coeff q.1 (fCurrent f ^ (k - p.2.length)) *
            aWord a p.1) * PowerSeries.coeff q.2 (bWord b p.2) := by
  rw [wickTerm]
  have hs : (-1 : PowerSeries A) ^ p.2.length *
      (k.descFactorial p.2.length : PowerSeries A) =
      PowerSeries.C ((-1 : A) ^ p.2.length *
        (k.descFactorial p.2.length : A)) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [hs, PowerSeries.coeff_C_mul]
  congr 1
  rw [aConst_word]
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mul_C, bWord]

/-- The coefficient contribution of one choice of contracted positions. -/
def conversionTerm (f a b : ℕ → A) (k s : ℕ)
    (p : List ℕ × List ℕ) : A :=
  (-1 : A) ^ p.2.length * (k.descFactorial p.2.length : A) *
    ∑ q ∈ Finset.antidiagonal s,
      (PowerSeries.coeff q.1 (fCurrent f ^ (k - p.2.length)) *
        aWord a p.1) * PowerSeries.coeff q.2 (bWord b p.2)

theorem coeff_wickSum (f a b : ℕ → A) (k s : ℕ) (xs : List ℕ) :
    PowerSeries.coeff s
      (wickSum (fCurrent f) (aConst a) (bTail b) k xs) =
      ((choices xs).map (conversionTerm f a b k s)).sum := by
  simp only [wickSum, map_list_sum, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact wickTerm_coeff f a b k s p

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.wickTerm_coeff
