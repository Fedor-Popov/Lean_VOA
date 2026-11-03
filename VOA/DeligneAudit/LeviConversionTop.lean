import VOA.DeligneAudit.LeviConversionLemma

/-! Separation of the top Wick contraction from the lower terms. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {A : Type*} [Ring A]

theorem conversionTerm_top (f a b : ℕ → A) (k s : ℕ)
    (p : List ℕ × List ℕ) (ht : p.2.length = k) :
    conversionTerm f a b k s p =
      (-1 : A) ^ k * (k.factorial : A) *
        (aWord a p.1 * PowerSeries.coeff s (bWord b p.2)) := by
  rw [conversionTerm, ht, Nat.descFactorial_self, Nat.sub_self, pow_zero]
  have hsum :
      (∑ q ∈ Finset.antidiagonal s,
        (PowerSeries.coeff q.1 (1 : PowerSeries A) * aWord a p.1) *
          PowerSeries.coeff q.2 (bWord b p.2)) =
        aWord a p.1 * PowerSeries.coeff s (bWord b p.2) := by
    calc
      _ = ∑ q ∈ Finset.antidiagonal s,
          PowerSeries.coeff q.1 (1 * PowerSeries.C (aWord a p.1)) *
            PowerSeries.coeff q.2 (bWord b p.2) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [PowerSeries.coeff_mul_C]
      _ = PowerSeries.coeff s ((1 * PowerSeries.C (aWord a p.1)) *
          bWord b p.2) := (PowerSeries.coeff_mul _ _ _).symm
      _ = _ := by simp only [one_mul, PowerSeries.coeff_C_mul]
  rw [hsum]

theorem conversionTerm_gt (f a b : ℕ → A) (k s : ℕ)
    (p : List ℕ × List ℕ) (ht : k < p.2.length) :
    conversionTerm f a b k s p = 0 := by
  simp [conversionTerm, Nat.descFactorial_of_lt ht]

def topSum (a b : ℕ → A) (k s : ℕ) (xs : List ℕ) : A :=
  ((choices xs).map fun p =>
    if p.2.length = k then aWord a p.1 * PowerSeries.coeff s (bWord b p.2)
    else 0).sum

def lowerSum (f a b : ℕ → A) (k s : ℕ) (xs : List ℕ) : A :=
  ((choices xs).map fun p =>
    if p.2.length < k then conversionTerm f a b k s p else 0).sum

theorem conversion_sum_split (f a b : ℕ → A) (k s : ℕ) (xs : List ℕ) :
    ((choices xs).map (conversionTerm f a b k s)).sum =
      ((-1 : A) ^ k * (k.factorial : A)) * topSum a b k s xs +
        lowerSum f a b k s xs := by
  rw [topSum, lowerSum, ← List.sum_map_mul_left, ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro p hp
  by_cases htop : p.2.length = k
  · simp [htop, conversionTerm_top f a b k s p htop]
  · by_cases hlow : p.2.length < k
    · simp [htop, hlow]
    · have hgt : k < p.2.length := by omega
      simp [htop, hlow, conversionTerm_gt f a b k s p hgt]

variable {V : Type*} [AddCommGroup V] [Module A V]

/-- Lemma C, with positional subsets encoded by `choices` and lower convolutions
expanded by `conversionTerm`. The spectator need only commute with the `f` modes. -/
theorem lemmaC (f a b : ℕ → A)
    (hfa : ∀ i j, f i * a j - a j * f i = b (i + j))
    (hfb : ∀ i j, f i * b j = b j * f i)
    (hab : ∀ i j, a i * b j = b j * a i)
    (k s : ℕ) (xs : List ℕ) (R : A) (v : V)
    (hRf : ∀ i, R * f i = f i * R)
    (hkill : PowerSeries.coeff s (fCurrent f ^ k) • v = 0) :
    (((-1 : A) ^ k * (k.factorial : A)) * topSum a b k s xs) • (R • v) =
      -(lowerSum f a b k s xs • (R • v)) := by
  have h := conversion_sum_zero_of_spectator f a b hfa hfb hab k s xs R v hRf hkill
  rw [conversion_sum_split] at h
  rw [add_smul] at h
  exact eq_neg_of_add_eq_zero_left h

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.lemmaC
