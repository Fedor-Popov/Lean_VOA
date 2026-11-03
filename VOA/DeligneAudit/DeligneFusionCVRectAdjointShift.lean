import VOA.DeligneAudit.DeligneFusionCVRectAdjointOrder
import VOA.DeligneAudit.DeligneFusionCVRectStarShift

/-! # Actual polynomial shift maps for the adjoint-site upper recursion -/

namespace VOA.DeligneAudit.A2.CVRectAdjointShift

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectAdjointOrder

noncomputable section

theorem adjOrder_lipschitz (p m q r : ℕ) (hm : m ≤ p) :
    adjOrder p q r ≤ adjOrder m q r + (p - m) := by
  unfold adjOrder
  omega

theorem special_shift_order_le (left right center : List ℕ) (p q r m : ℕ) (hm : m ≤ p) :
    fiveSiteOrder left right center p q r ≤
      adjointOrder left right center m q r + left.length * (p - m) := by
  have he := CVRectShift.excess_le_sub_add left (p + q) (p - m)
  rw [show p + q - (p - m) = m + q by omega] at he
  have ha := adjOrder_shift_le p m q r hm
  unfold fiveSiteOrder adjointOrder background
  omega

theorem ordinary_shift_order_le (left right center : List ℕ) (K p q r m : ℕ)
    (hm : m ≤ p) :
    adjointOrder left right (K :: center) p q r ≤
      adjointOrder (K :: left) right center m q r + (left.length + 1) * (p - m) := by
  have he := CVRectStarShift.leaf_shift_order_le left right center K p q r m hm
  have ha := adjOrder_lipschitz p m q r hm
  simp only [CVRectStarIdeal.starOrder] at he
  simp only [adjointOrder, background, Nat.add_mul, Nat.one_mul]
  omega

section Series

variable {R : Type*} [CommRing R]

/-- Binomial expansion transfers actual coefficient orders whenever
the explicit source and shifted orders satisfy the displayed inequality. -/
theorem shift_order_of_le (X Y Z V : PowerSeries R)
    (μ τ : ℕ → ℕ → ℕ → ℕ) (h : ℕ)
    (hle : ∀ p q r m, m ≤ p → τ p q r ≤ μ m q r + h * (p - m))
    (hV : PowerSeries.X ^ h ∣ V)
    (hsource : ∀ p q r, PowerSeries.X ^ μ p q r ∣ X ^ p * Y ^ q * Z ^ r) :
    ∀ p q r, PowerSeries.X ^ τ p q r ∣ (X - V) ^ p * Y ^ q * Z ^ r := by
  intro p q r
  rw [sub_eq_add_neg, (Commute.all X (-V)).add_pow, Finset.sum_mul, Finset.sum_mul]
  apply Finset.dvd_sum
  intro m hm
  have hm' : m ≤ p := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
  have hvpow : PowerSeries.X ^ (h * (p - m)) ∣ (-V) ^ (p - m) := by
    obtain ⟨W, hW⟩ := hV
    have hv : -V = PowerSeries.X ^ h * (-W) := by rw [hW]; ring
    refine ⟨(-W) ^ (p - m), ?_⟩
    rw [hv, mul_pow, pow_mul]
  have hprod : PowerSeries.X ^ (μ m q r + h * (p - m)) ∣
      (X ^ m * Y ^ q * Z ^ r) * (-V) ^ (p - m) := by
    rw [pow_add]
    exact mul_dvd_mul (hsource m q r) hvpow
  have hdiv := (pow_dvd_pow PowerSeries.X (hle p q r m hm')).trans hprod
  convert dvd_mul_of_dvd_left hdiv (p.choose m : PowerSeries R) using 1
  ring

end Series

section Polynomial

variable {A : Type*} [CommRing A]

/-- The concrete shift preserves the entire actual target coefficient
ideal, including all polynomial multiples of every generator. -/
theorem shift_ideal_map_of_orders (f g h : PowerSeries A)
    (μ τ : ℕ → ℕ → ℕ → ℕ) (n : ℕ)
    (hle : ∀ p q r m, m ≤ p → τ p q r ≤ μ m q r + n * (p - m)) :
    Ideal.map Polynomial.C (coefficientIdeal3 f g h τ) ≤
      coefficientIdeal3 (chosenCurrent n f) (constantCurrent g) (constantCurrent h) μ := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro P ⟨p, q, r, j, hj, rfl⟩
  let X := chosenCurrent n f
  let Y := constantCurrent g
  let Z := constantCurrent h
  let V : PowerSeries (Polynomial A) := PowerSeries.C Polynomial.X * PowerSeries.X ^ n
  let J := coefficientIdeal3 X Y Z μ
  let π := Ideal.Quotient.mk J
  let Q := PowerSeries.map π
  have hv : PowerSeries.X ^ n ∣ Q V := by
    refine ⟨Q (PowerSeries.C Polynomial.X), ?_⟩
    simp only [V, map_mul, map_pow, Q, PowerSeries.map_X]
    ring
  have hs : ∀ p q r, PowerSeries.X ^ μ p q r ∣ Q X ^ p * Q Y ^ q * Q Z ^ r :=
    CVRectStarShift.source_order_quotient X Y Z μ
  have hz := PowerSeries.X_pow_dvd_iff.mp
    (shift_order_of_le (Q X) (Q Y) (Q Z) (Q V) μ τ n hle hv hs p q r) j hj
  have heq : Q X - Q V = Q (constantCurrent f) := by
    rw [← map_sub]
    congr 1
    dsimp only [X, V, chosenCurrent]
    abel
  rw [heq, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul,
    PowerSeries.coeff_map] at hz
  have hc : PowerSeries.coeff j
      (constantCurrent f ^ p * constantCurrent g ^ q * constantCurrent h ^ r) =
      Polynomial.C (PowerSeries.coeff j (f ^ p * g ^ q * h ^ r)) := by
    unfold constantCurrent
    rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, PowerSeries.coeff_map]
  change π (PowerSeries.coeff j
    (constantCurrent f ^ p * constantCurrent g ^ q * constantCurrent h ^ r)) = 0 at hz
  rw [hc] at hz
  have hzmem : Polynomial.C (PowerSeries.coeff j (f ^ p * g ^ q * h ^ r)) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact hzmem

theorem adjoint_special_shift (f g h : PowerSeries A) (left right center : List ℕ) :
    Ideal.map Polynomial.C (coefficientIdeal3 f g h (fiveSiteOrder left right center)) ≤
      coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (adjointOrder left right center) :=
  shift_ideal_map_of_orders f g h _ _ left.length (special_shift_order_le left right center)

theorem adjoint_ordinary_shift (f g h : PowerSeries A) (left right center : List ℕ) (K : ℕ) :
    Ideal.map Polynomial.C (coefficientIdeal3 f g h (adjointOrder left right (K :: center))) ≤
      coefficientIdeal3 (chosenCurrent (left.length + 1) f) (constantCurrent g)
        (constantCurrent h) (adjointOrder (K :: left) right center) :=
  shift_ideal_map_of_orders f g h _ _ (left.length + 1)
    (ordinary_shift_order_le left right center K)

end Polynomial

end
end VOA.DeligneAudit.A2.CVRectAdjointShift

#print axioms VOA.DeligneAudit.A2.CVRectAdjointShift.shift_ideal_map_of_orders
#print axioms VOA.DeligneAudit.A2.CVRectAdjointShift.adjoint_special_shift
#print axioms VOA.DeligneAudit.A2.CVRectAdjointShift.adjoint_ordinary_shift
