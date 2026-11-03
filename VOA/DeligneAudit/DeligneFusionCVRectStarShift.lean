import VOA.DeligneAudit.DeligneFusionCVRectStarIdeal
import VOA.DeligneAudit.DeligneFusionCVRectShift

/-! # The actual leaf-color shift ideal map for the three-color star -/

namespace VOA.DeligneAudit.A2.CVRectStarShift

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectIntegrationIdeal
open VOA.DeligneAudit.A2.CVRectStarIdeal

noncomputable section

theorem leaf_shift_order_le (left right center : List ℕ) (K p q r m : ℕ) (hm : m ≤ p) :
    starOrder left right (K :: center) p q r ≤
      starOrder (K :: left) right center m q r + left.length * (p - m) := by
  have he := CVRectShift.shiftedOrder_le left [] K p q m hm
  simp only [CVRectShift.shiftedOrder, mixedOrder, siteOrder, excess,
    List.map_nil, List.sum_nil, Nat.zero_add] at he
  simp only [starOrder, excess, List.map_cons, List.sum_cons]
  omega

section Series

variable {R : Type*} [CommRing R]

/-- Binomial expansion transfers actual source orders after removing
the selected leaf zero-mode term. -/
theorem leaf_shift_order (X Y Z V : PowerSeries R)
    (left right center : List ℕ) (K : ℕ)
    (hV : PowerSeries.X ^ left.length ∣ V)
    (hsource : ∀ p q r, PowerSeries.X ^ starOrder (K :: left) right center p q r ∣
      X ^ p * Y ^ q * Z ^ r) :
    ∀ p q r, PowerSeries.X ^ starOrder left right (K :: center) p q r ∣
      (X - V) ^ p * Y ^ q * Z ^ r := by
  intro p q r
  rw [sub_eq_add_neg, (Commute.all X (-V)).add_pow, Finset.sum_mul, Finset.sum_mul]
  apply Finset.dvd_sum
  intro m hm
  have hm' : m ≤ p := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
  have hvpow : PowerSeries.X ^ (left.length * (p - m)) ∣ (-V) ^ (p - m) := by
    obtain ⟨W, hW⟩ := hV
    have hv : -V = PowerSeries.X ^ left.length * (-W) := by rw [hW]; ring
    refine ⟨(-W) ^ (p - m), ?_⟩
    rw [hv, mul_pow, pow_mul]
  have hprod : PowerSeries.X ^
      (starOrder (K :: left) right center m q r + left.length * (p - m)) ∣
        (X ^ m * Y ^ q * Z ^ r) * (-V) ^ (p - m) := by
    rw [pow_add]
    exact mul_dvd_mul (hsource m q r) hvpow
  have hle := leaf_shift_order_le left right center K p q r m hm'
  have hdiv := (pow_dvd_pow PowerSeries.X hle).trans hprod
  convert dvd_mul_of_dvd_left hdiv (p.choose m : PowerSeries R) using 1; ring

theorem source_order_quotient (X Y Z : PowerSeries R)
    (μ : ℕ → ℕ → ℕ → ℕ) (p q r : ℕ) :
    PowerSeries.X ^ μ p q r ∣
      (PowerSeries.map (Ideal.Quotient.mk (coefficientIdeal3 X Y Z μ)) X) ^ p *
        (PowerSeries.map (Ideal.Quotient.mk (coefficientIdeal3 X Y Z μ)) Y) ^ q *
        (PowerSeries.map (Ideal.Quotient.mk (coefficientIdeal3 X Y Z μ)) Z) ^ r := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro j hj
  rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, PowerSeries.coeff_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨p, q, r, j, hj, rfl⟩

end Series

section Polynomial

variable {A : Type*} [CommRing A]

theorem shift_coefficient_mem (f g h : PowerSeries A)
    (left right center : List ℕ) (K p q r j : ℕ)
    (hj : j < starOrder left right (K :: center) p q r) :
    Polynomial.C (PowerSeries.coeff j (f ^ p * g ^ q * h ^ r)) ∈
      coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (starOrder (K :: left) right center) := by
  let X := chosenCurrent left.length f
  let Y := constantCurrent g
  let Z := constantCurrent h
  let V : PowerSeries (Polynomial A) := PowerSeries.C Polynomial.X * PowerSeries.X ^ left.length
  let J := coefficientIdeal3 X Y Z (starOrder (K :: left) right center)
  let π := Ideal.Quotient.mk J
  let Q := PowerSeries.map π
  have hv : PowerSeries.X ^ left.length ∣ Q V := by
    refine ⟨Q (PowerSeries.C Polynomial.X), ?_⟩
    simp only [V, map_mul, map_pow, Q, PowerSeries.map_X]
    ring
  have hs : ∀ p q r, PowerSeries.X ^ starOrder (K :: left) right center p q r ∣
      Q X ^ p * Q Y ^ q * Q Z ^ r :=
    source_order_quotient X Y Z (starOrder (K :: left) right center)
  have hz := PowerSeries.X_pow_dvd_iff.mp
    (leaf_shift_order (Q X) (Q Y) (Q Z) (Q V) left right center K hv hs p q r) j hj
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
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

/-- The xy-to-y leaf shift preserves the whole actual coefficient ideal. -/
theorem shift_ideal_map (f g h : PowerSeries A)
    (left right center : List ℕ) (K : ℕ) :
    Ideal.map Polynomial.C
      (coefficientIdeal3 f g h (starOrder left right (K :: center))) ≤
      coefficientIdeal3 (chosenCurrent left.length f) (constantCurrent g) (constantCurrent h)
        (starOrder (K :: left) right center) := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro P ⟨p, q, r, j, hj, rfl⟩
  exact shift_coefficient_mem f g h left right center K p q r j hj

end Polynomial

end

end VOA.DeligneAudit.A2.CVRectStarShift

#print axioms VOA.DeligneAudit.A2.CVRectStarShift.leaf_shift_order
#print axioms VOA.DeligneAudit.A2.CVRectStarShift.shift_ideal_map
