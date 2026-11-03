import VOA.DeligneAudit.DeligneFusionCVRectIntegrationIdeal

/-!
# The color-shift ideal map in the commutative upper recursion

Changing a chosen two-color site to a one-color site shifts the selected
current modes, equivalently removes its distinguished zero-mode term
from the reversed current. The proof below uses the actual mixed
coefficient ideal and the binomial expansion; it does not assume a
fusion identification or the desired dimension bound.
-/

namespace VOA.DeligneAudit.A2.CVRectShift

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectIntegrationSeries
open VOA.DeligneAudit.A2.CVRectIntegrationIdeal

noncomputable section

theorem excess_le_sub_add (ks : List ℕ) (t u : ℕ) :
    excess ks t ≤ excess ks (t - u) + ks.length * u := by
  induction ks with
  | nil => simp [excess]
  | cons k ks ih =>
      simp only [excess, List.map_cons, List.sum_cons, List.length_cons] at *
      have hk : t - k ≤ t - u - k + u := by omega
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The selected site now sees only the unshifted color. -/
def shiftedOrder (ks inactive : List ℕ) (K a b : ℕ) : ℕ :=
  excess inactive b + (b - K) + excess ks (a + b)

theorem shiftedOrder_le (ks inactive : List ℕ) (K a b m : ℕ) (hm : m ≤ a) :
    shiftedOrder ks inactive K a b ≤
      mixedOrder ks inactive K m b + ks.length * (a - m) := by
  have he := excess_le_sub_add ks (a + b) (a - m)
  rw [show a + b - (a - m) = m + b by omega] at he
  dsimp only [shiftedOrder, mixedOrder, siteOrder]
  omega

section Series

variable {R : Type*} [CommRing R]

/-- Removing a degree-`h` zero-mode term preserves the shifted mixed
orders. This is the binomial relation transfer, in the upper-bound direction. -/
theorem shift_order (S T V : PowerSeries R) (ks inactive : List ℕ) (K : ℕ)
    (hV : PowerSeries.X ^ ks.length ∣ V)
    (hsource : ∀ a b, PowerSeries.X ^ mixedOrder ks inactive K a b ∣ S ^ a * T ^ b) :
    ∀ a b, PowerSeries.X ^ shiftedOrder ks inactive K a b ∣ (S - V) ^ a * T ^ b := by
  intro a b
  rw [sub_eq_add_neg, (Commute.all S (-V)).add_pow, Finset.sum_mul]
  apply Finset.dvd_sum
  intro m hm
  have hm' : m ≤ a := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm
  have hvpow : PowerSeries.X ^ (ks.length * (a - m)) ∣ (-V) ^ (a - m) := by
    obtain ⟨W, hW⟩ := hV
    have hv : -V = PowerSeries.X ^ ks.length * (-W) := by rw [hW]; ring
    refine ⟨(-W) ^ (a - m), ?_⟩
    rw [hv, mul_pow, pow_mul]
  have hprod : PowerSeries.X ^
      (mixedOrder ks inactive K m b + ks.length * (a - m)) ∣
        (S ^ m * T ^ b) * (-V) ^ (a - m) := by
    rw [pow_add]
    exact mul_dvd_mul (hsource m b) hvpow
  have hle := shiftedOrder_le ks inactive K a b m hm'
  have hdiv := (pow_dvd_pow PowerSeries.X hle).trans hprod
  convert dvd_mul_of_dvd_left hdiv (a.choose m : PowerSeries R) using 1; ring

/-- Source defining coefficients vanish in the actual coefficient-ideal quotient. -/
theorem source_order_quotient (S T : PowerSeries R) (μ : ℕ → ℕ → ℕ) (a b : ℕ) :
    PowerSeries.X ^ μ a b ∣
      (PowerSeries.map (Ideal.Quotient.mk (coefficientIdeal S T μ)) S) ^ a *
        (PowerSeries.map (Ideal.Quotient.mk (coefficientIdeal S T μ)) T) ^ b := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro j hj
  rw [← map_pow, ← map_pow, ← map_mul, PowerSeries.coeff_map]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨a, b, j, hj, rfl⟩

end Series

section Polynomial

variable {A : Type*} [CommRing A]

/-- Each shifted defining coefficient maps into the actual source ideal. -/
theorem shift_coefficient_mem (f g : PowerSeries A) (ks inactive : List ℕ) (K a b j : ℕ)
    (hj : j < shiftedOrder ks inactive K a b) :
    Polynomial.C (PowerSeries.coeff j (f ^ a * g ^ b)) ∈
      coefficientIdeal (chosenCurrent ks.length f) (constantCurrent g)
        (mixedOrder ks inactive K) := by
  let S := chosenCurrent ks.length f
  let T := constantCurrent g
  let V : PowerSeries (Polynomial A) := PowerSeries.C Polynomial.X * PowerSeries.X ^ ks.length
  let J := coefficientIdeal S T (mixedOrder ks inactive K)
  let q := Ideal.Quotient.mk J
  let Q := PowerSeries.map q
  have hv : PowerSeries.X ^ ks.length ∣ Q V := by
    refine ⟨Q (PowerSeries.C Polynomial.X), ?_⟩
    simp only [V, map_mul, map_pow, Q, PowerSeries.map_X]
    ring
  have hs : ∀ a b, PowerSeries.X ^ mixedOrder ks inactive K a b ∣ Q S ^ a * Q T ^ b :=
    source_order_quotient S T (mixedOrder ks inactive K)
  have hz := PowerSeries.X_pow_dvd_iff.mp
    (shift_order (Q S) (Q T) (Q V) ks inactive K hv hs a b) j hj
  have heq : Q S - Q V = Q (constantCurrent f) := by
    rw [← map_sub]
    congr 1
    dsimp only [S, V, chosenCurrent]
    abel
  rw [heq, ← map_pow, ← map_pow, ← map_mul, PowerSeries.coeff_map] at hz
  have hc : PowerSeries.coeff j (constantCurrent f ^ a * constantCurrent g ^ b) =
      Polynomial.C (PowerSeries.coeff j (f ^ a * g ^ b)) := by
    unfold constantCurrent
    rw [← map_pow, ← map_pow, ← map_mul, PowerSeries.coeff_map]
  change q (PowerSeries.coeff j (constantCurrent f ^ a * constantCurrent g ^ b)) = 0 at hz
  rw [hc] at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

/-- The actual color-shift homomorphism preserves the entire coefficient
ideal. The chosen site's maximality is not required for this half. -/
theorem shift_ideal_map (f g : PowerSeries A) (ks inactive : List ℕ) (K : ℕ) :
    Ideal.map Polynomial.C (coefficientIdeal f g (shiftedOrder ks inactive K)) ≤
      coefficientIdeal (chosenCurrent ks.length f) (constantCurrent g)
        (mixedOrder ks inactive K) := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro P ⟨a, b, j, hj, rfl⟩
  exact shift_coefficient_mem f g ks inactive K a b j hj

end Polynomial

end

end VOA.DeligneAudit.A2.CVRectShift

#print axioms VOA.DeligneAudit.A2.CVRectShift.shift_order
#print axioms VOA.DeligneAudit.A2.CVRectShift.source_order_quotient
#print axioms VOA.DeligneAudit.A2.CVRectShift.shift_ideal_map
