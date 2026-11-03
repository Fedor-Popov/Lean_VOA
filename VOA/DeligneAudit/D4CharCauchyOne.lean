import VOA.DeligneAudit.D4CharOneRow

/-! C(1,N) and the one-row Euler generating function, for all N and all degrees. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtQ_oneRow_eq (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N k : ℕ) :
    gtQ q h u (N + 1) (gtOneRow N k) =
      gtInvPoch q h k * gtEval q u (N + 1) (gtOneRow N k) := by
  rw [gtQ, gtNormUnit_oneRow, gtInvPoch_nat]

theorem gtQ_oneRow_one (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (k : ℕ) :
    gtQ q h u 1 (gtOneRow 0 k) = gtInvPoch q h k * (u 0 : R) ^ k := by
  rw [gtQ_oneRow_eq, gtEval_one]
  simp [gtOneRow]

/-- Normalized one-row branching is the Euler convolution. -/
theorem gtQ_oneRow_branching (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N k : ℕ) :
    gtQ q h u (N + 2) (gtOneRow (N + 1) k) =
      ∑ j ∈ Finset.range (k + 1), gtQ q h u (N + 1) (gtOneRow N j) *
        (gtInvPoch q h (k - j : ℕ) * (u (N + 1) : R) ^ (k - j)) := by
  rw [gtQ_oneRow_eq, gtEval_oneRow_branching, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ k := by simpa using hj
  have hn := gtGaussian_normalized q h k (k - j) (Nat.sub_le k j)
  rw [Nat.sub_sub_self hle] at hn
  simp only [← gtInvPoch_nat] at hn
  rw [gtQ_oneRow_eq]
  calc
    _ = (VOA.DeligneGaussian.qbinom q k (k - j) * gtInvPoch q h k) *
        ((u (N + 1) : R) ^ (k - j) * gtEval q u (N + 1) (gtOneRow N j)) := by ring
    _ = _ := by rw [hn]; ring

/-- The normalized one-row coefficient, including zero variables. -/
def gtOneRowCoeff (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) : ℕ → ℕ → R
  | 0, k => if k = 0 then 1 else 0
  | N + 1, k => gtQ q h u (N + 1) (gtOneRow N k)

/-- The C(1,N) coefficient identity, with no bound on N or the row length. -/
theorem gtEulerInv_product_coeff (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N k : ℕ) :
    coeff k (∏ i ∈ Finset.range N, gtEulerInv q h (u i : R)) =
      gtOneRowCoeff q h u N k := by
  induction N generalizing k with
  | zero => simp [gtOneRowCoeff, coeff_one]
  | succ N ih =>
      cases N with
      | zero => simp [gtOneRowCoeff, gtQ_oneRow_one, gtEulerInv]
      | succ N =>
          rw [Finset.prod_range_succ, coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          simp_rw [ih]
          simp only [gtOneRowCoeff, gtEulerInv, coeff_mk]
          exact (gtQ_oneRow_branching q h u N k).symm

/-- Lemma 3.2(e), equivalently ordinary Cauchy C(1,N). -/
theorem gtCauchy_one (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    (∏ i ∈ Finset.range N, gtEulerInv q h (u i : R)) =
      PowerSeries.mk (gtOneRowCoeff q h u N) := by
  ext k
  rw [gtEulerInv_product_coeff, coeff_mk]

/-- C(1,N) displayed with the unnormalized GT polynomial, for every positive N. -/
theorem gtCauchy_one_GT (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) :
    (∏ i ∈ Finset.range (N + 1), gtEulerInv q h (u i : R)) =
      PowerSeries.mk (fun k => gtInvPoch q h k *
        gtEval q u (N + 1) (gtOneRow N k)) := by
  rw [gtCauchy_one]
  congr 1
  funext k
  exact gtQ_oneRow_eq q h u N k

/-- The empty alphabet base of the ordinary Cauchy induction. -/
theorem gtCauchy_one_empty (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    PowerSeries.mk (gtOneRowCoeff q h u 0) = 1 := by
  rw [← gtCauchy_one]
  simp

/-- Lemma gP at m = 1: the only possible upper row has length r + k. -/
theorem gtGP_one (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (r k : ℕ) :
    VOA.DeligneGaussian.qbinom q (r + k) k * gtQ q h u 1 (gtOneRow 0 (r + k)) =
      gtQ q h u 1 (gtOneRow 0 k) * gtQ q h u 1 (gtOneRow 0 r) := by
  have hn := gtGaussian_normalized q h (r + k) k (Nat.le_add_left k r)
  simp only [Nat.add_sub_cancel_right, ← gtInvPoch_nat] at hn
  simp only [gtQ_oneRow_one, pow_add]
  calc
    _ = (VOA.DeligneGaussian.qbinom q (r + k) k * gtInvPoch q h (r + k : ℕ)) *
        ((u 0 : R) ^ r * (u 0 : R) ^ k) := by ring
    _ = _ := by rw [hn]; ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtQ_oneRow_eq
#print axioms VOA.DeligneAudit.D4Char.gtQ_oneRow_one
#print axioms VOA.DeligneAudit.D4Char.gtQ_oneRow_branching
#print axioms VOA.DeligneAudit.D4Char.gtEulerInv_product_coeff
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_one
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_one_GT
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_one_empty
#print axioms VOA.DeligneAudit.D4Char.gtGP_one
