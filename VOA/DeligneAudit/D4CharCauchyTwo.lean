import VOA.DeligneAudit.D4CharQTwoRow

/-!
The finite coefficient formula for C(2,N), and its reduction to a q-difference equation.
`GTCauchyTwoShift` remains an unproved target. This file does not assert C(2,N).
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open PowerSeries

noncomputable section

variable {R : Type*} [CommRing R]

/-- A two-row weight with N trailing zeroes. -/
def gtTwoRow (N a b : ℕ) : Fin (N + 2) → ℤ :=
  Fin.cons (a : ℤ) (Fin.cons (b : ℤ) (fun _ => 0))

theorem gtTwoRow_zero (N a : ℕ) : gtTwoRow N a 0 = gtOneRow (N + 1) a := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [gtTwoRow, gtOneRow]
  · refine Fin.cases ?_ (fun k => ?_) j <;> simp [gtTwoRow, gtOneRow]

/-- The x^r y^s coefficient of the two-row Cauchy sum, from `gtQ_two_expansion`. -/
def gtCauchyTwoCoeff (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N r s : ℕ) : R :=
  ∑ b ∈ Finset.range (min r s + 1),
    gtInvPoch q h (r - b : ℕ) * gtInvPoch q h (s - b : ℕ) * gtInvPoch q h b *
      gtEval q u (N + 2) (gtTwoRow N (r + s - b) b)

/-- C(2,N+2), as an equality of every coefficient in the two formal variables. -/
def GTCauchyTwo (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) : Prop :=
  ∀ r s, gtCauchyTwoCoeff q h u N r s =
    gtOneRowCoeff q h u (N + 2) r * gtOneRowCoeff q h u (N + 2) s

theorem gtCauchyTwoCoeff_symm (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N r s : ℕ) : gtCauchyTwoCoeff q h u N r s = gtCauchyTwoCoeff q h u N s r := by
  unfold gtCauchyTwoCoeff
  rw [min_comm r s, add_comm r s]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The initial value needed by q-difference uniqueness is already C(1,N+2). -/
theorem gtCauchyTwoCoeff_zero_right (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N r : ℕ) : gtCauchyTwoCoeff q h u N r 0 = gtOneRowCoeff q h u (N + 2) r := by
  simp [gtCauchyTwoCoeff, gtTwoRow_zero, gtOneRowCoeff, gtQ_oneRow_eq]

theorem gtCauchyTwoCoeff_zero_left (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N s : ℕ) : gtCauchyTwoCoeff q h u N 0 s = gtOneRowCoeff q h u (N + 2) s := by
  rw [gtCauchyTwoCoeff_symm, gtCauchyTwoCoeff_zero_right]

/-- The coefficient of x^r, viewed as a formal series in the last variable y. -/
def gtCauchyTwoSeries (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N r : ℕ) : PowerSeries R := PowerSeries.mk (gtCauchyTwoCoeff q h u N r)

/-- The remaining finite GT coefficient-comparison step of C(2,N+2). -/
def GTCauchyTwoShift (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ) : Prop :=
  ∀ r, rescale q (gtCauchyTwoSeries q h u N r) = gtCauchyTwoSeries q h u N r *
    ∏ i ∈ Finset.range (N + 2), (1 - PowerSeries.C (u i : R) * X)

/-- X, B and e-Pieri need only establish the stated shift; uniqueness supplies C(2,N+2). -/
theorem gtCauchy_two_of_shift (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N : ℕ) (hshift : GTCauchyTwoShift q h u N) : GTCauchyTwo q h u N := by
  intro r s
  let K := ∏ i ∈ Finset.range (N + 2), gtEulerInv q h (u i : R)
  let B := ∏ i ∈ Finset.range (N + 2), (1 - PowerSeries.C (u i : R) * X)
  let c := gtOneRowCoeff q h u (N + 2) r
  have hC : rescale q (PowerSeries.C c) = PowerSeries.C c := by
    ext n
    by_cases hn : n = 0 <;> simp [coeff_rescale, coeff_C, hn]
  have hK : rescale q (PowerSeries.C c * K) * 1 = (PowerSeries.C c * K) * B := by
    rw [map_mul, hC, mul_one]
    dsimp [K, B]
    rw [gtEulerInv_product_shift]
    ring
  have he : gtCauchyTwoSeries q h u N r = PowerSeries.C c * K := by
    apply qDifference_unique q (pochhammerUnits_qDifferenceUnits q h) 1 B
      (gtCauchyTwoSeries q h u N r) (PowerSeries.C c * K) (by simp)
    · simp [B]
    · simpa only [mul_one] using hshift r
    · exact hK
    · simp [gtCauchyTwoSeries, gtCauchyTwoCoeff_zero_right, c, K]
  have hc := congrArg (coeff s) he
  simpa only [gtCauchyTwoSeries, coeff_mk, coeff_C_mul,
    gtEulerInv_product_coeff, c, K] using hc

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtTwoRow_zero
#print axioms VOA.DeligneAudit.D4Char.gtCauchyTwoCoeff_symm
#print axioms VOA.DeligneAudit.D4Char.gtCauchyTwoCoeff_zero_right
#print axioms VOA.DeligneAudit.D4Char.gtCauchyTwoCoeff_zero_left
#print axioms VOA.DeligneAudit.D4Char.gtCauchy_two_of_shift
