import VOA.DeligneAudit.D4CharMixedKernel

/-!
Finite coefficients of the stable mixed-Cauchy sum at (m,n,N) = (2,2,5).
All four formal-variable degrees are arbitrary. The homogeneous shift below is a
named remaining target, not an asserted theorem.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The x_1^r x_2^s coefficient of Q_(r+s-b,b), from the proved Q expansion. -/
def gtTwoQCoefficient (q : R) (h : PochhammerUnits q) (r s b : ℕ) : R :=
  gtInvPoch q h (r - b : ℕ) * gtInvPoch q h (s - b : ℕ) * gtInvPoch q h b

theorem gtTwoQCoefficient_symm (q : R) (h : PochhammerUnits q) (r s b : ℕ) :
    gtTwoQCoefficient q h r s b = gtTwoQCoefficient q h s r b := by
  unfold gtTwoQCoefficient
  ring

/-- The complete x_1^r x_2^s y_1^t y_2^v coefficient on the GT side of MC_(2,2,5). -/
def gtMixedFiveCoeff (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v : ℕ) : R :=
  ∑ b ∈ Finset.range (min r s + 1), ∑ d ∈ Finset.range (min t v + 1),
    gtTwoQCoefficient q h r s b * gtTwoQCoefficient q h t v d *
      gtEval q u 5 (gtMixedFiveRow (r + s - b : ℕ) b (t + v - d : ℕ) d)

theorem gtMixedFiveCoeff_swap_x (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v : ℕ) :
    gtMixedFiveCoeff q h u r s t v = gtMixedFiveCoeff q h u s r t v := by
  unfold gtMixedFiveCoeff
  rw [min_comm r s, add_comm r s]
  simp only [gtTwoQCoefficient_symm q h r s]

theorem gtMixedFiveCoeff_swap_y (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v : ℕ) :
    gtMixedFiveCoeff q h u r s t v = gtMixedFiveCoeff q h u r s v t := by
  unfold gtMixedFiveCoeff
  rw [min_comm t v, add_comm t v]
  simp only [gtTwoQCoefficient_symm q h t v]

theorem gtMixedFiveRow_zero_head (a b : ℕ) :
    gtMixedFiveRow 0 0 a b = gtDual (gtTwoRow 3 a b) := by
  ext i
  fin_cases i <;> rfl

theorem gtMixedFiveRow_zero_tail (a b : ℕ) :
    gtMixedFiveRow a b 0 0 = gtTwoRow 3 a b := by
  ext i
  fin_cases i <;> rfl

/-- The negative-only base is precisely C(2,5) in the inverse u variables. -/
theorem gtMixedFiveCoeff_zero_x (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (t v : ℕ) :
    gtMixedFiveCoeff q h u 0 0 t v =
      gtOneRowCoeff q h (fun i => (u i)⁻¹) 5 t *
        gtOneRowCoeff q h (fun i => (u i)⁻¹) 5 v := by
  rw [← gtCauchy_two q h (fun i => (u i)⁻¹) 3 t v]
  simp only [gtMixedFiveCoeff, min_self, Nat.zero_add, Finset.range_one,
    Finset.sum_singleton, gtTwoQCoefficient, Nat.sub_zero, gtInvPoch_zero,
    one_mul, Nat.cast_zero, gtCauchyTwoCoeff]
  apply Finset.sum_congr rfl
  intro d _
  rw [gtMixedFiveRow_zero_head, gtEval_duality]

/-- The positive-only boundary is C(2,5) in u. -/
theorem gtMixedFiveCoeff_zero_y (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s : ℕ) :
    gtMixedFiveCoeff q h u r s 0 0 =
      gtOneRowCoeff q h u 5 r * gtOneRowCoeff q h u 5 s := by
  rw [← gtCauchy_two q h u 3 r s]
  simp only [gtMixedFiveCoeff, min_self, Nat.zero_add, Finset.range_one,
    Finset.sum_singleton, gtTwoQCoefficient, Nat.sub_zero, gtInvPoch_zero,
    mul_one, Nat.cast_zero, gtCauchyTwoCoeff]
  apply Finset.sum_congr rfl
  intro b _
  rw [gtMixedFiveRow_zero_tail]

/-- The coefficient equation F(qz)(1-z y_1)(1-z y_2) = F(z) prod_i(1-z u_i). -/
def GTMixedFiveRecurrence (q : R) (u : ℕ → Rˣ) (F : ℕ → ℕ → ℕ → ℕ → R) : Prop :=
  ∀ r s t v,
    q ^ s * F r s t v -
      (if 0 < s ∧ 0 < t then q ^ (s - 1) * F r (s - 1) (t - 1) v else 0) -
      (if 0 < s ∧ 0 < v then q ^ (s - 1) * F r (s - 1) t (v - 1) else 0) +
      (if 1 < s ∧ 0 < t ∧ 0 < v then
        q ^ (s - 2) * F r (s - 2) (t - 1) (v - 1) else 0) =
      ∑ j ∈ Finset.range (s + 1), (-1) ^ j * pieriElementary u 5 j * F r (s - j) t v

/-- Remaining homogeneous assembly of `gtMixedFive_local_normalized` and e-Pieri. -/
def GTMixedFiveShift (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) : Prop :=
  GTMixedFiveRecurrence q u (gtMixedFiveCoeff q h u)

/-- The zero second-degree equation already holds, for every array. -/
theorem gtMixedFiveRecurrence_zero (q : R) (u : ℕ → Rˣ)
    (F : ℕ → ℕ → ℕ → ℕ → R) (r t v : ℕ) :
    q ^ 0 * F r 0 t v =
      ∑ j ∈ Finset.range (0 + 1), (-1 : R) ^ j * pieriElementary u 5 j *
        F r (0 - j) t v := by
  simp [pieriElementary]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtTwoQCoefficient_symm
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveCoeff_swap_x
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveCoeff_swap_y
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveRow_zero_head
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveRow_zero_tail
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveCoeff_zero_x
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveCoeff_zero_y
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveRecurrence_zero
