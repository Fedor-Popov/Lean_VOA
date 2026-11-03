import VOA.DeligneAudit.D4CharDownGP

/-! The GT side of the GL_5 to GL_4 constant-term down-step, in all bidegrees. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- A coefficient of the mixed GL_4 sum, homogeneous in each two-variable alphabet. -/
def gtMixedFourHomCoeff (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (n m : ℕ) (a : ℕ →₀ ℤ) : R :=
  ∑ p ∈ gtPartitionsTwo n, ∑ r ∈ gtPartitionsTwo m,
    gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
      gtQ q h y 2 ![(r.1 : ℤ), (r.2 : ℤ)] *
        gtPoly q 4 (gtMixedFourRow p.1 p.2 r.1 r.2) a

/-- The corresponding homogeneous GL_5 coefficient, before extracting its last variable. -/
def gtMixedFiveHomCoeff (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (n m : ℕ) (a : ℕ →₀ ℤ) : R :=
  ∑ p ∈ gtPartitionsTwo n, ∑ r ∈ gtPartitionsTwo m,
    gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
      gtQ q h y 2 ![(r.1 : ℤ), (r.2 : ℤ)] *
        gtPoly q 5 (gtMixedFiveRow p.1 p.2 r.1 r.2) a

/-- After taking the fifth-variable constant term, gP in both alphabets gives Gamma. -/
theorem gtMixedFive_ct_regroup (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (n m : ℕ) (a : ℕ →₀ ℤ) (ha : a 4 = 0) :
    gtMixedFiveHomCoeff q h x y n m a =
      ∑ k ∈ Finset.range (min n m + 1),
        (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 k) *
          gtMixedFourHomCoeff q h x y (n - k) (m - k) a := by
  unfold gtMixedFiveHomCoeff gtMixedFourHomCoeff
  rw [← gtDownTwo_transform_diagonal]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  rw [gtMixedFive_last_zero_coeff q _ _ _ _ a ha]
  simp_rw [sum_gtRows_three_nat]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  have hp := (mem_gtPartitionsTwo n p).mp hp
  have hr := (mem_gtPartitionsTwo m r).mp hr
  have he : (p.1 : ℤ) + p.2 - ∑ i, (![(c.1 : ℤ), (c.2 : ℤ)] : Fin 2 → ℤ) i =
      (r.1 : ℤ) + r.2 - ∑ i, (![(d.1 : ℤ), (d.2 : ℤ)] : Fin 2 → ℤ) i ↔
        n + (d.1 + d.2) = m + (c.1 + c.2) := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  simp only [he, mul_ite, mul_zero, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- No spurious monomial in the deleted variable occurs on the GL_4 side. -/
theorem gtMixedFourHomCoeff_last_ne_zero (q : R) (h : PochhammerUnits q)
    (x y : ℕ → Rˣ) (n m : ℕ) (a : ℕ →₀ ℤ) (ha : a 4 ≠ 0) :
    gtMixedFourHomCoeff q h x y n m a = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro r _
  have he : gtPoly q 4 (gtMixedFourRow p.1 p.2 r.1 r.2) a = 0 := by
    by_contra hn
    exact ha ((gtPoly_support_bounds q 4 _ a hn).1 4 le_rfl)
  rw [he, mul_zero]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_ct_regroup
#print axioms VOA.DeligneAudit.D4Char.gtMixedFourHomCoeff_last_ne_zero
