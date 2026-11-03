import VOA.DeligneAudit.D4CharDownReindex

/-! Applying rank-two gP after reversing all branches of a homogeneous slice. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- One alphabet of the down-step, for any function of the lower partition. -/
theorem gtDownTwo_transform (q : R) (h : PochhammerUnits q) (x : ℕ → Rˣ)
    (n : ℕ) (f : (ℕ × ℕ) → R) :
    (∑ p ∈ gtPartitionsTwo n, gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
      ∑ c ∈ gtDownRowsTwo p.1 p.2,
        gtPsi q ![(p.1 : ℤ), (p.2 : ℤ), 0] ![(c.1 : ℤ), (c.2 : ℤ)] * f c) =
      ∑ k ∈ Finset.range (n + 1), gtOneRowCoeff q h x 2 k *
        ∑ c ∈ gtPartitionsTwo (n - k), gtQ q h x 2 ![(c.1 : ℤ), (c.2 : ℤ)] *
          f c := by
  simp_rw [Finset.mul_sum]
  rw [sum_gtDownRowsTwo_reverse]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c hc
  have hc := (mem_gtPartitionsTwo (n - k) c).mp hc
  calc
    _ = (∑ p ∈ gtGPUppersTwo c.1 c.2 k,
        gtPsi q ![(p.1 : ℤ), (p.2 : ℤ), 0] ![(c.1 : ℤ), (c.2 : ℤ)] *
          gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)]) * f c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [gtGP_two_branching q h x c.1 c.2 k hc.2]; ring

/-- Both alphabets, before restricting to equal positive and negative gains. -/
theorem gtDownTwo_transform_pair (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (n m : ℕ) (f : (ℕ × ℕ) → (ℕ × ℕ) → R) :
    (∑ p ∈ gtPartitionsTwo n, ∑ r ∈ gtPartitionsTwo m,
      gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        gtQ q h y 2 ![(r.1 : ℤ), (r.2 : ℤ)] *
        ∑ c ∈ gtDownRowsTwo p.1 p.2, ∑ d ∈ gtDownRowsTwo r.1 r.2,
          (gtPsi q ![(p.1 : ℤ), (p.2 : ℤ), 0] ![(c.1 : ℤ), (c.2 : ℤ)] *
            gtPsi q ![(r.1 : ℤ), (r.2 : ℤ), 0] ![(d.1 : ℤ), (d.2 : ℤ)]) * f c d) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 l) *
          ∑ c ∈ gtPartitionsTwo (n - k), ∑ d ∈ gtPartitionsTwo (m - l),
            gtQ q h x 2 ![(c.1 : ℤ), (c.2 : ℤ)] *
              gtQ q h y 2 ![(d.1 : ℤ), (d.2 : ℤ)] * f c d := by
  calc
    _ = ∑ p ∈ gtPartitionsTwo n, gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        ∑ c ∈ gtDownRowsTwo p.1 p.2,
          gtPsi q ![(p.1 : ℤ), (p.2 : ℤ), 0] ![(c.1 : ℤ), (c.2 : ℤ)] *
            (∑ r ∈ gtPartitionsTwo m, gtQ q h y 2 ![(r.1 : ℤ), (r.2 : ℤ)] *
              ∑ d ∈ gtDownRowsTwo r.1 r.2,
                gtPsi q ![(r.1 : ℤ), (r.2 : ℤ), 0] ![(d.1 : ℤ), (d.2 : ℤ)] *
                  f c d) := by
      apply Finset.sum_congr rfl
      intro p _
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = _ := by
      rw [gtDownTwo_transform]
      simp_rw [gtDownTwo_transform, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring

/-- The constant term imposes exactly one common gain, with the full range retained. -/
theorem gtDownTwo_transform_diagonal (q : R) (h : PochhammerUnits q)
    (x y : ℕ → Rˣ) (n m : ℕ) (f : (ℕ × ℕ) → (ℕ × ℕ) → R) :
    (∑ p ∈ gtPartitionsTwo n, ∑ r ∈ gtPartitionsTwo m,
      gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        gtQ q h y 2 ![(r.1 : ℤ), (r.2 : ℤ)] *
        ∑ c ∈ gtDownRowsTwo p.1 p.2, ∑ d ∈ gtDownRowsTwo r.1 r.2,
          (gtPsi q ![(p.1 : ℤ), (p.2 : ℤ), 0] ![(c.1 : ℤ), (c.2 : ℤ)] *
            gtPsi q ![(r.1 : ℤ), (r.2 : ℤ), 0] ![(d.1 : ℤ), (d.2 : ℤ)]) *
              (if n + (d.1 + d.2) = m + (c.1 + c.2) then f c d else 0)) =
      ∑ k ∈ Finset.range (min n m + 1),
        (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 k) *
          ∑ c ∈ gtPartitionsTwo (n - k), ∑ d ∈ gtPartitionsTwo (m - k),
            gtQ q h x 2 ![(c.1 : ℤ), (c.2 : ℤ)] *
              gtQ q h y 2 ![(d.1 : ℤ), (d.2 : ℤ)] * f c d := by
  classical
  rw [gtDownTwo_transform_pair]
  have he : ∀ k ∈ Finset.range (n + 1), ∀ l ∈ Finset.range (m + 1),
      (∑ c ∈ gtPartitionsTwo (n - k), ∑ d ∈ gtPartitionsTwo (m - l),
        gtQ q h x 2 ![(c.1 : ℤ), (c.2 : ℤ)] *
          gtQ q h y 2 ![(d.1 : ℤ), (d.2 : ℤ)] *
            (if n + (d.1 + d.2) = m + (c.1 + c.2) then f c d else 0)) =
      if k = l then
        ∑ c ∈ gtPartitionsTwo (n - k), ∑ d ∈ gtPartitionsTwo (m - l),
          gtQ q h x 2 ![(c.1 : ℤ), (c.2 : ℤ)] *
            gtQ q h y 2 ![(d.1 : ℤ), (d.2 : ℤ)] * f c d else 0 := by
    intro k hk l hl
    simp only [Finset.mem_range] at hk hl
    by_cases hkl : k = l
    · rw [if_pos hkl]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      have hc := (mem_gtPartitionsTwo _ c).mp hc
      have hd := (mem_gtPartitionsTwo _ d).mp hd
      rw [if_pos (by omega)]
    · rw [if_neg hkl]
      apply Finset.sum_eq_zero
      intro c hc
      apply Finset.sum_eq_zero
      intro d hd
      have hc := (mem_gtPartitionsTwo _ c).mp hc
      have hd := (mem_gtPartitionsTwo _ d).mp hd
      rw [if_neg (by omega), mul_zero]
  calc
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (m + 1),
        if k = l then (gtOneRowCoeff q h x 2 k * gtOneRowCoeff q h y 2 l) *
          ∑ c ∈ gtPartitionsTwo (n - k), ∑ d ∈ gtPartitionsTwo (m - l),
            gtQ q h x 2 ![(c.1 : ℤ), (c.2 : ℤ)] *
              gtQ q h y 2 ![(d.1 : ℤ), (d.2 : ℤ)] * f c d else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [he k hk l hl, mul_ite, mul_zero]
    _ = _ := by
      simp only [Finset.sum_ite_eq, Finset.mem_range]
      rw [← Finset.sum_subset (Finset.range_mono
        (show min n m + 1 ≤ n + 1 by omega))]
      · apply Finset.sum_congr rfl
        intro k hk
        have hk := Finset.mem_range.mp hk
        rw [if_pos (by omega)]
      · intro k hk hn
        have hk := Finset.mem_range.mp hk
        have hn : ¬ k < min n m + 1 := by simpa using hn
        rw [if_neg (by omega)]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtDownTwo_transform
#print axioms VOA.DeligneAudit.D4Char.gtDownTwo_transform_pair
#print axioms VOA.DeligneAudit.D4Char.gtDownTwo_transform_diagonal
