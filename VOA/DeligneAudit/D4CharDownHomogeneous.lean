import VOA.DeligneAudit.D4CharDownKernelCT

/-! Converting homogeneous partition sums to the existing four-degree coefficient notation. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Interchanging the fixed-size partition and its first variable degree. -/
theorem sum_gtPartitionsTwo_expansion {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : (ℕ × ℕ) → ℕ → A) :
    (∑ p ∈ gtPartitionsTwo n, ∑ r ∈ Finset.Icc p.2 p.1, f p r) =
      ∑ r ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (min r (n - r) + 1),
        f (n - b, b) r := by
  classical
  simp_rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun z _ => ⟨z.2, z.1.2⟩)
    (fun z _ => ⟨(n - z.2, z.2), z.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rcases Finset.mem_sigma.mp hz with ⟨hp, hr⟩
    have hp := (mem_gtPartitionsTwo n z.1).mp hp
    have hr := Finset.mem_Icc.mp hr
    apply Finset.mem_sigma.mpr
    simp only [Finset.mem_range]
    omega
  · intro z hz
    rcases Finset.mem_sigma.mp hz with ⟨hr, hb⟩
    simp only [Finset.mem_range] at hr hb
    apply Finset.mem_sigma.mpr
    simp only [mem_gtPartitionsTwo, Finset.mem_Icc]
    omega
  · intro z hz
    rcases Finset.mem_sigma.mp hz with ⟨hp, _⟩
    have hp := (mem_gtPartitionsTwo n z.1).mp hp
    have he : n - z.1.2 = z.1.1 := by omega
    dsimp
    simp only [he]
  · intro z _
    rfl
  · intro z hz
    rcases Finset.mem_sigma.mp hz with ⟨hp, _⟩
    have hp := (mem_gtPartitionsTwo n z.1).mp hp
    have he : n - z.1.2 = z.1.1 := by omega
    dsimp
    simp only [he]

/-- Evaluate one homogeneous alphabet while retaining every coefficient used by MC. -/
theorem gtTwoQ_homogeneous_sum (q : R) (h : PochhammerUnits q) (x : ℕ → Rˣ)
    (n : ℕ) (f : (ℕ × ℕ) → R) :
    (∑ p ∈ gtPartitionsTwo n, gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] * f p) =
      ∑ r ∈ Finset.range (n + 1), (x 0 : R) ^ r * (x 1 : R) ^ (n - r) *
        ∑ b ∈ Finset.range (min r (n - r) + 1),
          gtTwoQCoefficient q h r (n - r) b * f (n - b, b) := by
  simp_rw [gtQ_two_expansion, Finset.sum_mul]
  rw [sum_gtPartitionsTwo_expansion]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hr := Finset.mem_range.mp hr
  have hb := Finset.mem_range.mp hb
  have he : n - b + b - r = n - r := by omega
  have hf : n - b - r = n - r - b := by omega
  rw [he, hf]
  unfold gtTwoQCoefficient
  ring

/-- Both homogeneous alphabets, with an arbitrary mixed-row payload. -/
theorem gtTwoQ_homogeneous_pair (q : R) (h : PochhammerUnits q) (x y : ℕ → Rˣ)
    (n m : ℕ) (f : (ℕ × ℕ) → (ℕ × ℕ) → R) :
    (∑ p ∈ gtPartitionsTwo n, ∑ z ∈ gtPartitionsTwo m,
      gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        gtQ q h y 2 ![(z.1 : ℤ), (z.2 : ℤ)] * f p z) =
      ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (m + 1),
        ((x 0 : R) ^ r * (x 1 : R) ^ (n - r) *
          ((y 0 : R) ^ t * (y 1 : R) ^ (m - t))) *
          ∑ b ∈ Finset.range (min r (n - r) + 1),
            ∑ d ∈ Finset.range (min t (m - t) + 1),
              gtTwoQCoefficient q h r (n - r) b *
                gtTwoQCoefficient q h t (m - t) d * f (n - b, b) (m - d, d) := by
  calc
    _ = ∑ p ∈ gtPartitionsTwo n, gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        ∑ z ∈ gtPartitionsTwo m,
          gtQ q h y 2 ![(z.1 : ℤ), (z.2 : ℤ)] * f p z := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by
      rw [gtTwoQ_homogeneous_sum]
      simp_rw [gtTwoQ_homogeneous_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      ring

/-- The stable MC theorem, as a sum over partitions of arbitrary fixed sizes. -/
theorem gtMixed_five_homogeneous (q : R) (h : PochhammerUnits q)
    (x y u : ℕ → Rˣ) (n m : ℕ) :
    (∑ p ∈ gtPartitionsTwo n, ∑ z ∈ gtPartitionsTwo m,
      gtQ q h x 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
        gtQ q h y 2 ![(z.1 : ℤ), (z.2 : ℤ)] *
          gtEval q u 5 (gtMixedFiveRow p.1 p.2 z.1 z.2)) =
      ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (m + 1),
        ((x 0 : R) ^ r * (x 1 : R) ^ (n - r) *
          ((y 0 : R) ^ t * (y 1 : R) ^ (m - t))) *
            gtMixedFiveKernelCoeff q h u r (n - r) t (m - t) := by
  rw [gtTwoQ_homogeneous_pair]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  have hr : r ≤ n := by simpa using hr
  have ht : t ≤ m := by simpa using ht
  rw [← gtMixed_five]
  simp only [gtMixedFiveCoeff, Nat.add_sub_of_le hr, Nat.add_sub_of_le ht]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.sum_gtPartitionsTwo_expansion
#print axioms VOA.DeligneAudit.D4Char.gtTwoQ_homogeneous_sum
#print axioms VOA.DeligneAudit.D4Char.gtTwoQ_homogeneous_pair
#print axioms VOA.DeligneAudit.D4Char.gtMixed_five_homogeneous
