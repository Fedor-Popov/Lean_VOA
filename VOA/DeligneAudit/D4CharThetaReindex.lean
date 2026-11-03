import VOA.DeligneAudit.D4CharMixedTheta

/-! Exhaustive reindexing of the equal-gap partition pairs left by theta orthogonality. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open DeligneCharacter PowerSeries

noncomputable section

/-- Equal gaps and even total size are exactly the triples a+b+c=n. -/
theorem rsEqualGap_sum {A : Type*} [AddCommMonoid A] (n : ℕ) (f : ℕ → ℕ → ℕ → A) :
    (∑ t ∈ Finset.antidiagonal (2 * n),
      ∑ p ∈ gtPartitionsTwo t.2, ∑ z ∈ gtPartitionsTwo t.1,
        if p.1 - p.2 = z.1 - z.2 then f (p.1 - p.2) p.2 z.2 else 0) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - a + 1), f a b (n - a - b) := by
  classical
  let s : Finset (Σ _ : ℕ × ℕ, (ℕ × ℕ) × (ℕ × ℕ)) :=
    ((Finset.antidiagonal (2 * n)).sigma fun t =>
      (gtPartitionsTwo t.2).product (gtPartitionsTwo t.1)).filter fun z =>
        z.2.1.1 - z.2.1.2 = z.2.2.1 - z.2.2.2
  let t : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.range (n + 1)).sigma fun a => Finset.range (n - a + 1)
  have hs : ∀ z, z ∈ s ↔
      z.1.1 + z.1.2 = 2 * n ∧
      (z.2.1.1 + z.2.1.2 = z.1.2 ∧ z.2.1.2 ≤ z.2.1.1) ∧
      (z.2.2.1 + z.2.2.2 = z.1.1 ∧ z.2.2.2 ≤ z.2.2.1) ∧
      z.2.1.1 - z.2.1.2 = z.2.2.1 - z.2.2.2 := by
    intro z
    simp only [s, Finset.mem_filter, Finset.mem_sigma, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_antidiagonal, mem_gtPartitionsTwo]
    tauto
  have ht : ∀ z, z ∈ t ↔ z.1 ≤ n ∧ z.2 ≤ n - z.1 := by
    intro z
    simp [t, Nat.lt_succ_iff]
  have hleft :
      (∑ t ∈ Finset.antidiagonal (2 * n),
        ∑ p ∈ gtPartitionsTwo t.2, ∑ z ∈ gtPartitionsTwo t.1,
          if p.1 - p.2 = z.1 - z.2 then f (p.1 - p.2) p.2 z.2 else 0) =
        ∑ z ∈ s, f (z.2.1.1 - z.2.1.2) z.2.1.2 z.2.2.2 := by
    simp only [s, Finset.sum_filter, Finset.sum_sigma, Finset.product_eq_sprod,
      Finset.sum_product]
  have hright :
      (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - a + 1), f a b (n - a - b)) =
        ∑ z ∈ t, f z.1 z.2 (n - z.1 - z.2) := by
    simp only [t, Finset.sum_sigma]
  rw [hleft, hright]
  refine Finset.sum_bij'
    (fun z _ => ⟨z.2.1.1 - z.2.1.2, z.2.1.2⟩)
    (fun z _ => ⟨(z.1 + 2 * (n - z.1 - z.2), z.1 + 2 * z.2),
      ((z.1 + z.2, z.2), (z.1 + (n - z.1 - z.2), n - z.1 - z.2))⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro z hz
    apply (ht _).mpr
    have hz := (hs z).mp hz
    dsimp
    constructor <;> omega
  · intro z hz
    apply (hs _).mpr
    have hz := (ht z).mp hz
    dsimp
    omega
  · rintro ⟨⟨m, k⟩, ⟨⟨a, b⟩, ⟨c, d⟩⟩⟩ hz
    have hz := (hs _).mp hz
    dsimp at hz ⊢
    have hd : n - (a - b) - b = d := by omega
    have ha : a - b + b = a := by omega
    have hc : a - b + d = c := by omega
    have hm : a - b + 2 * d = m := by omega
    have hk : a - b + 2 * b = k := by omega
    simp only [hd, ha, hc, hm, hk]
  · intro z _
    simp
  · intro z hz
    have hz := (hs z).mp hz
    dsimp
    congr 1
    omega

/-- The full three-index GL_4 theta formula, in every even degree. -/
theorem rsMixedKernel_moment_even (n : ℕ) :
    rsMoment (coeff (2 * n) rsMixedKernel) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n - a + 1),
        ((D4K.qpoch a)⁻¹ * (D4K.qpoch b)⁻¹ * (D4K.qpoch (n - a - b))⁻¹) •
          gtEval rsNome rsZAlphabet 4
            (gtMixedFourRow ((a + b : ℕ) : ℤ) b
              ((a + (n - a - b) : ℕ) : ℤ) ((n - a - b : ℕ) : ℤ)) := by
  simp only [Nat.cast_add]
  rw [rsMixedKernel_moment_coeff]
  have h := rsEqualGap_sum n (fun a b c =>
    ((D4K.qpoch a)⁻¹ * (D4K.qpoch b)⁻¹ * (D4K.qpoch c)⁻¹) •
      gtEval rsNome rsZAlphabet 4 (gtMixedFourRow (a + b) b (a + c) c))
  rw [← h]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro z hz
  have hp := (mem_gtPartitionsTwo _ _).mp hp
  have hz := (mem_gtPartitionsTwo _ _).mp hz
  by_cases he : p.1 - p.2 = z.1 - z.2
  · rw [if_pos he, if_pos he]
    rw [show ((p.1 - p.2 : ℕ) : ℤ) + p.2 = p.1 by omega,
      show ((p.1 - p.2 : ℕ) : ℤ) + z.2 = z.1 by omega]
  · rw [if_neg he, if_neg he]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsEqualGap_sum
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_moment_even
