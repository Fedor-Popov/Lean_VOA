import VOA.DeligneAudit.D4CharGPTwoCoeff

/-! Lemma gP for two variables, for every partition and every degree. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Rank-two gP, with the upper rows parametrized by their second-part increment. -/
theorem gtGP_two (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (c d k : ℕ) (hd : d ≤ c) :
    (∑ b ∈ Finset.range (min k (c - d) + 1),
      gtPsi q ![((c + k - b : ℕ) : ℤ), ((d + b : ℕ) : ℤ), 0]
        ![(c : ℤ), (d : ℤ)] *
      gtQ q h u 2 ![((c + k - b : ℕ) : ℤ), ((d + b : ℕ) : ℤ)]) =
    gtOneRowCoeff q h u 2 k * gtQ q h u 2 ![(c : ℤ), (d : ℤ)] := by
  have hc := gtCauchy_two q h u 0 k (c - d)
  change gtCauchyTwoCoeff q h u 0 k (c - d) =
    gtOneRowCoeff q h u 2 k * gtOneRowCoeff q h u 2 (c - d) at hc
  rw [gtQ_two_oneRow q h u c d hd]
  calc
    _ = gtInvPoch q h d * ((u 0 : R) * (u 1 : R)) ^ d *
        gtCauchyTwoCoeff q h u 0 k (c - d) := by
      rw [gtCauchyTwoCoeff, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hb : b ≤ min k (c - d) := by simpa using hb
      rw [gtQ, ← mul_assoc, gtGP_two_normalized q h c d k b hd hb]
      have hs : c + k - b = k + (c - d) - b + d := by omega
      have hr : gtTwoRow 0 (k + (c - d) - b) b =
          ![((k + (c - d) - b : ℕ) : ℤ), (b : ℤ)] := by
        ext i
        fin_cases i <;> rfl
      rw [hr, hs, add_comm d b, gtEval_two_shift]
      ring
    _ = _ := by rw [hc]; ring

/-- Every upper partition in the paper's rank-two gP sum, with no extra support cutoff. -/
def gtGPUppersTwo (c d k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.antidiagonal (c + d + k)).filter fun p =>
    (![(c : ℤ), (d : ℤ)] : Fin 2 → ℤ) ∈
      gtRows ![(p.1 : ℤ), (p.2 : ℤ), 0]

theorem mem_gtGPUppersTwo (c d k : ℕ) (p : ℕ × ℕ) :
    p ∈ gtGPUppersTwo c d k ↔ p.1 + p.2 = c + d + k ∧
      d ≤ p.2 ∧ p.2 ≤ c ∧ c ≤ p.1 := by
  simp only [gtGPUppersTwo, Finset.mem_filter, Finset.mem_antidiagonal, mem_gtRows]
  constructor
  · rintro ⟨hs, hi⟩
    have h₀ := hi 0
    have h₁ := hi 1
    change (p.2 : ℤ) ≤ c ∧ (c : ℤ) ≤ p.1 at h₀
    change (0 : ℤ) ≤ d ∧ (d : ℤ) ≤ p.2 at h₁
    exact ⟨hs, by omega, by omega, by omega⟩
  · rintro ⟨hs, h₁, h₂, h₃⟩
    refine ⟨hs, fun i => ?_⟩
    fin_cases i
    · change (p.2 : ℤ) ≤ c ∧ (c : ℤ) ≤ p.1
      omega
    · change (0 : ℤ) ≤ d ∧ (d : ℤ) ≤ p.2
      omega

/-- The finite reindexing includes every interlacing upper partition exactly once. -/
theorem sum_gtGPUppersTwo {A : Type*} [AddCommMonoid A]
    (c d k : ℕ) (hd : d ≤ c) (f : ℕ × ℕ → A) :
    (∑ p ∈ gtGPUppersTwo c d k, f p) =
      ∑ b ∈ Finset.range (min k (c - d) + 1), f (c + k - b, d + b) := by
  classical
  refine Finset.sum_bij' (fun p _ => p.2 - d) (fun b _ => (c + k - b, d + b))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hp := (mem_gtGPUppersTwo c d k p).mp hp
    simp only [Finset.mem_range]
    omega
  · intro b hb
    have hb : b ≤ min k (c - d) := by simpa using hb
    apply (mem_gtGPUppersTwo c d k _).mpr
    dsimp
    omega
  · intro p hp
    have hp := (mem_gtGPUppersTwo c d k p).mp hp
    apply Prod.ext <;> dsimp <;> omega
  · intro b _
    dsimp
    omega
  · intro p hp
    have hp := (mem_gtGPUppersTwo c d k p).mp hp
    congr 1
    apply Prod.ext <;> dsimp <;> omega

/-- Lemma gP in precisely the GT branching notation used by the mixed-Cauchy down-step. -/
theorem gtGP_two_branching (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (c d k : ℕ) (hd : d ≤ c) :
    (∑ p ∈ gtGPUppersTwo c d k,
      gtPsi q ![(p.1 : ℤ), (p.2 : ℤ), 0] ![(c : ℤ), (d : ℤ)] *
        gtQ q h u 2 ![(p.1 : ℤ), (p.2 : ℤ)]) =
      gtOneRowCoeff q h u 2 k * gtQ q h u 2 ![(c : ℤ), (d : ℤ)] := by
  rw [sum_gtGPUppersTwo c d k hd]
  exact gtGP_two q h u c d k hd

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtGP_two
#print axioms VOA.DeligneAudit.D4Char.mem_gtGPUppersTwo
#print axioms VOA.DeligneAudit.D4Char.sum_gtGPUppersTwo
#print axioms VOA.DeligneAudit.D4Char.gtGP_two_branching
