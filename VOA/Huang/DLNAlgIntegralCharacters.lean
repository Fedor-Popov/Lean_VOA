import VOA.Huang.DLNAlgField

/-!
# An independent arithmetic boundary for character congruence

The named input is the integral, weight-zero q-series consequence of
Calegari--Dimitrov--Tang, arXiv:2109.09040, Theorem 7.3.3, Corollary 7.3.4,
and the congruence level theorem (Wohlfahrt) on the span of the functions.
It is not proved here. It concerns functions rather than a representation
on potentially dependent module labels. In particular, it does not give
the genuine kernel of Zhu's full trace representation.
-/

noncomputable section

namespace VOA.Huang.DLNAlg

open Complex VOA VOA.Classification.COne VOA.Huang.CongruenceGaloisSplit

/-- A true arithmetic theorem left as an explicit input. Convergent integral
q-series with rational exponents and finite S-stable span are invariant under
Gamma(N) whenever N clears all exponents. The exact level uses the congruence
level theorem in addition to CDT, not just finite image or a T-period.
S may be singular on the displayed labels; pass to their actual function span.
Zero functions and dependent labels do not cause a problem. -/
def IntegralQSeriesCongruenceInput : Prop :=
  ∀ (ι : Type) [Fintype ι] (r : ι → ℚ) (c : ι → ℕ → ℤ)
    (f : ι → ℂ → ℂ) (S : Matrix ι ι ℂ),
    (∀ a τ, 0 < im τ → HasSum (fun n : ℕ => (c a n : ℂ) *
      exp (2 * Real.pi * I * ((r a : ℂ) + n) * τ)) (f a τ)) →
    (∀ a τ, 0 < im τ → f a (-1 / τ) = ∑ b, S a b * f b τ) →
    ∀ N : ℕ, 0 < N → (∀ a, ∃ k : ℤ, (N : ℂ) * (r a : ℂ) = k) →
    ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ a τ, 0 < im τ →
      f a (mobius γ τ) = f a τ

universe u

/-- No Verlinde, charge-conjugation or PBW input is used in this implication.
The unproved premise is the arithmetic q-series theorem above. -/
theorem dlnCongruenceInput_of_integralQSeries
    (h : IntegralQSeriesCongruenceInput) : DLNCongruenceInput.{u} := by
  intro 𝒱 _ _ V _ D hD N hN
  choose k hk using hN.2
  let r : D.ι → ℚ := fun a => (k a : ℚ) / N
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.1.ne'
  have he : ∀ a, (r a : ℂ) = (D.h a : ℂ) - V.centralCharge / 24 := by
    intro a
    dsimp [r]
    push_cast
    apply (div_eq_iff hn).mpr
    simpa only [mul_comm] using (hk a).symm
  apply h D.ι r
    (fun a n => (Module.finrank ℂ ((D.module a).weight ((D.h a : ℂ) + n)) : ℤ)) D.ch D.S
  · intro a τ hτ
    simpa only [Int.cast_natCast, he, sub_add_eq_add_sub] using hD.char a τ hτ
  · exact hD.S_transform
  · exact hN.1
  · intro a
    exact ⟨k a, by rw [he]; exact hk a⟩

end VOA.Huang.DLNAlg
