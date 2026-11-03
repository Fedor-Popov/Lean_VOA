import VOA.DeligneAudit.D4CharMixedLocal

/-! Identity Y on the two-row negative block, including the equal-part boundary. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtTwo_antitone (a b : ℤ) : Antitone (![a, b] : Fin 2 → ℤ) ↔ b ≤ a := by
  constructor
  · intro h
    exact h (show (0 : Fin 2) ≤ 1 by decide)
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem gtQ_two_zero_of_lt (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (a b : ℕ) (hab : a < b) : gtQ q h u 2 ![(a : ℤ), (b : ℤ)] = 0 := by
  rw [gtQ_two_expansion, Finset.Icc_eq_empty_of_lt hab, Finset.sum_empty]

/-- Normalized e_1-Pieri at two variables, with the nondominant summand explicitly zero. -/
theorem gtQ_two_eOne (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (c d : ℕ) (hd : d ≤ c) :
    ((u 0 : R) + (u 1 : R)) * gtQ q h u 2 ![(c : ℤ), (d : ℤ)] =
      (1 - q ^ (c - d + 1)) * gtQ q h u 2 ![((c + 1 : ℕ) : ℤ), (d : ℤ)] +
        (1 - q ^ (d + 1)) * gtQ q h u 2 ![(c : ℤ), ((d + 1 : ℕ) : ℤ)] := by
  classical
  have hp : ∀ i : Fin 2, 0 ≤ (![(c : ℤ), (d : ℤ)] : Fin 2 → ℤ) i := by
    intro i
    fin_cases i <;> simp
  have hs := gtQ_ePieri q h u 2 ![(c : ℤ), (d : ℤ)]
    ((gtTwo_antitone _ _).mpr (by omega)) hp 1
  have hS : ((Finset.univ : Finset (Fin 2)).powersetCard 1) = {{0}, {1}} := by decide
  have h₀ : pieriWeight (![(c : ℤ), (d : ℤ)] : Fin 2 → ℤ) {0} =
      ![((c + 1 : ℕ) : ℤ), (d : ℤ)] := by
    ext i
    fin_cases i <;> simp [pieriWeight]
  have h₁ : pieriWeight (![(c : ℤ), (d : ℤ)] : Fin 2 → ℤ) {1} =
      ![(c : ℤ), ((d + 1 : ℕ) : ℤ)] := by
    ext i
    fin_cases i <;> simp [pieriWeight]
  have he₀ : gtExitCoeff q ![((c + 1 : ℕ) : ℤ), (d : ℤ)] {0} =
      1 - q ^ (c - d + 1) := by
    simp [gtExitCoeff, gtExitFactor, gtGapInt, gtPadBits, pieriIndicator,
      Fin.prod_univ_succ, Fin.snoc]
    congr 2
    omega
  have he₁ : gtExitCoeff q ![(c : ℤ), ((d + 1 : ℕ) : ℤ)] {1} =
      1 - q ^ (d + 1) := by
    simp [gtExitCoeff, gtExitFactor, gtGapInt, gtPadBits, pieriIndicator,
      Fin.prod_univ_succ, Fin.snoc]
  have hd₀ : Antitone (![((c + 1 : ℕ) : ℤ), (d : ℤ)] : Fin 2 → ℤ) :=
    (gtTwo_antitone _ _).mpr (by omega)
  simp only [pieriElementary, hS, Finset.sum_filter, Finset.sum_pair (by decide :
    ({0} : Finset (Fin 2)) ≠ {1}), Finset.prod_singleton, h₀, h₁, hd₀,
    ↓reduceIte, he₀, he₁] at hs
  by_cases hdc : d < c
  · have hd₁ : Antitone (![(c : ℤ), ((d + 1 : ℕ) : ℤ)] : Fin 2 → ℤ) :=
      (gtTwo_antitone _ _).mpr (by omega)
    simpa only [hd₁, ↓reduceIte] using hs
  · have hd₁ : ¬Antitone (![(c : ℤ), ((d + 1 : ℕ) : ℤ)] : Fin 2 → ℤ) := by
      rw [gtTwo_antitone]
      omega
    rw [gtQ_two_zero_of_lt q h u c (d + 1) (by omega), mul_zero, add_zero]
    simpa only [hd₁, ↓reduceIte, add_zero] using hs

/-- Normalized top Pieri in two variables. -/
theorem gtQ_two_eTwo (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (c d : ℕ) :
    ((u 0 : R) * (u 1 : R)) * gtQ q h u 2 ![(c : ℤ), (d : ℤ)] =
      (1 - q ^ (d + 1)) *
        gtQ q h u 2 ![((c + 1 : ℕ) : ℤ), ((d + 1 : ℕ) : ℤ)] := by
  rw [gtQ_two_eq, gtQ_two_eq, gtEval_two_shift]
  simp only [Nat.add_sub_add_right, pow_one]
  rw [gtInvPoch_succ q h d]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The four negative-block paths with the incoming zero edge included. -/
theorem gtMixedTailAction_two (q : R) (f : (Fin 2 → ℤ) → R) (a b : ℤ) :
    gtMixedTailAction q f ![-b, -a] =
      f ![-b, -a] - (1 - q ^ (b + 1).toNat) * f ![-b - 1, -a] -
        (1 - q ^ (a - b + 1).toNat) * f ![-b, -a - 1] +
        (1 - q ^ (b + 1).toNat) * f ![-b - 1, -a - 1] := by
  have hl (s t : Bool) : pieriLower (![-b, -a] : Fin 2 → ℤ) ![s, t] =
      ![-b - pieriBit s, -a - pieriBit t] := by
    ext i
    fin_cases i <;> rfl
  rw [gtMixedTailAction, ← (finTwoArrowEquiv Bool).symm.sum_comp]
  change (∑ st : Bool × Bool,
    gtCauchyPath q 0 false (List.ofFn fun i =>
      ((![-b, -a] : Fin 2 → ℤ) i, (![st.1, st.2] : Fin 2 → Bool) i)) *
        f (pieriLower ![-b, -a] ![st.1, st.2])) = _
  simp only [Fintype.sum_prod_type, hl, Fintype.sum_bool]
  simp [gtCauchyPath, List.ofFn_succ, gtCauchyBond, pieriBit]
  ring_nf

/-- X·Y's negative part: the tail action is the two y-side Euler denominator. -/
theorem gtMixedTailAction_Q_two (q : R) (h : PochhammerUnits q) (y : ℕ → Rˣ)
    (c d : ℕ) (hd : d ≤ c) :
    gtMixedTailAction q (fun μ => gtQ q h y 2 (gtDual μ)) ![-(d : ℤ), -(c : ℤ)] =
      (1 - (y 0 : R)) * (1 - (y 1 : R)) * gtQ q h y 2 ![(c : ℤ), (d : ℤ)] := by
  rw [gtMixedTailAction_two]
  have he (a b : ℤ) : gtDual (![-b, -a] : Fin 2 → ℤ) = ![a, b] := by
    ext i
    fin_cases i <;> simp [gtDual]
  have h₁ (a : ℤ) : -a - 1 = -(a + 1) := by ring
  simp only [h₁, he]
  have hc : ((c : ℤ) - d + 1).toNat = c - d + 1 := by omega
  have hd' : ((d : ℤ) + 1).toNat = d + 1 := by omega
  simp only [hc, hd']
  have hOne := gtQ_two_eOne q h y c d hd
  have hTwo := gtQ_two_eTwo q h y c d
  simp only [Nat.cast_add, Nat.cast_one] at hOne hTwo
  linear_combination hOne - hTwo

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtTwo_antitone
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_zero_of_lt
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_eOne
#print axioms VOA.DeligneAudit.D4Char.gtQ_two_eTwo
#print axioms VOA.DeligneAudit.D4Char.gtMixedTailAction_two
#print axioms VOA.DeligneAudit.D4Char.gtMixedTailAction_Q_two
