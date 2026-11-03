import VOA.Classification.COne.PlusSplitOmegaECharacters

/-! Numerical checks for the four twisted rows and the W value forced by
the mixed relation. These checks do not assert existence of characters. -/
set_option maxSynthPendingDepth 3
noncomputable section

namespace VOA.Classification.COne.PlusCharacterTable
open PlusZhuNormalForms

/-- The candidate values of the three Zhu generators. -/
def twistedRow (m : ℕ) (i : Fin 4) : Fin 3 → ℂ :=
  row m (twistedLabel m i)

theorem twistedRow_E_ne_zero (m : ℕ) (hm2 : 2 ≤ m) (i : Fin 4) :
    twistedRow m i 2 ≠ 0 := by
  have ha : (twistedScale m : ℂ) ≠ 0 := by
    exact_mod_cast twistedScale_ne_zero m
  have hm : (4 * (m : ℂ) - 1) ≠ 0 := by
    intro h
    have hz : 4 * (m : ℤ) - 1 = 0 := by exact_mod_cast h
    omega
  fin_cases i <;>
    simp [twistedRow, row, values, exceptional, twistedLabel, ha, hm]

/-- All four rows satisfy the quadratic W identity. -/
theorem twistedRow_W_squared (m : ℕ) (i : Fin 4) :
    twistedRow m i 1 ^ 2 =
      (-264/7 : ℂ) * twistedRow m i 0 ^ 3 + (3/7 : ℂ) * twistedRow m i 1 -
      (6/7 : ℂ) * twistedRow m i 0 -
      (37/7 : ℂ) * (twistedRow m i 0 * twistedRow m i 1) +
      (102/7 : ℂ) * twistedRow m i 0 ^ 2 +
      (132/7 : ℂ) * (twistedRow m i 0 ^ 2 * twistedRow m i 1) := by
  fin_cases i <;> norm_num [twistedRow, row, values, exceptional, twistedLabel]

/-- All four rows satisfy the highest W-column identity. -/
theorem twistedRow_omega_cubed_W (m : ℕ) (i : Fin 4) :
    twistedRow m i 0 ^ 3 * twistedRow m i 1 =
      2 * twistedRow m i 0 ^ 4 - (13/4 : ℂ) * twistedRow m i 0 ^ 3 +
      (169/128 : ℂ) * twistedRow m i 0 ^ 2 - (9/128 : ℂ) * twistedRow m i 0 +
      (9/256 : ℂ) * twistedRow m i 1 -
      (169/256 : ℂ) * (twistedRow m i 0 * twistedRow m i 1) +
      (13/8 : ℂ) * (twistedRow m i 0 ^ 2 * twistedRow m i 1) := by
  fin_cases i <;> norm_num [twistedRow, row, values, exceptional, twistedLabel]

/-- The cubic E annihilator vanishes at both twisted conformal weights. -/
theorem twistedRow_omega_E (m : ℕ) (i : Fin 4) :
    (twistedRow m i 0 - (m : ℂ)/4) * (twistedRow m i 0 - 1/16) *
      (twistedRow m i 0 - 9/16) * twistedRow m i 2 = 0 := by
  fin_cases i <;> norm_num [twistedRow, row, values, exceptional, twistedLabel]

/-- Uniform scalar check of the mixed relation, after cancelling E. -/
theorem twistedRow_mixed (m : ℕ) (i : Fin 4) :
    ((4 * (m : ℂ) - 1) * (4 * m - 9)) * twistedRow m i 1 =
      (60 - 160 * (m : ℂ)) * twistedRow m i 0 ^ 2 +
      (72 * (m : ℂ)^2 - 80*m + 3) * twistedRow m i 0 -
      (15/4 : ℂ) * m * (m - 1) := by
  fin_cases i <;>
    norm_num [twistedRow, row, values, exceptional, twistedLabel] <;> ring

variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance candidateRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance candidateAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) :=
  instAlgebraA _

/-- Any actual character with the proposed omega and E values necessarily
has the proposed W value too. This is a uniqueness result, not existence. -/
theorem twisted_W_forced (hm2 : 2 ≤ m) (i : Fin 4)
    (χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ)
    (h0 : χ (generator m hm 0) = twistedRow m i 0)
    (h2 : χ (generator m hm 2) = twistedRow m i 2) :
    χ (generator m hm 1) = twistedRow m i 1 := by
  have h := congrArg χ (W_E_relation m hm hm2)
  simp only [map_smul, map_mul, map_add, map_sub, map_pow, smul_eq_mul, h0, h2] at h
  have he := twistedRow_E_ne_zero m hm2 i
  have hd := mixed_denominator_ne_zero m hm2
  have hc : ((4 * (m : ℂ) - 1) * (4 * m - 9)) * χ (generator m hm 1) =
      ((4 * (m : ℂ) - 1) * (4 * m - 9)) * twistedRow m i 1 := by
    apply mul_right_cancel₀ he
    rw [twistedRow_mixed]
    calc
      _ = (60 - 160 * (m : ℂ)) * (twistedRow m i 0 ^ 2 * twistedRow m i 2) +
          (72 * (m : ℂ)^2 - 80*m + 3) * (twistedRow m i 0 * twistedRow m i 2) -
          (15/4 * (m : ℂ) * (m - 1)) * twistedRow m i 2 := by
            simpa only [mul_assoc] using h
      _ = _ := by ring
  exact mul_left_cancel₀ hd hc

end VOA.Classification.COne.PlusCharacterTable

namespace VOA.Classification.COne
open PlusCharacterTable PlusZhuNormalForms

/-- The omega/E-only interface is equivalent to the full twisted-row interface. -/
theorem twistedOmegaECharacters_iff_twistedCharacters :
    V2mPlusTwistedOmegaECharacters ↔ V2mPlusTwistedCharacters := by
  refine ⟨?_, twistedOmegaECharacters_of_twistedCharacters⟩
  intro ht m hm hm2 j hj
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  have hj' : ∃ i : Fin 4, j = twistedLabel m i := by
    rcases j with j | j
    · exact (hj trivial).elim
    · have hj4 : 4 ≤ j.val := by simpa [IsUntwisted] using hj
      refine ⟨⟨j.val - 4, by omega⟩, ?_⟩
      congr 1
      apply Fin.ext
      simp
      omega
  obtain ⟨i, rfl⟩ := hj'
  obtain ⟨χ, h0, h2⟩ := ht m hm hm2 i
  rw [twistedPair_eq_table] at h0 h2
  exact ⟨χ, h0, twisted_W_forced m hm hm2 i χ h0 h2, h2⟩

end VOA.Classification.COne
