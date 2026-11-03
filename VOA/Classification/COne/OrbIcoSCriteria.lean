import VOA.Classification.COne.OrbIcoSMeasurements

/-! Exact scalar compatibility criterion for the two icosahedral symbols.
This module does not assert that the compatible, nonzero coefficients exist. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoS
open VOA VertexOperatorAlgebra OrbSpan OrbC2b OrbC2c OrbIco OrbXu

theorem xuU37_ne_zero : (xuU37 : ℂ) ≠ 0 := by norm_num [xuU37]
theorem xuV19_ne_zero : (xuV19 : ℂ) ≠ 0 := by norm_num [xuV19]

/-- Compatibility and nonvanishing are precisely the remaining scalar requirements.
No uniqueness of quotient coefficients is assumed. -/
theorem icoSymbolRelations_iff_coefficients : IcoSymbolRelations ↔
    ∃ a b a' b' : ℂ, a * b ≠ 0 ∧
      a * (xuU38 : ℂ) = a' * (xuU37 : ℂ) ∧
      b * (xuV20 : ℂ) = b' * (xuV19 : ℂ) ∧
      modeSymbol Wi Xico (-3) 37 19 a b ∈ O₂ Wi ∧
      modeSymbol Wi Xico (-5) 38 20 a' b' ∈ O₂ Wi := by
  constructor
  · rintro ⟨c₀, c₆, h₀, h₆, h74, h76⟩
    refine ⟨c₀ * xuU37, c₆ * xuV19, c₀ * xuU38, c₆ * xuV20,
      mul_ne_zero (mul_ne_zero h₀ xuU37_ne_zero) (mul_ne_zero h₆ xuV19_ne_zero),
      ?_, ?_, h74, h76⟩ <;> ring
  · rintro ⟨a, b, a', b', hab, ha, hb, h74, h76⟩
    have ha0 : a ≠ 0 := fun h => hab (by rw [h, zero_mul])
    have hb0 : b ≠ 0 := fun h => hab (by rw [h, mul_zero])
    have ha' : a / (xuU37 : ℂ) * (xuU38 : ℂ) = a' := by
      apply (mul_right_cancel₀ xuU37_ne_zero)
      calc
        a / (xuU37 : ℂ) * (xuU38 : ℂ) * (xuU37 : ℂ) =
            a * (xuU38 : ℂ) := by rw [mul_right_comm, div_mul_cancel₀ _ xuU37_ne_zero]
        _ = a' * (xuU37 : ℂ) := ha
    have hb' : b / (xuV19 : ℂ) * (xuV20 : ℂ) = b' := by
      apply (mul_right_cancel₀ xuV19_ne_zero)
      calc
        b / (xuV19 : ℂ) * (xuV20 : ℂ) * (xuV19 : ℂ) =
            b * (xuV20 : ℂ) := by rw [mul_right_comm, div_mul_cancel₀ _ xuV19_ne_zero]
        _ = b' * (xuV19 : ℂ) := hb
    refine ⟨a / xuU37, b / xuV19, div_ne_zero ha0 xuU37_ne_zero,
      div_ne_zero hb0 xuV19_ne_zero, ?_, ?_⟩
    · simpa only [div_mul_cancel₀ _ xuU37_ne_zero, div_mul_cancel₀ _ xuV19_ne_zero] using h74
    · simpa only [ha', hb'] using h76

/-- Intrinsic Virasoro remainders with the required scalar compatibility finish B4. -/
theorem icoSymbolRelations_of_remainders (a b a' b' : ℂ) (hab : a * b ≠ 0)
    (ha : a * (xuU38 : ℂ) = a' * (xuU37 : ℂ))
    (hb : b * (xuV20 : ℂ) = b' * (xuV19 : ℂ))
    (h74 : modeSymbol Wi Xico (-3) 37 19 a b ∈ virError Wi Wi.vacuum ⊔ virError Wi Xico)
    (h76 : modeSymbol Wi Xico (-5) 38 20 a' b' ∈ virError Wi Wi.vacuum ⊔ virError Wi Xico) :
    IcoSymbolRelations := by
  have hle := sup_le (virError_le_c2 Wi Wi.vacuum) (virError_le_c2 Wi Xico)
  exact icoSymbolRelations_iff_coefficients.mpr ⟨a, b, a', b', hab, ha, hb, hle h74, hle h76⟩

end VOA.Classification.COne.OrbIcoS
