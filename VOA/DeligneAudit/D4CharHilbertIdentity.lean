import VOA.DeligneAudit.D4CharHilbertSpecialization

/-! L4: the all-n, all-degree Demazure Hilbert identity, with no character hypothesis. -/

namespace VOA.DeligneAudit.D4Char

open DeligneCharacter

noncomputable section

theorem rsEvOne_Cdem_coeff (n N : ℕ) :
    (D4K.ev1 (D4K.Cdem n)).coeff (2 * (N : ℤ)) = (D4K.hilbInt n N : ℚ) := by
  rw [D4K.ev1_Cdem, D4K.coeff_list_sum, List.map_map, D4K.hilbInt]
  generalize demazureChar cartanD4 thetaD4 wordD4 n = l
  induction l with
  | nil => simp
  | cons t l ih =>
      have he : 2 * (t.1.2 + (n : ℤ) * n) = 2 * (N : ℤ) ↔
          t.1.2 + (n : ℤ) * n = N := by omega
      by_cases ht : t.1.2 + (n : ℤ) * n = N
      · simp [HahnSeries.coeff_single, ht, ih, he, eq_comm]
      · simp [HahnSeries.coeff_single, ht, ih, he, eq_comm]

/-- The exact L4 target, proved for every highest weight and every graded degree. -/
theorem d4_hilbInt_eq_levi (n N : ℕ) : D4K.hilbInt n N = (d4LeviHilb n N : ℤ) := by
  have hh := congrArg (fun z : D4K.Kq => z.coeff (2 * (N : ℤ))) (rsEvOne_Cdem n)
  dsimp only at hh
  rw [rsEvOne_Cdem_coeff, rsPolyMap_coeff, coeff_d4LeviPoly] at hh
  exact_mod_cast hh

theorem d4_hilbertIdentity : HilbertIdentity := d4_hilbInt_eq_levi

/-- Coefficient positivity follows from the natural-valued Levi formula. -/
theorem d4_hilbInt_nonneg (n N : ℕ) : 0 ≤ D4K.hilbInt n N := by
  rw [d4_hilbInt_eq_levi]
  exact Int.natCast_nonneg _

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsEvOne_Cdem_coeff
#print axioms VOA.DeligneAudit.D4Char.d4_hilbInt_eq_levi
#print axioms VOA.DeligneAudit.D4Char.d4_hilbertIdentity
#print axioms VOA.DeligneAudit.D4Char.d4_hilbInt_nonneg
