import VOA.DeligneAudit.D4CharGradedReduction
import VOA.DeligneAudit.D4FusionToroidalStarModel

/-! The character realization squeeze, with the remaining L1 hypothesis explicit. -/

namespace VOA.DeligneAudit.D4Char

open SectorWeyl UnivG DeligneSector.D4 DeligneCharacter

noncomputable section

/-- L2 in the exact degrees of the actual finite cyclic tensor model. -/
theorem d4_model_degree_sum (n : ℕ) :
    ∃ B : ℕ, ∀ C : ℕ, B ≤ C →
      (∑ N ∈ Finset.range C, Module.finrank ℂ
        (cycDeg (D1TensorG.Gr.D4Check.modelRep n)
          (D1TensorG.Gr.D4Check.modelGenerator n) N)) = 29 ^ n := by
  obtain ⟨B, hB⟩ := D1TensorG.Gr.exists_stable_sum_finrank
    (D1TensorG.D4Check.currentRep n) (D1TensorG.D4Check.highest n)
    (D1TensorG.D4Check.current_cyclic n)
  refine ⟨B, fun C hC => ?_⟩
  calc
    _ = ∑ N ∈ Finset.range C, Module.finrank ℂ
        (cycDeg (D1TensorG.Gr.grRep (D1TensorG.D4Check.currentRep n)
          (D1TensorG.D4Check.highest n))
          (D1TensorG.Gr.wg (D1TensorG.D4Check.currentRep n)
            (D1TensorG.D4Check.highest n)) N) := by
      apply Finset.sum_congr rfl
      intro N _
      exact D1TensorG.Gr.finrank_cycDeg_cyclicRep _ _ N
    _ = _ := (hB C hC).trans (D1TensorG.D4Check.dimension n)

/-- Natural-valued degree bounds with the same finite total are equal term by term. -/
theorem d4_degree_eq_of_upper_and_total (n : ℕ) (c : ℕ → ℕ)
    (hup : ∀ N, c N ≤ d4LeviHilb n N)
    (htotal : ∃ B, 29 ^ n ≤ ∑ N ∈ Finset.range B, c N) :
    ∀ N, c N = d4LeviHilb n N := by
  obtain ⟨B, hzero, hsum⟩ := d4LeviHilb_sum n
  obtain ⟨C, hC⟩ := htotal
  intro N
  apply le_antisymm (hup N)
  by_cases hN : B ≤ N
  · rw [hzero N hN]
    exact Nat.zero_le _
  · let M := max B C
    have hsumM : (∑ e ∈ Finset.range M, d4LeviHilb n e) = 29 ^ n := by
      rw [← hsum]
      exact (Finset.sum_subset (Finset.range_mono (le_max_left B C))
        (fun e _ he => hzero e (by simpa using he))).symm
    have hsumc : 29 ^ n ≤ ∑ e ∈ Finset.range M, c e :=
      hC.trans (Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_right B C)))
    by_contra hlt
    have hstrict : c N < d4LeviHilb n N := Nat.lt_of_not_ge hlt
    have hs := Finset.sum_lt_sum (fun e (_ : e ∈ Finset.range M) => hup e)
      ⟨N, Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_of_not_ge hN)
        (le_max_left B C)), hstrict⟩
    omega

/-- Once L1 holds, every degree of the model attains the Levi bound. -/
theorem d4_model_degree_eq_levi (hL1 : GradedLeviBound) (n N : ℕ) :
    Module.finrank ℂ (cycDeg (D1TensorG.Gr.D4Check.modelRep n)
      (D1TensorG.Gr.D4Check.modelGenerator n) N) = d4LeviHilb n N := by
  apply d4_degree_eq_of_upper_and_total n _
    (hL1 n _ _ _ (Toroidal.model_ravFam_sat n)) _ N
  obtain ⟨B, hB⟩ := d4_model_degree_sum n
  exact ⟨B, (hB B le_rfl).ge⟩

/-- The original algorithmic Demazure series has exactly the Levi coefficients. -/
theorem d4_hilbSeriesZ_coeff_eq_levi (n N : ℕ) :
    PowerSeries.coeff N (D4Wp.hilbSeriesZ n) = (d4LeviHilb n N : ℚ) := by
  simp only [D4Wp.hilbSeriesZ, PowerSeries.coeff_mk, d4_hilbInt_eq_levi,
    Int.cast_natCast]

/-- The full realization input hD follows from L1; no fusion bound is used. -/
theorem d4_demazureRealization_of_gradedLeviBound (hL1 : GradedLeviBound) :
    ∀ n, DemazureRealizationG D4sector (ravFam D4sector) D4Wp.hilbSeriesZ n := by
  intro n
  refine ⟨D1TensorG.Gr.D4Check.modelSpace n, inferInstance, inferInstance,
    D1TensorG.Gr.D4Check.modelRep n, D1TensorG.Gr.D4Check.modelGenerator n,
    Toroidal.model_ravFam_sat n, fun N => ?_⟩
  rw [d4_hilbSeriesZ_coeff_eq_levi]
  exact_mod_cast (d4_model_degree_eq_levi hL1 n N).ge

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.d4_model_degree_sum
#print axioms VOA.DeligneAudit.D4Char.d4_degree_eq_of_upper_and_total
#print axioms VOA.DeligneAudit.D4Char.d4_model_degree_eq_levi
#print axioms VOA.DeligneAudit.D4Char.d4_hilbSeriesZ_coeff_eq_levi
#print axioms VOA.DeligneAudit.D4Char.d4_demazureRealization_of_gradedLeviBound
