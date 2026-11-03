import VOA.Classification.COne.OrbRat4Normal
import VOA.Classification.COne.OrbRat4Telescope

/-! # `V8OuterCertificates` holds

The five list identities `OrbRat3.OuterCert n Zn w` (`n ≤ 4`) about the executable evaluator
`actU`, which `OrbRat3` left open because their direct kernel evaluation exceeds the memory budget,
follow from the semantic outer products `outer0`–`outer4` (proved through skew-symmetry and small
kernel certificates) and the faithfulness of the evaluator's normal forms
(`bucket_eq_of_eval`).
-/
set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbRat4
open VOA OrbC2e OrbRat3

theorem outerCert_0 : OuterCert 0 Z0 (-379468800) := by
  unfold OuterCert
  apply bucket_eq_of_eval _ (actU_sectors _ _ _ Z_sectors_0) _ (by norm_num)
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (0 : ℤ)
  have h := outer0
  rw [inner_0] at hz h
  rw [← actU_sound _ _ Z0 hz (by norm_num) (by norm_num),
    show (16 : ℤ) - ((0 : ℕ) : ℤ) = 16 by norm_num, h]

theorem outerCert_1 : OuterCert 1 Z1 (-86184000) := by
  unfold OuterCert
  apply bucket_eq_of_eval _ (actU_sectors _ _ _ Z_sectors_1) _ (by norm_num)
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (1 : ℤ)
  have h := outer1
  rw [inner_1] at hz h
  rw [← actU_sound _ _ Z1 hz (by norm_num) (by norm_num),
    show (16 : ℤ) - ((1 : ℕ) : ℤ) = 15 by norm_num, h]

theorem outerCert_2 : OuterCert 2 Z2 (-16416000) := by
  unfold OuterCert
  apply bucket_eq_of_eval _ (actU_sectors _ _ _ Z_sectors_2) _ (by norm_num)
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (2 : ℤ)
  have h := outer2
  rw [inner_2] at hz h
  rw [← actU_sound _ _ Z2 hz (by norm_num) (by norm_num),
    show (16 : ℤ) - ((2 : ℕ) : ℤ) = 14 by norm_num, h]

theorem outerCert_3 : OuterCert 3 Z3 (-2462400) := by
  unfold OuterCert
  apply bucket_eq_of_eval _ (actU_sectors _ _ _ Z_sectors_3) _ (by norm_num)
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (3 : ℤ)
  have h := outer3
  rw [inner_3] at hz h
  rw [← actU_sound _ _ Z3 hz (by norm_num) (by norm_num),
    show (16 : ℤ) - ((3 : ℕ) : ℤ) = 13 by norm_num, h]

theorem outerCert_4 : OuterCert 4 Z4 (-259200) := by
  unfold OuterCert
  apply bucket_eq_of_eval _ (actU_sectors _ _ _ Z_sectors_4) _ (by norm_num)
  have hz := (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem (4 : ℤ)
  have h := outer4
  rw [inner_4] at hz h
  rw [← actU_sound _ _ Z4 hz (by norm_num) (by norm_num),
    show (16 : ℤ) - ((4 : ℕ) : ℤ) = 12 by norm_num, h]

/-- The residual of `OrbRat3`, closed. -/
theorem v8OuterCertificates_holds : V8OuterCertificates :=
  ⟨outerCert_0, outerCert_1, outerCert_2, outerCert_3, outerCert_4⟩

/-- The `OrbRat3` telescope, instantiated with the closed residual. -/
theorem telescope_V8_of_certs :
    ∑ n ∈ Finset.range 9, ((-1 : ℂ) ^ n * ((16 : ℕ).choose n : ℂ)) •
      (V2m 4 four_ge_one).smul Uc (((16 : ℕ) : ℤ) - n) ((V2m 4 four_ge_one).smul Uc n hV) =
        (-345600 : ℂ) • hV :=
  telescope_V8 v8OuterCertificates_holds

end VOA.Classification.COne.OrbRat4
