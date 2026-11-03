import VOA.Classification.COne.OrbRat3Inner

/-! # Certified outer products `U₍11₎ U₍5₎ h(-1)1` in `V₈`, term by term

The finite iterate expansion of `U₍11₎` on `Z5` has `8` terms; each is certified by
`decide +kernel` to be a multiple of `h(-1)1`.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000

namespace VOA.Classification.COne.OrbRat3
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN
  MvPolynomial VOA.SparseRational PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e LatMod

theorem outer_cert_5_0 :
    bucket [-2, 0, 2] (termU 11 0 Z5) = [(-2, []), (0, []), (2, [])] := by
  decide +kernel

theorem outer_cert_5_1 :
    bucket [-2, 0, 2] (termU 11 1 Z5) = [(-2, []), (0, []), (2, [])] := by
  decide +kernel

theorem outer_cert_5_2 :
    bucket [-2, 0, 2] (termU 11 2 Z5) = [(-2, []), (0, []), (2, [])] := by
  decide +kernel

theorem outer_cert_5_3 :
    bucket [-2, 0, 2] (termU 11 3 Z5) = [(-2, []), (0, [(11520, [1])]), (2, [])] := by
  decide +kernel

theorem outer_cert_5_4 :
    bucket [-2, 0, 2] (termU 11 4 Z5) = [(-2, []), (0, [(28800, [1])]), (2, [])] := by
  decide +kernel

theorem outer_cert_5_5 :
    bucket [-2, 0, 2] (termU 11 5 Z5) = [(-2, []), (0, [(-34560, [1])]), (2, [])] := by
  decide +kernel

theorem outer_cert_5_6 :
    bucket [-2, 0, 2] (termU 11 6 Z5) = [(-2, []), (0, [(-20160, [1])]), (2, [])] := by
  decide +kernel

theorem outer_cert_5_7 :
    bucket [-2, 0, 2] (termU 11 7 Z5) = [(-2, []), (0, []), (2, [])] := by
  decide +kernel

theorem termU_sectors_5 (k : ℤ) (i : ℕ) : ∀ p ∈ termU k i Z5, p.1 ∈ [-2, 0, 2] := by
  intro p hp
  simp only [termU, scaleSt, actJ, actE, Z5, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  aesop

/-- The value of the `i`-th iterate term (`0` when absent). -/
def outerVal5 : ℕ → ℚ := fun i => ([0, 0, 0, 11520, 28800, -34560, -20160, 0] : List ℚ).getD i 0

theorem outer_term_5 (i : ℕ) (hi : i < 8) :
    evalSt (termU 11 i Z5) = (outerVal5 i : ℂ) • hV := by
  rw [← evalSt_bucket _ (by decide) _ (termU_sectors_5 _ _)]
  interval_cases i
  · rw [outer_cert_5_0, evalSt_three, evRc_nil, map_zero]; simp [outerVal5]
  · rw [outer_cert_5_1, evalSt_three, evRc_nil, map_zero]; simp [outerVal5]
  · rw [outer_cert_5_2, evalSt_three, evRc_nil, map_zero]; simp [outerVal5]
  · rw [outer_cert_5_3, evalSt_three, sector_one]; simp [outerVal5]
  · rw [outer_cert_5_4, evalSt_three, sector_one]; simp [outerVal5]
  · rw [outer_cert_5_5, evalSt_three, sector_one]; simp [outerVal5]
  · rw [outer_cert_5_6, evalSt_three, sector_one]; simp [outerVal5]
  · rw [outer_cert_5_7, evalSt_three, evRc_nil, map_zero]; simp [outerVal5]

/-- `U₍11₎ U₍5₎ h(-1)1 = (-14400) h(-1)1` in `V₈`. -/
theorem outer_5 : (V2m 4 four_ge_one).smul Uc 11 ((V2m 4 four_ge_one).smul Uc 5 hV) =
    ((-14400 : ℚ) : ℂ) • hV := by
  have hz : (V2m 4 four_ge_one).smul Uc 5 hV ∈ (V2m 4 four_ge_one).grading 4 :=
    (V2m 4 four_ge_one).smul_mem_grading Uc_mem hV_mem 5
  rw [inner_5] at hz ⊢
  rw [actU_sound 11 8 Z5 hz (by norm_num) (by norm_num), actU, evalSt_flatMap, list_range_sum,
    Finset.sum_congr rfl (fun i hi => outer_term_5 i (Finset.mem_range.mp hi)), ← Finset.sum_smul]
  congr 1
  simp [Finset.sum_range_succ, outerVal5]
  norm_num

end VOA.Classification.COne.OrbRat3
