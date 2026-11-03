import VOA.Classification.COne.OrbIcoVFockCheck01
import VOA.Classification.COne.OrbIcoVFockCheck02
import VOA.Classification.COne.OrbIcoVFockCheck03
import VOA.Classification.COne.OrbIcoVFockCheck04
import VOA.Classification.COne.OrbIcoVFockCheck05
import VOA.Classification.COne.OrbIcoVFockCheck06
import VOA.Classification.COne.OrbIcoVFockCheck07
import VOA.Classification.COne.OrbIcoVFockCheck08
import VOA.Classification.COne.OrbIcoVFockCheck09
import VOA.Classification.COne.OrbIcoVFockCheck10
import VOA.Classification.COne.OrbIcoVFockCheck11
import VOA.Classification.COne.OrbIcoVFockCheck12
import VOA.Classification.COne.OrbIcoVFockCheck13

/-! The first-row level-13 singular vector vanishes in the actual generic
charged Fock representation. No flatness or specialization is assumed. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 8192
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA HeisenbergN MvPolynomial VOA.SparseRational VOA.VirasoroScreening
  InverseDS.LeeYangFockVirasoro InverseDS.VirasoroVerma

abbrev familyCharge (s : ℂ) := 1 - 24 * familyBackground s ^ 2
abbrev familyWeight (s : ℂ) := familyMomentum s ^ 2 -
  2 * familyBackground s * familyMomentum s
abbrev familyMap (s : ℂ) := chargedFockMap (familyBackground s) (familyMomentum s)

def familyBSAState (s : ℂ) (r : ℕ) : FF :=
  familyMap s (vermaBSAState (familyCharge s) (familyWeight s) (s^2) 13 r)

def familyBSASource (s : ℂ) (r : ℕ) : FF :=
  familyMap s (vermaBSASource (familyCharge s) (familyWeight s) (s^2) 13 r)

theorem familyBSAState_zero (s : ℂ) : familyBSAState s 0 = vacuumN 1 := by
  simp only [familyBSAState, vermaBSAState_zero, familyMap, chargedFockMap,
    universalMap_highestVector]

theorem familyBSAState_source (s : ℂ) (r : ℕ) (hr : 0 < r) :
    familyBSAState s r =
      (-s^2 / ((r : ℂ) * (13 - (r : ℂ)))) • familyBSASource s r := by
  rw [familyBSAState, vermaBSAState_eq_source _ _ _ _ r hr, map_smul]
  rfl

theorem familyBSASource_sum (s : ℂ) (r : ℕ) :
    familyBSASource s r = ∑ j : Fin r,
      sectorVirasoro (familyBackground s) (familyMomentum s)
        ((j : ℤ) - (r : ℤ)) (familyBSAState s j) := by
  simp only [familyBSASource, vermaBSASource, map_sum, familyMap,
    chargedFockMap_mode, familyBSAState]

theorem fockRawEval_flatMap {ι : Type*} (s : ℂ) (xs : List ι)
    (f : ι → RawPoly ℕ) :
    fockRawEval s (xs.flatMap f) = (xs.map fun x => fockRawEval s (f x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, fockRawEval_append, ih, List.map_cons, List.sum_cons]

theorem fockDataStep (r : ℕ) (hr : 0 < r) (hmax : r < 13) :
    normalizeQ (rawScale ((r : ℚ) * (13 - (r : ℚ))) (rawPrepend 0 (fockBSAData r)) ++
      fockBSASourceData r) = [] := by
  interval_cases r
  · rw [show (((1 : ℕ) : ℚ) * (13 - ((1 : ℕ) : ℚ))) = 12 by norm_num]
    exact fockBSAData_step_1
  · rw [show (((2 : ℕ) : ℚ) * (13 - ((2 : ℕ) : ℚ))) = 22 by norm_num]
    exact fockBSAData_step_2
  · rw [show (((3 : ℕ) : ℚ) * (13 - ((3 : ℕ) : ℚ))) = 30 by norm_num]
    exact fockBSAData_step_3
  · rw [show (((4 : ℕ) : ℚ) * (13 - ((4 : ℕ) : ℚ))) = 36 by norm_num]
    exact fockBSAData_step_4
  · rw [show (((5 : ℕ) : ℚ) * (13 - ((5 : ℕ) : ℚ))) = 40 by norm_num]
    exact fockBSAData_step_5
  · rw [show (((6 : ℕ) : ℚ) * (13 - ((6 : ℕ) : ℚ))) = 42 by norm_num]
    exact fockBSAData_step_6
  · rw [show (((7 : ℕ) : ℚ) * (13 - ((7 : ℕ) : ℚ))) = 42 by norm_num]
    exact fockBSAData_step_7
  · rw [show (((8 : ℕ) : ℚ) * (13 - ((8 : ℕ) : ℚ))) = 40 by norm_num]
    exact fockBSAData_step_8
  · rw [show (((9 : ℕ) : ℚ) * (13 - ((9 : ℕ) : ℚ))) = 36 by norm_num]
    exact fockBSAData_step_9
  · rw [show (((10 : ℕ) : ℚ) * (13 - ((10 : ℕ) : ℚ))) = 30 by norm_num]
    exact fockBSAData_step_10
  · rw [show (((11 : ℕ) : ℚ) * (13 - ((11 : ℕ) : ℚ))) = 22 by norm_num]
    exact fockBSAData_step_11
  · rw [show (((12 : ℕ) : ℚ) * (13 - ((12 : ℕ) : ℚ))) = 12 by norm_num]
    exact fockBSAData_step_12

theorem fockDataStep_sound (s : ℂ) (r : ℕ) (hr : 0 < r) (hmax : r < 13) :
    ((r : ℂ) * (13 - (r : ℂ))) • ((s⁻¹^2) • fockRawEval s (fockBSAData r)) +
      fockRawEval s (fockBSASourceData r) = 0 := by
  have h := congrArg (evalSparse (fockRawVar s)) (fockDataStep r hr hmax)
  rw [evalSparse_normalizeQ] at h
  change fockRawEval s (rawScale ((r : ℚ)*(13-(r : ℚ)))
    (rawPrepend 0 (fockBSAData r)) ++ fockBSASourceData r) = 0 at h
  rw [fockRawEval_append, eval_rawScale, fockRawEval_prepend] at h
  simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, Rat.cast_ofNat,
    fockRawVar, ← smul_eq_C_mul, evalSparse, List.map_nil, List.sum_nil] using h

theorem fockBSASourceData_sound (s : ℂ) (hs : s ≠ 0) (r : ℕ)
    (ih : ∀ j : Fin r, fockRawEval s (fockBSAData j) = familyBSAState s j) :
    fockRawEval s (fockBSASourceData r) = familyBSASource s r := by
  rw [fockBSASourceData, fockRawEval_flatMap, fock_list_sum_range,
    familyBSASource_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fockRawMode_sound s hs (r-j) (by omega), ih j]
  have hm : -((r-j : ℕ) : ℤ) = (j : ℤ) - (r : ℤ) := by omega
  rw [hm]

theorem fockBSAData_sound (s : ℂ) (hs : s ≠ 0) (r : ℕ) (hmax : r < 13) :
    fockRawEval s (fockBSAData r) = familyBSAState s r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases hr : r=0
    · subst r
      rw [familyBSAState_zero]
      simp [fockBSAData, fockRawEval, evalRaw, evalWord, vacuumN]
    · have hrpos : 0 < r := by omega
      have hsrc := fockBSASourceData_sound s hs r
        (fun j => ih j j.isLt (by omega))
      have hstep := fockDataStep_sound s r hrpos hmax
      rw [hsrc, smul_smul] at hstep
      have hd : (r : ℂ) * (13 - (r : ℂ)) ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast (show r ≠ 0 by omega)
        · exact sub_ne_zero.mpr (by exact_mod_cast (show 13 ≠ r by omega))
      have hdx : ((r : ℂ)*(13-(r : ℂ))) * (s⁻¹^2) ≠ 0 :=
        mul_ne_zero hd (pow_ne_zero _ (inv_ne_zero hs))
      apply (smul_right_injective FF hdx)
      change (((r : ℂ)*(13-(r : ℂ))) * (s⁻¹^2)) • fockRawEval s (fockBSAData r) =
        (((r : ℂ)*(13-(r : ℂ))) * (s⁻¹^2)) • familyBSAState s r
      rw [familyBSAState_source s r hrpos, smul_smul]
      have he : (((r : ℂ) * (13-(r : ℂ))) * (s⁻¹^2)) *
          (-s^2 / ((r : ℂ)*(13-(r : ℂ)))) = -1 := by
        field_simp [hs, hd]
        rw [div_self hd]
      rw [he, neg_one_smul]
      exact eq_neg_of_add_eq_zero_left hstep

theorem family_fock_s13_zero (s : ℂ) (hs : s ≠ 0) : familyBSASource s 13 = 0 := by
  have hz := congrArg (evalSparse (fockRawVar s)) fockBSAData_terminal
  rw [evalSparse_normalizeQ] at hz
  change fockRawEval s (fockBSASourceData 13) = 0 at hz
  rwa [fockBSASourceData_sound s hs 13 (fun j => fockBSAData_sound s hs j j.isLt)] at hz

end VOA.Classification.COne.OrbIcoV
