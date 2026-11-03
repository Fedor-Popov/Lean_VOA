import VOA.Classification.COne.OrbC2hNormalize
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e

def schurData0 : RawPoly ℕ := [(1, [])]

theorem schur_sound_0 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 0) = evRc a c schurData0 := by
  simp only [schurR, schurData0]

def schurData1 : RawPoly ℕ := [(1, [0, 1])]

theorem schur_check_1 : fastNorm (scaleR (1/1) (prependC 0 (prependC 1 (schurData0)) ++ [])) = schurData1 := by
  decide +kernel

theorem schur_sound_1 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 1) = evRc a c schurData1 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0]
  have h := congrArg (evRc a c) schur_check_1
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData2 : RawPoly ℕ := [(1/2, [0, 0, 1, 1]),
    (1/2, [0, 2])]

theorem schur_check_2 : fastNorm (scaleR (1/2) (prependC 0 (prependC 1 (schurData1)) ++ prependC 0 (prependC 2 (schurData0)) ++ [])) = schurData2 := by
  decide +kernel

theorem schur_sound_2 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 2) = evRc a c schurData2 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1]
  have h := congrArg (evRc a c) schur_check_2
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData3 : RawPoly ℕ := [(1/6, [0, 0, 0, 1, 1, 1]),
    (1/2, [0, 0, 1, 2]),
    (1/3, [0, 3])]

theorem schur_check_3 : fastNorm (scaleR (1/3) (prependC 0 (prependC 1 (schurData2)) ++ prependC 0 (prependC 2 (schurData1)) ++ prependC 0 (prependC 3 (schurData0)) ++ [])) = schurData3 := by
  decide +kernel

theorem schur_sound_3 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 3) = evRc a c schurData3 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2]
  have h := congrArg (evRc a c) schur_check_3
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData4 : RawPoly ℕ := [(1/24, [0, 0, 0, 0, 1, 1, 1, 1]),
    (1/4, [0, 0, 0, 1, 1, 2]),
    (1/3, [0, 0, 1, 3]),
    (1/8, [0, 0, 2, 2]),
    (1/4, [0, 4])]

theorem schur_check_4 : fastNorm (scaleR (1/4) (prependC 0 (prependC 1 (schurData3)) ++ prependC 0 (prependC 2 (schurData2)) ++ prependC 0 (prependC 3 (schurData1)) ++ prependC 0 (prependC 4 (schurData0)) ++ [])) = schurData4 := by
  decide +kernel

theorem schur_sound_4 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 4) = evRc a c schurData4 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3]
  have h := congrArg (evRc a c) schur_check_4
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData5 : RawPoly ℕ := [(1/120, [0, 0, 0, 0, 0, 1, 1, 1, 1, 1]),
    (1/12, [0, 0, 0, 0, 1, 1, 1, 2]),
    (1/6, [0, 0, 0, 1, 1, 3]),
    (1/8, [0, 0, 0, 1, 2, 2]),
    (1/4, [0, 0, 1, 4]),
    (1/6, [0, 0, 2, 3]),
    (1/5, [0, 5])]

theorem schur_check_5 : fastNorm (scaleR (1/5) (prependC 0 (prependC 1 (schurData4)) ++ prependC 0 (prependC 2 (schurData3)) ++ prependC 0 (prependC 3 (schurData2)) ++ prependC 0 (prependC 4 (schurData1)) ++ prependC 0 (prependC 5 (schurData0)) ++ [])) = schurData5 := by
  decide +kernel

theorem schur_sound_5 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 5) = evRc a c schurData5 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3, schur_sound_4]
  have h := congrArg (evRc a c) schur_check_5
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData6 : RawPoly ℕ := [(1/720, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1]),
    (1/48, [0, 0, 0, 0, 0, 1, 1, 1, 1, 2]),
    (1/18, [0, 0, 0, 0, 1, 1, 1, 3]),
    (1/16, [0, 0, 0, 0, 1, 1, 2, 2]),
    (1/8, [0, 0, 0, 1, 1, 4]),
    (1/6, [0, 0, 0, 1, 2, 3]),
    (1/48, [0, 0, 0, 2, 2, 2]),
    (1/5, [0, 0, 1, 5]),
    (1/8, [0, 0, 2, 4]),
    (1/18, [0, 0, 3, 3]),
    (1/6, [0, 6])]

theorem schur_check_6 : fastNorm (scaleR (1/6) (prependC 0 (prependC 1 (schurData5)) ++ prependC 0 (prependC 2 (schurData4)) ++ prependC 0 (prependC 3 (schurData3)) ++ prependC 0 (prependC 4 (schurData2)) ++ prependC 0 (prependC 5 (schurData1)) ++ prependC 0 (prependC 6 (schurData0)) ++ [])) = schurData6 := by
  decide +kernel

theorem schur_sound_6 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 6) = evRc a c schurData6 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3, schur_sound_4, schur_sound_5]
  have h := congrArg (evRc a c) schur_check_6
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData7 : RawPoly ℕ := [(1/5040, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1]),
    (1/240, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2]),
    (1/72, [0, 0, 0, 0, 0, 1, 1, 1, 1, 3]),
    (1/48, [0, 0, 0, 0, 0, 1, 1, 1, 2, 2]),
    (1/24, [0, 0, 0, 0, 1, 1, 1, 4]),
    (1/12, [0, 0, 0, 0, 1, 1, 2, 3]),
    (1/48, [0, 0, 0, 0, 1, 2, 2, 2]),
    (1/10, [0, 0, 0, 1, 1, 5]),
    (1/8, [0, 0, 0, 1, 2, 4]),
    (1/18, [0, 0, 0, 1, 3, 3]),
    (1/24, [0, 0, 0, 2, 2, 3]),
    (1/6, [0, 0, 1, 6]),
    (1/10, [0, 0, 2, 5]),
    (1/12, [0, 0, 3, 4]),
    (1/7, [0, 7])]

theorem schur_check_7 : fastNorm (scaleR (1/7) (prependC 0 (prependC 1 (schurData6)) ++ prependC 0 (prependC 2 (schurData5)) ++ prependC 0 (prependC 3 (schurData4)) ++ prependC 0 (prependC 4 (schurData3)) ++ prependC 0 (prependC 5 (schurData2)) ++ prependC 0 (prependC 6 (schurData1)) ++ prependC 0 (prependC 7 (schurData0)) ++ [])) = schurData7 := by
  decide +kernel

theorem schur_sound_7 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 7) = evRc a c schurData7 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3, schur_sound_4, schur_sound_5, schur_sound_6]
  have h := congrArg (evRc a c) schur_check_7
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData8 : RawPoly ℕ := [(1/40320, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1]),
    (1/1440, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2]),
    (1/360, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 3]),
    (1/192, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2]),
    (1/96, [0, 0, 0, 0, 0, 1, 1, 1, 1, 4]),
    (1/36, [0, 0, 0, 0, 0, 1, 1, 1, 2, 3]),
    (1/96, [0, 0, 0, 0, 0, 1, 1, 2, 2, 2]),
    (1/30, [0, 0, 0, 0, 1, 1, 1, 5]),
    (1/16, [0, 0, 0, 0, 1, 1, 2, 4]),
    (1/36, [0, 0, 0, 0, 1, 1, 3, 3]),
    (1/24, [0, 0, 0, 0, 1, 2, 2, 3]),
    (1/384, [0, 0, 0, 0, 2, 2, 2, 2]),
    (1/12, [0, 0, 0, 1, 1, 6]),
    (1/10, [0, 0, 0, 1, 2, 5]),
    (1/12, [0, 0, 0, 1, 3, 4]),
    (1/32, [0, 0, 0, 2, 2, 4]),
    (1/36, [0, 0, 0, 2, 3, 3]),
    (1/7, [0, 0, 1, 7]),
    (1/12, [0, 0, 2, 6]),
    (1/15, [0, 0, 3, 5]),
    (1/32, [0, 0, 4, 4]),
    (1/8, [0, 8])]

theorem schur_check_8 : fastNorm (scaleR (1/8) (prependC 0 (prependC 1 (schurData7)) ++ prependC 0 (prependC 2 (schurData6)) ++ prependC 0 (prependC 3 (schurData5)) ++ prependC 0 (prependC 4 (schurData4)) ++ prependC 0 (prependC 5 (schurData3)) ++ prependC 0 (prependC 6 (schurData2)) ++ prependC 0 (prependC 7 (schurData1)) ++ prependC 0 (prependC 8 (schurData0)) ++ [])) = schurData8 := by
  decide +kernel

theorem schur_sound_8 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 8) = evRc a c schurData8 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3, schur_sound_4, schur_sound_5, schur_sound_6, schur_sound_7]
  have h := congrArg (evRc a c) schur_check_8
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData9 : RawPoly ℕ := [(1/362880, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
    (1/10080, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2]),
    (1/2160, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 3]),
    (1/960, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2]),
    (1/480, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 4]),
    (1/144, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 3]),
    (1/288, [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2]),
    (1/120, [0, 0, 0, 0, 0, 1, 1, 1, 1, 5]),
    (1/48, [0, 0, 0, 0, 0, 1, 1, 1, 2, 4]),
    (1/108, [0, 0, 0, 0, 0, 1, 1, 1, 3, 3]),
    (1/48, [0, 0, 0, 0, 0, 1, 1, 2, 2, 3]),
    (1/384, [0, 0, 0, 0, 0, 1, 2, 2, 2, 2]),
    (1/36, [0, 0, 0, 0, 1, 1, 1, 6]),
    (1/20, [0, 0, 0, 0, 1, 1, 2, 5]),
    (1/24, [0, 0, 0, 0, 1, 1, 3, 4]),
    (1/32, [0, 0, 0, 0, 1, 2, 2, 4]),
    (1/36, [0, 0, 0, 0, 1, 2, 3, 3]),
    (1/144, [0, 0, 0, 0, 2, 2, 2, 3]),
    (1/14, [0, 0, 0, 1, 1, 7]),
    (1/12, [0, 0, 0, 1, 2, 6]),
    (1/15, [0, 0, 0, 1, 3, 5]),
    (1/32, [0, 0, 0, 1, 4, 4]),
    (1/40, [0, 0, 0, 2, 2, 5]),
    (1/24, [0, 0, 0, 2, 3, 4]),
    (1/162, [0, 0, 0, 3, 3, 3]),
    (1/8, [0, 0, 1, 8]),
    (1/14, [0, 0, 2, 7]),
    (1/18, [0, 0, 3, 6]),
    (1/20, [0, 0, 4, 5]),
    (1/9, [0, 9])]

theorem schur_check_9 : fastNorm (scaleR (1/9) (prependC 0 (prependC 1 (schurData8)) ++ prependC 0 (prependC 2 (schurData7)) ++ prependC 0 (prependC 3 (schurData6)) ++ prependC 0 (prependC 4 (schurData5)) ++ prependC 0 (prependC 5 (schurData4)) ++ prependC 0 (prependC 6 (schurData3)) ++ prependC 0 (prependC 7 (schurData2)) ++ prependC 0 (prependC 8 (schurData1)) ++ prependC 0 (prependC 9 (schurData0)) ++ [])) = schurData9 := by
  decide +kernel

theorem schur_sound_9 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 9) = evRc a c schurData9 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3, schur_sound_4, schur_sound_5, schur_sound_6, schur_sound_7, schur_sound_8]
  have h := congrArg (evRc a c) schur_check_9
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData10 : RawPoly ℕ := [(1/3628800, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
    (1/80640, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
    (1/15120, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 3]),
    (1/5760, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2]),
    (1/2880, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 4]),
    (1/720, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 3]),
    (1/1152, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2]),
    (1/600, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 5]),
    (1/192, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 4]),
    (1/432, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 3, 3]),
    (1/144, [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3]),
    (1/768, [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 2]),
    (1/144, [0, 0, 0, 0, 0, 1, 1, 1, 1, 6]),
    (1/60, [0, 0, 0, 0, 0, 1, 1, 1, 2, 5]),
    (1/72, [0, 0, 0, 0, 0, 1, 1, 1, 3, 4]),
    (1/64, [0, 0, 0, 0, 0, 1, 1, 2, 2, 4]),
    (1/72, [0, 0, 0, 0, 0, 1, 1, 2, 3, 3]),
    (1/144, [0, 0, 0, 0, 0, 1, 2, 2, 2, 3]),
    (1/3840, [0, 0, 0, 0, 0, 2, 2, 2, 2, 2]),
    (1/42, [0, 0, 0, 0, 1, 1, 1, 7]),
    (1/24, [0, 0, 0, 0, 1, 1, 2, 6]),
    (1/30, [0, 0, 0, 0, 1, 1, 3, 5]),
    (1/64, [0, 0, 0, 0, 1, 1, 4, 4]),
    (1/40, [0, 0, 0, 0, 1, 2, 2, 5]),
    (1/24, [0, 0, 0, 0, 1, 2, 3, 4]),
    (1/162, [0, 0, 0, 0, 1, 3, 3, 3]),
    (1/192, [0, 0, 0, 0, 2, 2, 2, 4]),
    (1/144, [0, 0, 0, 0, 2, 2, 3, 3]),
    (1/16, [0, 0, 0, 1, 1, 8]),
    (1/14, [0, 0, 0, 1, 2, 7]),
    (1/18, [0, 0, 0, 1, 3, 6]),
    (1/20, [0, 0, 0, 1, 4, 5]),
    (1/48, [0, 0, 0, 2, 2, 6]),
    (1/30, [0, 0, 0, 2, 3, 5]),
    (1/64, [0, 0, 0, 2, 4, 4]),
    (1/72, [0, 0, 0, 3, 3, 4]),
    (1/9, [0, 0, 1, 9]),
    (1/16, [0, 0, 2, 8]),
    (1/21, [0, 0, 3, 7]),
    (1/24, [0, 0, 4, 6]),
    (1/50, [0, 0, 5, 5]),
    (1/10, [0, 10])]

theorem schur_check_10 : fastNorm (scaleR (1/10) (prependC 0 (prependC 1 (schurData9)) ++ prependC 0 (prependC 2 (schurData8)) ++ prependC 0 (prependC 3 (schurData7)) ++ prependC 0 (prependC 4 (schurData6)) ++ prependC 0 (prependC 5 (schurData5)) ++ prependC 0 (prependC 6 (schurData4)) ++ prependC 0 (prependC 7 (schurData3)) ++ prependC 0 (prependC 8 (schurData2)) ++ prependC 0 (prependC 9 (schurData1)) ++ prependC 0 (prependC 10 (schurData0)) ++ [])) = schurData10 := by
  decide +kernel

theorem schur_sound_10 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 10) = evRc a c schurData10 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3, schur_sound_4, schur_sound_5, schur_sound_6, schur_sound_7, schur_sound_8, schur_sound_9]
  have h := congrArg (evRc a c) schur_check_10
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData11 : RawPoly ℕ := [(1/39916800, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
    (1/725760, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
    (1/120960, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
    (1/40320, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
    (1/20160, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 4]),
    (1/4320, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 3]),
    (1/5760, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2]),
    (1/3600, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 5]),
    (1/960, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 4]),
    (1/2160, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 3, 3]),
    (1/576, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3]),
    (1/2304, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2]),
    (1/720, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 6]),
    (1/240, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 5]),
    (1/288, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 3, 4]),
    (1/192, [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 4]),
    (1/216, [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 3, 3]),
    (1/288, [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 3]),
    (1/3840, [0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 2]),
    (1/168, [0, 0, 0, 0, 0, 1, 1, 1, 1, 7]),
    (1/72, [0, 0, 0, 0, 0, 1, 1, 1, 2, 6]),
    (1/90, [0, 0, 0, 0, 0, 1, 1, 1, 3, 5]),
    (1/192, [0, 0, 0, 0, 0, 1, 1, 1, 4, 4]),
    (1/80, [0, 0, 0, 0, 0, 1, 1, 2, 2, 5]),
    (1/48, [0, 0, 0, 0, 0, 1, 1, 2, 3, 4]),
    (1/324, [0, 0, 0, 0, 0, 1, 1, 3, 3, 3]),
    (1/192, [0, 0, 0, 0, 0, 1, 2, 2, 2, 4]),
    (1/144, [0, 0, 0, 0, 0, 1, 2, 2, 3, 3]),
    (1/1152, [0, 0, 0, 0, 0, 2, 2, 2, 2, 3]),
    (1/48, [0, 0, 0, 0, 1, 1, 1, 8]),
    (1/28, [0, 0, 0, 0, 1, 1, 2, 7]),
    (1/36, [0, 0, 0, 0, 1, 1, 3, 6]),
    (1/40, [0, 0, 0, 0, 1, 1, 4, 5]),
    (1/48, [0, 0, 0, 0, 1, 2, 2, 6]),
    (1/30, [0, 0, 0, 0, 1, 2, 3, 5]),
    (1/64, [0, 0, 0, 0, 1, 2, 4, 4]),
    (1/72, [0, 0, 0, 0, 1, 3, 3, 4]),
    (1/240, [0, 0, 0, 0, 2, 2, 2, 5]),
    (1/96, [0, 0, 0, 0, 2, 2, 3, 4]),
    (1/324, [0, 0, 0, 0, 2, 3, 3, 3]),
    (1/18, [0, 0, 0, 1, 1, 9]),
    (1/16, [0, 0, 0, 1, 2, 8]),
    (1/21, [0, 0, 0, 1, 3, 7]),
    (1/24, [0, 0, 0, 1, 4, 6]),
    (1/50, [0, 0, 0, 1, 5, 5]),
    (1/56, [0, 0, 0, 2, 2, 7]),
    (1/36, [0, 0, 0, 2, 3, 6]),
    (1/40, [0, 0, 0, 2, 4, 5]),
    (1/90, [0, 0, 0, 3, 3, 5]),
    (1/96, [0, 0, 0, 3, 4, 4]),
    (1/10, [0, 0, 1, 10]),
    (1/18, [0, 0, 2, 9]),
    (1/24, [0, 0, 3, 8]),
    (1/28, [0, 0, 4, 7]),
    (1/30, [0, 0, 5, 6]),
    (1/11, [0, 11])]

theorem schur_check_11 : fastNorm (scaleR (1/11) (prependC 0 (prependC 1 (schurData10)) ++ prependC 0 (prependC 2 (schurData9)) ++ prependC 0 (prependC 3 (schurData8)) ++ prependC 0 (prependC 4 (schurData7)) ++ prependC 0 (prependC 5 (schurData6)) ++ prependC 0 (prependC 6 (schurData5)) ++ prependC 0 (prependC 7 (schurData4)) ++ prependC 0 (prependC 8 (schurData3)) ++ prependC 0 (prependC 9 (schurData2)) ++ prependC 0 (prependC 10 (schurData1)) ++ prependC 0 (prependC 11 (schurData0)) ++ [])) = schurData11 := by
  decide +kernel

theorem schur_sound_11 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 11) = evRc a c schurData11 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3, schur_sound_4, schur_sound_5, schur_sound_6, schur_sound_7, schur_sound_8, schur_sound_9, schur_sound_10]
  have h := congrArg (evRc a c) schur_check_11
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

def schurData12 : RawPoly ℕ := [(1/479001600, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
    (1/7257600, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
    (1/1088640, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
    (1/322560, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
    (1/161280, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
    (1/30240, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
    (1/34560, [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
    (1/25200, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 5]),
    (1/5760, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 4]),
    (1/12960, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 3, 3]),
    (1/2880, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 3]),
    (1/9216, [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2]),
    (1/4320, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 6]),
    (1/1200, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 5]),
    (1/1440, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 3, 4]),
    (1/768, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 4]),
    (1/864, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 3, 3]),
    (1/864, [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 3]),
    (1/7680, [0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 2, 2]),
    (1/840, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 7]),
    (1/288, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 6]),
    (1/360, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 3, 5]),
    (1/768, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 4, 4]),
    (1/240, [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 5]),
    (1/144, [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 3, 4]),
    (1/972, [0, 0, 0, 0, 0, 0, 1, 1, 1, 3, 3, 3]),
    (1/384, [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 4]),
    (1/288, [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3]),
    (1/1152, [0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 3]),
    (1/46080, [0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2]),
    (1/192, [0, 0, 0, 0, 0, 1, 1, 1, 1, 8]),
    (1/84, [0, 0, 0, 0, 0, 1, 1, 1, 2, 7]),
    (1/108, [0, 0, 0, 0, 0, 1, 1, 1, 3, 6]),
    (1/120, [0, 0, 0, 0, 0, 1, 1, 1, 4, 5]),
    (1/96, [0, 0, 0, 0, 0, 1, 1, 2, 2, 6]),
    (1/60, [0, 0, 0, 0, 0, 1, 1, 2, 3, 5]),
    (1/128, [0, 0, 0, 0, 0, 1, 1, 2, 4, 4]),
    (1/144, [0, 0, 0, 0, 0, 1, 1, 3, 3, 4]),
    (1/240, [0, 0, 0, 0, 0, 1, 2, 2, 2, 5]),
    (1/96, [0, 0, 0, 0, 0, 1, 2, 2, 3, 4]),
    (1/324, [0, 0, 0, 0, 0, 1, 2, 3, 3, 3]),
    (1/1536, [0, 0, 0, 0, 0, 2, 2, 2, 2, 4]),
    (1/864, [0, 0, 0, 0, 0, 2, 2, 2, 3, 3]),
    (1/54, [0, 0, 0, 0, 1, 1, 1, 9]),
    (1/32, [0, 0, 0, 0, 1, 1, 2, 8]),
    (1/42, [0, 0, 0, 0, 1, 1, 3, 7]),
    (1/48, [0, 0, 0, 0, 1, 1, 4, 6]),
    (1/100, [0, 0, 0, 0, 1, 1, 5, 5]),
    (1/56, [0, 0, 0, 0, 1, 2, 2, 7]),
    (1/36, [0, 0, 0, 0, 1, 2, 3, 6]),
    (1/40, [0, 0, 0, 0, 1, 2, 4, 5]),
    (1/90, [0, 0, 0, 0, 1, 3, 3, 5]),
    (1/96, [0, 0, 0, 0, 1, 3, 4, 4]),
    (1/288, [0, 0, 0, 0, 2, 2, 2, 6]),
    (1/120, [0, 0, 0, 0, 2, 2, 3, 5]),
    (1/256, [0, 0, 0, 0, 2, 2, 4, 4]),
    (1/144, [0, 0, 0, 0, 2, 3, 3, 4]),
    (1/1944, [0, 0, 0, 0, 3, 3, 3, 3]),
    (1/20, [0, 0, 0, 1, 1, 10]),
    (1/18, [0, 0, 0, 1, 2, 9]),
    (1/24, [0, 0, 0, 1, 3, 8]),
    (1/28, [0, 0, 0, 1, 4, 7]),
    (1/30, [0, 0, 0, 1, 5, 6]),
    (1/64, [0, 0, 0, 2, 2, 8]),
    (1/42, [0, 0, 0, 2, 3, 7]),
    (1/48, [0, 0, 0, 2, 4, 6]),
    (1/100, [0, 0, 0, 2, 5, 5]),
    (1/108, [0, 0, 0, 3, 3, 6]),
    (1/60, [0, 0, 0, 3, 4, 5]),
    (1/384, [0, 0, 0, 4, 4, 4]),
    (1/11, [0, 0, 1, 11]),
    (1/20, [0, 0, 2, 10]),
    (1/27, [0, 0, 3, 9]),
    (1/32, [0, 0, 4, 8]),
    (1/35, [0, 0, 5, 7]),
    (1/72, [0, 0, 6, 6]),
    (1/12, [0, 12])]

theorem schur_check_12 : fastNorm (scaleR (1/12) (prependC 0 (prependC 1 (schurData11)) ++ prependC 0 (prependC 2 (schurData10)) ++ prependC 0 (prependC 3 (schurData9)) ++ prependC 0 (prependC 4 (schurData8)) ++ prependC 0 (prependC 5 (schurData7)) ++ prependC 0 (prependC 6 (schurData6)) ++ prependC 0 (prependC 7 (schurData5)) ++ prependC 0 (prependC 8 (schurData4)) ++ prependC 0 (prependC 9 (schurData3)) ++ prependC 0 (prependC 10 (schurData2)) ++ prependC 0 (prependC 11 (schurData1)) ++ prependC 0 (prependC 12 (schurData0)) ++ [])) = schurData12 := by
  decide +kernel

theorem schur_sound_12 {r : ℕ} (a : Fin r) (c : ℂ) :
    evRc a c (schurR 12) = evRc a c schurData12 := by
  rw [schurR]
  simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, Nat.reduceSub, Nat.reduceAdd]
  simp only [evRc_normR, evRc_scaleR, evRc_append, evRc_prependC, schur_sound_0, schur_sound_1, schur_sound_2, schur_sound_3, schur_sound_4, schur_sound_5, schur_sound_6, schur_sound_7, schur_sound_8, schur_sound_9, schur_sound_10, schur_sound_11]
  have h := congrArg (evRc a c) schur_check_12
  simp only [evRc_fastNorm, evRc_scaleR, evRc_append, evRc_prependC, evRc_nil] at h
  convert h using 1 <;> norm_num [evRc_nil] <;> ring

end VOA.Classification.COne.OrbC2h
