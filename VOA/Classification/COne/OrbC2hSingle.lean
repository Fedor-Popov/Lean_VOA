import VOA.Classification.COne.OrbC2hQuick
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e OrbC2g

theorem sum_select_count {r : ℕ} (L : List ℤ) (s : ℤ) (x : FockN r) :
    (L.map fun m => if s = m then x else 0).sum = (L.count s : ℂ) • x := by
  induction L with
  | nil => simp
  | cons m L ih =>
    by_cases h : s = m
    · subst m
      simp [List.count_cons, ih, add_smul, add_comm]
    · simp [List.count_cons, h, Ne.symm h, ih]

def singleWord (i : ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  scaleR (((intRange (-((i+1+w : ℕ) : ℤ))
    ((max (-1) ((w:ℤ)+s))+((i+1+w : ℕ) : ℤ)+1).toNat).count s : ℕ):ℚ)
    (fActC i s P)

theorem evRc_singleWord {r : ℕ} (a : Fin r) (c : ℂ)
    (i : ℕ) (s : ℤ) (w : ℕ) (P : RawPoly ℕ) :
    evRc a c (singleWord i s w P) = evRc a c (wordActC [i] s w P) := by
  rw [singleWord, evRc_scaleR, wordActC, evRc_flatMap]
  simp only [wWt, zero_add]
  rw [show (intRange (-((i+1+w : ℕ):ℤ))
    ((max (-1) ((w:ℤ)+s))+((i+1+w : ℕ):ℤ)+1).toNat).map
    (fun m => evRc a c (if 0 ≤ m then fActC i m (wordActC [] (s-m) w P)
      else wordActC [] (s-m) ((((i+1+w:ℕ):ℤ)+m).toNat) (fActC i m P))) =
    (intRange (-((i+1+w : ℕ):ℤ))
    ((max (-1) ((w:ℤ)+s))+((i+1+w : ℕ):ℤ)+1).toNat).map
    (fun m => if s=m then evRc a c (fActC i s P) else 0) from by
      apply List.map_congr_left
      intro m hm
      by_cases he : s=m
      · subst m; simp [wordActC]
      · have hz : s-m ≠ 0 := sub_ne_zero.mpr he
        simp [wordActC, hz, he, fActC, evRc_nil]]
  rw [sum_select_count]
  rw [Rat.cast_natCast]

def wordSingle : List ℕ → ℤ → ℕ → RawPoly ℕ → RawPoly ℕ
  | [], s, _, P => if s = 0 then P else []
  | [i], s, w, P => fastNormFuel (singleWord i s w P)
  | i :: j :: is, s, w, P => if P = [] then [] else
    fastNormFuel ((intRange (-((i+1+w : ℕ) : ℤ))
      ((max (-1) (((wWt (j::is)+w : ℕ) : ℤ)+s))+((i+1+w : ℕ) : ℤ)+1).toNat).flatMap
      fun m => if 0 ≤ m then fastNormFuel (fActC i m (wordSingle (j::is) (s-m) w P))
        else wordSingle (j::is) (s-m) ((((i+1+w : ℕ) : ℤ)+m).toNat) (fastNormFuel (fActC i m P)))

theorem evRc_wordSingle {r : ℕ} (a : Fin r) (c : ℂ)
    (is : List ℕ) (s : ℤ) (w : ℕ) (P Q : RawPoly ℕ)
    (h : evRc a c P = evRc a c Q) :
    evRc a c (wordSingle is s w P) = evRc a c (wordActC is s w Q) := by
  induction is generalizing s w P Q with
  | nil =>
    simp only [wordSingle, wordActC]
    split_ifs
    · exact h
    · rfl
  | cons i is ih =>
    cases is with
    | nil =>
      rw [wordSingle, evRc_fastNormFuel, ← evRc_singleWord, singleWord, singleWord,
        evRc_scaleR, evRc_scaleR, evRc_fActC, evRc_fActC, h]
    | cons j is =>
      rw [wordSingle]
      split_ifs with hp
      · have hz : evRc a c Q = 0 := by rw [← h, hp, evRc_nil]
        rw [evRc_nil, evRc_wordActC a c _ _ _ Q (hz ▸ Submodule.zero_mem _), hz, map_zero]
      · rw [evRc_fastNormFuel, wordActC, evRc_flatMap, evRc_flatMap]
        apply congrArg List.sum
        apply List.map_congr_left
        intro m hm
        split_ifs with hm0
        · rw [evRc_fastNormFuel, evRc_fActC, evRc_fActC, ih _ _ P Q h]
        · apply ih
          rw [evRc_fastNormFuel, evRc_fActC, evRc_fActC, h]

def polySingle (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  fastNormFuel (P.flatMap fun t => Q.flatMap fun u =>
    scaleR u.1 (wordSingle u.2 s (wWtC t.2) [t]))

theorem evRc_polySingle {r : ℕ} (a : Fin r) (c : ℂ)
    (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) :
    evRc a c (polySingle Q s P) = evRc a c (polyActWC Q s P) := by
  rw [polySingle, evRc_fastNormFuel, polyActWC, evRc_flatMap, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [polyActC, evRc_flatMap, evRc_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [evRc_scaleR, evRc_scaleR, evRc_wordSingle a c _ _ _ _ _ rfl]
end VOA.Classification.COne.OrbC2h
