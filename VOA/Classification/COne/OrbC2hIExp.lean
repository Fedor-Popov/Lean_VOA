import VOA.Classification.COne.OrbC2hISchur
import VOA.Classification.COne.OrbC2hIBucket
import VOA.Classification.COne.OrbC2hExpCache
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e

/-- Exponential recursion with one common denominator and integer arithmetic. -/
def iExp : List ℕ → ℤ → IntPoly
  | [], s => if 0 ≤ s then iSchurMemo s.toNat else []
  | 0::w, s => iPrepend 0 (iExp w s)
  | (i+1)::w, s => iAddReduced (iPrepend (i+1) (iExp w s))
      (iScale (-1) (iPrepend 0 (iExp w (s+i+1))))

theorem iExp_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (w : List ℕ) (s : ℤ)
    (hn : s + (w.sum:ℤ) ≤ 22) :
    iEval a c (iExp w s) = (expDen:ℂ) • evRc a c (expWordR w s) := by
  induction w generalizing s with
  | nil =>
    rw [iExp, expWordR]
    split_ifs with hs
    · have hns : s ≤ 22 := by simpa only [List.sum_nil, Nat.cast_zero, add_zero] using hn
      exact iSchurMemo_sound a c hc _ (by omega)
    · simp [iEval_nil, evRc_nil]
  | cons i w ih =>
    cases i with
    | zero =>
      simp only [List.sum_cons, Nat.cast_add, Nat.cast_zero, zero_add] at hn
      rw [iExp, expWordR, iEval_prepend, evRc_prependC, ih s hn, mul_smul_comm]
    | succ i =>
      simp only [List.sum_cons, Nat.cast_add, Nat.cast_succ] at hn
      have h0 : s + (w.sum:ℤ) ≤ 22 := by omega
      have h1 : s + i + 1 + (w.sum:ℤ) ≤ 22 := by omega
      simp only [iExp, expWordR, iEval_addReduced _ _ hc, iEval_scale,
        iEval_prepend, evRc_normR, evRc_append, evRc_scaleR, evRc_prependC]
      rw [ih s h0, ih (s+i+1) h1]
      simp only [mul_smul_comm, Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one,
        neg_one_smul, smul_add, smul_neg]

/-- Outside the certified finite range, retain the unrestricted evaluator. -/
def expInteger (w : List ℕ) (s : ℤ) : RawPoly ℕ :=
  if s + (w.sum:ℤ) ≤ 22 then
    scaleR (1/(expDen:ℚ)) (toRatPoly (iExp w s))
  else expCached w s

theorem expInteger_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (w : List ℕ) (s : ℤ) :
    evRc a c (expInteger w s) = evRc a c (expWordR w s) := by
  rw [expInteger]
  split_ifs with hn
  · rw [evRc_scaleR]
    change (((1/(expDen:ℚ):ℚ):ℂ)) • iEval a c (iExp w s) = _
    rw [iExp_sound _ _ hc _ _ hn, smul_smul]
    have hq : (((1/(expDen:ℚ):ℚ):ℂ)) * (expDen:ℂ) = 1 := by norm_num [expDen]
    rw [hq, one_smul]
  · exact expCached_sound a c hc w s

end VOA.Classification.COne.OrbC2h
