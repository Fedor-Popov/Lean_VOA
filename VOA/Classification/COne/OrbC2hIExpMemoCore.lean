import VOA.Classification.COne.OrbC2hIExp
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e

structure IExpEntry where
  word : List ℕ
  shift : ℤ
  poly : IntPoly
  correct : ∀ {r : ℕ} (a : Fin r) (c : ℂ), c*c = ((8:ℚ):ℂ) →
    iEval a c poly = (expDen:ℂ) • evRc a c (expWordR word shift)

def iExpUsing (entries : List IExpEntry) : List ℕ → ℤ → IntPoly
  | [], s => if 0 ≤ s then iSchurMemo s.toNat else []
  | i::w, s =>
    match entries.find? (fun e => decide (e.word = i::w ∧ e.shift = s)) with
    | some e => e.poly
    | none => match i with
      | 0 => iPrepend 0 (iExpUsing entries w s)
      | i+1 => iAddReduced (iPrepend (i+1) (iExpUsing entries w s))
          (iScale (-1) (iPrepend 0 (iExpUsing entries w (s+i+1))))

theorem iExpUsing_sound (entries : List IExpEntry) {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (w : List ℕ) (s : ℤ)
    (hn : s + (w.sum:ℤ) ≤ 22) :
    iEval a c (iExpUsing entries w s) = (expDen:ℂ) • evRc a c (expWordR w s) := by
  induction w generalizing s with
  | nil =>
    rw [iExpUsing, expWordR]
    split_ifs with hs
    · have hns : s ≤ 22 := by simpa only [List.sum_nil, Nat.cast_zero, add_zero] using hn
      exact iSchurMemo_sound a c hc _ (by omega)
    · simp [iEval_nil, evRc_nil]
  | cons i w ih =>
    cases he : entries.find? (fun e => decide (e.word = i::w ∧ e.shift = s)) with
    | none =>
      rw [iExpUsing.eq_def]
      dsimp only
      rw [he]
      cases i with
      | zero =>
        simp only [List.sum_cons, Nat.cast_add, Nat.cast_zero, zero_add] at hn
        rw [expWordR, iEval_prepend, evRc_prependC, ih s hn, mul_smul_comm]
      | succ i =>
        simp only [List.sum_cons, Nat.cast_add, Nat.cast_succ] at hn
        have h0 : s + (w.sum:ℤ) ≤ 22 := by omega
        have h1 : s + i + 1 + (w.sum:ℤ) ≤ 22 := by omega
        simp only [expWordR, iEval_addReduced _ _ hc, iEval_scale,
          iEval_prepend, evRc_normR, evRc_append, evRc_scaleR, evRc_prependC]
        rw [ih s h0, ih (s+i+1) h1]
        simp only [mul_smul_comm, Int.cast_neg, Int.cast_one, Rat.cast_neg, Rat.cast_one,
          neg_one_smul, smul_add, smul_neg]
    | some e =>
      rw [iExpUsing.eq_def]
      dsimp only
      rw [he]
      have hp := List.find?_some (p := fun e : IExpEntry =>
        decide (e.word = i::w ∧ e.shift = s)) he
      have hh : e.word = i::w ∧ e.shift = s := of_decide_eq_true hp
      rw [← hh.1, ← hh.2]
      exact e.correct a c hc
end VOA.Classification.COne.OrbC2h
