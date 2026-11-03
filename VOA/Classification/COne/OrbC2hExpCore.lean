import VOA.Classification.COne.OrbC2hExpBase
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e
/-- A cached polynomial carries its exact evaluation theorem. -/
structure ExpEntry where
  word : List ℕ
  shift : ℤ
  poly : RawPoly ℕ
  correct : ∀ {r : ℕ} (a : Fin r) (c : ℂ), c*c = ((8:ℚ):ℂ) →
    evRc a c poly = evRc a c (expWordR word shift)


/-- Only explicitly certified entries bypass the recursive evaluator. -/
def expUsing (entries : List ExpEntry) : List ℕ → ℤ → RawPoly ℕ
  | [], s => if 0 ≤ s then schurReducedMemo s.toNat else []
  | i::w, s =>
    match entries.find? (fun e => decide (e.word = i::w ∧ e.shift = s)) with
    | some e => e.poly
    | none => match i with
      | 0 => prependC 0 (expUsing entries w s)
      | i+1 => fastReduce (prependC (i+1) (expUsing entries w s) ++
          scaleR (-1) (prependC 0 (expUsing entries w (s+i+1))))

theorem expUsing_sound (entries : List ExpEntry) {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (w : List ℕ) (s : ℤ) :
    evRc a c (expUsing entries w s) = evRc a c (expWordR w s) := by
  induction w generalizing s with
  | nil =>
    simp only [expUsing, expWordR]
    split_ifs <;> simp only [schurReducedMemo_sound _ _ hc, schurMemo_sound]
  | cons i w ih =>
    cases he : entries.find? (fun e => decide (e.word = i::w ∧ e.shift = s)) with
    | none =>
      rw [expUsing.eq_def]
      dsimp only
      rw [he]
      cases i <;> simp only [expWordR, evRc_normR,
        evRc_fastReduce_of_sq _ _ hc, evRc_append, evRc_scaleR, evRc_prependC, ih]
    | some e =>
      rw [expUsing.eq_def]
      dsimp only
      rw [he]
      have hp := List.find?_some (p := fun e : ExpEntry =>
        decide (e.word = i::w ∧ e.shift = s)) he
      have hh : e.word = i::w ∧ e.shift = s := of_decide_eq_true hp
      rw [← hh.1, ← hh.2]
      exact e.correct a c hc

end VOA.Classification.COne.OrbC2h
