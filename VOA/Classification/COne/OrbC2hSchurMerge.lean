import VOA.Classification.COne.OrbC2hSchurSmall
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary

def sortRaw (P : RawPoly ℕ) : RawPoly ℕ := P.map fun t => (t.1, sortWord t.2)

theorem evRc_sortRaw {r : ℕ} (a : Fin r) (c : ℂ) (P : RawPoly ℕ) :
    evRc a c (sortRaw P) = evRc a c P := by
  induction P with
  | nil => rfl
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    simp only [sortRaw, List.map_cons, evRc_cons, evalWord_sortWord]
    exact congrArg (_ + ·) ih

theorem mergePairs_certificate {r : ℕ} (a : Fin r) (c : ℂ)
    (S T : List (RawPoly ℕ)) (h : mergePairs S = T) :
    (S.map (evRc a c)).sum = (T.map (evRc a c)).sum := by
  rw [← h, evRc_mergePairs]
end VOA.Classification.COne.OrbC2h
