import VOA.Classification.COne.OrbC2hSchur14
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2h
open VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary

def mergePairsFuel (fuel : ℕ) : List (RawPoly ℕ) → List (RawPoly ℕ)
  | [] => []
  | [P] => [P]
  | P::Q::S => mergeRaw fuel P Q :: mergePairsFuel fuel S

theorem evRc_mergePairsFuel {r : ℕ} (a : Fin r) (c : ℂ) (fuel : ℕ)
    (S : List (RawPoly ℕ)) :
    ((mergePairsFuel fuel S).map (evRc a c)).sum = (S.map (evRc a c)).sum := by
  induction S using mergePairsFuel.induct with
  | case1 => rfl
  | case2 P => rfl
  | case3 P Q S ih =>
    simp only [mergePairsFuel, List.map_cons, List.sum_cons, evRc_mergeRaw, ih]
    abel

theorem mergePairsFuel_certificate {r : ℕ} (a : Fin r) (c : ℂ) (fuel : ℕ)
    (S T : List (RawPoly ℕ)) (h : mergePairsFuel fuel S = T) :
    (S.map (evRc a c)).sum = (T.map (evRc a c)).sum := by
  rw [← h, evRc_mergePairsFuel]
end VOA.Classification.COne.OrbC2h
