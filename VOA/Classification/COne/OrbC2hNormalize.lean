import VOA.Classification.COne.OrbC2hEvaluator
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary

/-- Structural merge. Exhausting the fuel retains all terms, so soundness is unconditional. -/
def mergeRaw : ℕ → RawPoly ℕ → RawPoly ℕ → RawPoly ℕ
  | 0, P, Q => P ++ Q
  | _+1, [], Q => Q
  | _+1, P, [] => P
  | n+1, (a,w)::P, (b,v)::Q =>
    match compareWord w v with
    | .lt => (a,w) :: mergeRaw n P ((b,v)::Q)
    | .gt => (b,v) :: mergeRaw n ((a,w)::P) Q
    | .eq => if a+b = 0 then mergeRaw n P Q else (a+b,w)::mergeRaw n P Q

def mergePoly (P Q : RawPoly ℕ) : RawPoly ℕ := mergeRaw (P.length+Q.length) P Q

theorem evRc_mergeRaw {r : ℕ} (a : Fin r) (c : ℂ) (n : ℕ) (P Q : RawPoly ℕ) :
    evRc a c (mergeRaw n P Q) = evRc a c P + evRc a c Q := by
  induction n generalizing P Q with
  | zero => exact evRc_append a c P Q
  | succ n ih =>
    cases P with
    | nil => simp [mergeRaw, evRc_nil]
    | cons t P =>
      rcases t with ⟨q,w⟩
      cases Q with
      | nil => simp [mergeRaw, evRc_nil]
      | cons t Q =>
        rcases t with ⟨b,v⟩
        rw [mergeRaw]
        cases hh : compareWord w v with
        | lt => simp only [evRc_cons, ih]; abel
        | gt => simp only [evRc_cons, ih]; abel
        | eq =>
          have he := (compareWord_eq_iff w v).mp hh
          subst v
          split_ifs with hq
          · rw [ih, evRc_cons, evRc_cons]
            have hz : (q:ℂ)+b = 0 := by exact_mod_cast hq
            have he : (q:ℂ) = -(b:ℂ) := by linear_combination hz
            rw [he]
            module
          · rw [evRc_cons, ih, evRc_cons, evRc_cons, Rat.cast_add, add_smul]
            abel

def mergePairs : List (RawPoly ℕ) → List (RawPoly ℕ)
  | [] => []
  | [P] => [P]
  | P::Q::S => mergePoly P Q :: mergePairs S

def mergeMany : ℕ → List (RawPoly ℕ) → RawPoly ℕ
  | 0, S => S.flatten
  | _+1, [] => []
  | _+1, [P] => P
  | n+1, P::Q::S => mergeMany n (mergePairs (P::Q::S))

theorem evRc_mergePairs {r : ℕ} (a : Fin r) (c : ℂ) (S : List (RawPoly ℕ)) :
    ((mergePairs S).map (evRc a c)).sum = (S.map (evRc a c)).sum := by
  induction S using mergePairs.induct with
  | case1 => rfl
  | case2 P => rfl
  | case3 P Q S ih =>
    simp only [mergePairs, List.map_cons, List.sum_cons, mergePoly, evRc_mergeRaw, ih]
    abel

theorem evRc_flatten {r : ℕ} (a : Fin r) (c : ℂ) (S : List (RawPoly ℕ)) :
    evRc a c S.flatten = (S.map (evRc a c)).sum := by
  induction S with
  | nil => simp [evRc_nil]
  | cons P S ih => simp [evRc_append, ih]

theorem evRc_mergeMany {r : ℕ} (a : Fin r) (c : ℂ) (n : ℕ) (S : List (RawPoly ℕ)) :
    evRc a c (mergeMany n S) = (S.map (evRc a c)).sum := by
  induction n generalizing S with
  | zero => exact evRc_flatten a c S
  | succ n ih =>
    cases S with
    | nil => simp [mergeMany, evRc_nil]
    | cons P S =>
      cases S with
      | nil => simp [mergeMany]
      | cons Q S => rw [mergeMany, ih, evRc_mergePairs]

def fastNorm (P : RawPoly ℕ) : RawPoly ℕ :=
  mergeMany P.length (P.map fun t => if t.1 = 0 then [] else [(t.1, sortWord t.2)])

theorem evRc_fastNorm {r : ℕ} (a : Fin r) (c : ℂ) (P : RawPoly ℕ) :
    evRc a c (fastNorm P) = evRc a c P := by
  rw [fastNorm, evRc_mergeMany, List.map_map]
  induction P with
  | nil => simp [evRc_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    simp only [List.map_cons, List.sum_cons, evRc_cons]
    rw [ih]
    by_cases hq : q = 0
    · simp [hq, evRc_nil]
    · simp [hq, evRc_cons, evRc_nil, evalWord_sortWord]

end VOA.Classification.COne.OrbC2h
