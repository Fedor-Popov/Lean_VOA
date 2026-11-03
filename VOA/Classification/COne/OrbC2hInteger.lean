import VOA.Classification.COne.OrbC2hQuick
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary OrbC2e

abbrev IntPoly := List (ℤ × List ℕ)

def toRatPoly (P : IntPoly) : RawPoly ℕ := P.map fun t => ((t.1:ℚ), t.2)
noncomputable def iEval {r : ℕ} (a : Fin r) (c : ℂ) (P : IntPoly) := evRc a c (toRatPoly P)

theorem iEval_nil {r : ℕ} (a : Fin r) (c : ℂ) : iEval a c [] = 0 := rfl

theorem iEval_cons {r : ℕ} (a : Fin r) (c : ℂ) (q : ℤ) (w : List ℕ) (P : IntPoly) :
    iEval a c ((q,w)::P) = (q:ℂ) • evalWord (xvc a c) w + iEval a c P := by
  simp [iEval, toRatPoly, evRc_cons]

theorem iEval_append {r : ℕ} (a : Fin r) (c : ℂ) (P Q : IntPoly) :
    iEval a c (P++Q) = iEval a c P + iEval a c Q := by
  simp [iEval, toRatPoly, evRc_append]

theorem iEval_flatMap {r : ℕ} (a : Fin r) (c : ℂ) (P : List α) (f : α → IntPoly) :
    iEval a c (P.flatMap f) = (P.map fun t => iEval a c (f t)).sum := by
  induction P with
  | nil => rfl
  | cons t P ih => simp only [List.flatMap_cons, iEval_append, ih, List.map_cons, List.sum_cons]

def iScale (q : ℤ) (P : IntPoly) : IntPoly := P.map fun t => (q*t.1,t.2)
def iPrepend (j : ℕ) (P : IntPoly) : IntPoly := P.map fun t => (t.1,j::t.2)

theorem iEval_scale {r : ℕ} (a : Fin r) (c : ℂ) (q : ℤ) (P : IntPoly) :
    iEval a c (iScale q P) = (q:ℂ) • iEval a c P := by
  induction P with
  | nil => simp [iScale, iEval_nil]
  | cons t P ih =>
    rcases t with ⟨b,w⟩
    simp only [iScale, List.map_cons, iEval_cons] at *
    rw [ih, Int.cast_mul, mul_smul, smul_add]

theorem iEval_prepend {r : ℕ} (a : Fin r) (c : ℂ) (j : ℕ) (P : IntPoly) :
    iEval a c (iPrepend j P) = xvc a c j * iEval a c P := by
  induction P with
  | nil => simp [iPrepend, iEval_nil]
  | cons t P ih =>
    rcases t with ⟨b,w⟩
    simp only [iPrepend, List.map_cons, iEval_cons, evalWordC_cons] at *
    rw [ih, mul_add, mul_smul_comm]

def iMerge : ℕ → IntPoly → IntPoly → IntPoly
  | 0, P, Q => P++Q
  | _+1, [], Q => Q
  | _+1, P, [] => P
  | n+1, (a,w)::P, (b,v)::Q =>
    match compareWord w v with
    | .lt => (a,w)::iMerge n P ((b,v)::Q)
    | .gt => (b,v)::iMerge n ((a,w)::P) Q
    | .eq => if a+b = 0 then iMerge n P Q else (a+b,w)::iMerge n P Q

theorem iEval_merge {r : ℕ} (a : Fin r) (c : ℂ) (n : ℕ) (P Q : IntPoly) :
    iEval a c (iMerge n P Q) = iEval a c P + iEval a c Q := by
  induction n generalizing P Q with
  | zero => exact iEval_append a c P Q
  | succ n ih =>
    cases P with
    | nil => simp [iMerge, iEval_nil]
    | cons t P =>
      rcases t with ⟨q,w⟩
      cases Q with
      | nil => simp [iMerge, iEval_nil]
      | cons t Q =>
        rcases t with ⟨b,v⟩
        rw [iMerge]
        cases hh : compareWord w v with
        | lt => simp only [iEval_cons, ih]; abel
        | gt => simp only [iEval_cons, ih]; abel
        | eq =>
          have he := (compareWord_eq_iff w v).mp hh
          subst v
          split_ifs with hq
          · rw [ih, iEval_cons, iEval_cons]
            have hz : (q:ℂ)+(b:ℂ) = 0 := by exact_mod_cast hq
            have he : (q:ℂ) = -(b:ℂ) := by linear_combination hz
            rw [he]
            module
          · rw [iEval_cons, ih, iEval_cons, iEval_cons, Int.cast_add, add_smul]
            abel

def iPairs : List IntPoly → List IntPoly
  | [] => []
  | [P] => [P]
  | P::Q::S => iMerge 100000 P Q :: iPairs S

def iMany : ℕ → List IntPoly → IntPoly
  | 0, S => S.flatten
  | _+1, [] => []
  | _+1, [P] => P
  | n+1, P::Q::S => iMany n (iPairs (P::Q::S))

theorem iEval_pairs {r : ℕ} (a : Fin r) (c : ℂ) (S : List IntPoly) :
    ((iPairs S).map (iEval a c)).sum = (S.map (iEval a c)).sum := by
  induction S using iPairs.induct with
  | case1 => rfl
  | case2 P => rfl
  | case3 P Q S ih =>
    simp only [iPairs, List.map_cons, List.sum_cons, iEval_merge, ih]
    abel

theorem iEval_flatten {r : ℕ} (a : Fin r) (c : ℂ) (S : List IntPoly) :
    iEval a c S.flatten = (S.map (iEval a c)).sum := by
  induction S with
  | nil => simp [iEval_nil]
  | cons P S ih => simp [iEval_append, ih]

theorem iEval_many {r : ℕ} (a : Fin r) (c : ℂ) (n : ℕ) (S : List IntPoly) :
    iEval a c (iMany n S) = (S.map (iEval a c)).sum := by
  induction n generalizing S with
  | zero => exact iEval_flatten a c S
  | succ n ih =>
    cases S with
    | nil => simp [iMany, iEval_nil]
    | cons P S =>
      cases S with
      | nil => simp [iMany]
      | cons Q S => rw [iMany, ih, iEval_pairs]

def iNorm (P : IntPoly) : IntPoly :=
  iMany 100000 (P.map fun t => if t.1 = 0 then [] else [(t.1, sortWord t.2)])

theorem iEval_norm {r : ℕ} (a : Fin r) (c : ℂ) (P : IntPoly) :
    iEval a c (iNorm P) = iEval a c P := by
  rw [iNorm, iEval_many, List.map_map]
  induction P with
  | nil => simp [iEval_nil]
  | cons t P ih =>
    rcases t with ⟨q,w⟩
    simp only [List.map_cons, List.sum_cons, iEval_cons]
    rw [ih]
    by_cases hq : q = 0
    · simp [hq, iEval_nil]
    · simp [hq, iEval_cons, iEval_nil, evalWord_sortWord]

def iReduceWord : List ℕ → IntPoly
  | [] => [(1,[])]
  | [i] => [(1,[i])]
  | i::j::w => if i = 0 ∧ j = 0 then iScale 8 (iReduceWord w)
      else iPrepend i (iReduceWord (j::w))

theorem iEval_reduceWord {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) : ∀ w : List ℕ,
    iEval a c (iReduceWord w) = evalWord (xvc a c) w
  | [] => by simp [iReduceWord, iEval_cons, iEval_nil, evalWordC_nil]
  | [i] => by simp [iReduceWord, iEval_cons, iEval_nil]
  | i::j::w => by
    rw [iReduceWord]
    split_ifs with h
    · obtain ⟨rfl,rfl⟩ := h
      rw [iEval_scale, iEval_reduceWord a c hc w, evalWordC_cons, evalWordC_cons]
      simp only [xvc, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, hc]
      norm_num
    · rw [iEval_prepend, iEval_reduceWord a c hc (j::w), evalWordC_cons]
      rfl

def iReduce (P : IntPoly) : IntPoly :=
  iNorm ((iNorm P).flatMap fun t => iScale t.1 (iReduceWord t.2))

theorem iEval_reduce {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c*c = ((8:ℚ):ℂ)) (P : IntPoly) : iEval a c (iReduce P) = iEval a c P := by
  rw [iReduce, iEval_norm, iEval_flatMap]
  have h : ∀ Q : IntPoly,
      (Q.map fun t => iEval a c (iScale t.1 (iReduceWord t.2))).sum = iEval a c Q := by
    intro Q
    induction Q with
    | nil => simp [iEval_nil]
    | cons t Q ih =>
      rcases t with ⟨q,w⟩
      rw [List.map_cons, List.sum_cons, iEval_scale,
        iEval_reduceWord _ _ hc, ih, iEval_cons]
  rw [h, iEval_norm]

end VOA.Classification.COne.OrbC2h
