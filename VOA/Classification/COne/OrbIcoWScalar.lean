import VOA.Classification.COne.OrbIcoWJetApprox

/-! Actual complex-valued width-six BSA coefficient recursion.
The rational jet recursion is its finite continuous-remainder evaluation. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoW

def scalarBracket (h K : ℂ) (n q r j : ℕ) : ℂ :=
  (((r-j : ℕ) : ℂ)+1)*h-K+(j : ℂ)-2*((n+q : ℕ) : ℂ)

def scalarSource (h K : ℂ) (n r : ℕ) (A : List (List ℂ)) : List ℂ :=
  (List.range 7).map fun q => ((List.range r).map fun j =>
    (-1 : ℂ)^(r-j)*scalarBracket h K n q r j*((((A[j]?).getD [])[q]?).getD 0) +
      (if r-j=2 ∧ 0<q then (((A[j]?).getD [])[q-1]?).getD 0 else 0)).sum

def scalarStep (h K t : ℂ) (n r : ℕ) (A : List (List ℂ)) : List ℂ :=
  (scalarSource h K n r A).map fun a => -t/((r : ℂ)*(13-(r : ℂ)))*a

def scalarRows (h K t : ℂ) (n : ℕ) : ℕ → List (List ℂ)
  | 0 => [(List.range 7).map fun q => if q=0 then 1 else 0]
  | r+1 => let A := scalarRows h K t n r; A ++ [scalarStep h K t n (r+1) A]

def scalarWidth (h K t : ℂ) (n q : ℕ) : ℂ :=
  (((scalarSource h K n 13 (scalarRows h K t n 12))[q]?).getD 0)

def widthH (t : ℂ) : ℂ := 42/t-6

def widthAt (self : Bool) (n q : ℕ) (t : ℂ) : ℂ :=
  scalarWidth (widthH t) (if self then widthH t else 0) t n q


@[simp] theorem scalarSource_length (h K : ℂ) (n r : ℕ) (A : List (List ℂ)) :
    (scalarSource h K n r A).length=7 := by simp [scalarSource]

@[simp] theorem scalarStep_length (h K t : ℂ) (n r : ℕ) (A : List (List ℂ)) :
    (scalarStep h K t n r A).length=7 := by simp [scalarStep]

@[simp] theorem scalarRows_length (h K t : ℂ) (n r : ℕ) :
    (scalarRows h K t n r).length=r+1 := by
  induction r with
  | zero => simp [scalarRows]
  | succ r ih => simp [scalarRows,ih]

theorem scalarRows_earlier (h K t : ℂ) (n r j : ℕ) (hj : j≤r) :
    ((scalarRows h K t n r)[j]?).getD [] = ((scalarRows h K t n j)[j]?).getD [] := by
  induction r generalizing j with
  | zero =>
    have he : j=0 := by omega
    subst j
    rfl
  | succ r ih =>
    by_cases hjr : j≤r
    · rw [scalarRows,List.getElem?_append_left (by rw [scalarRows_length]; omega)]
      exact ih j hjr
    · have he : j=r+1 := by omega
      rw [he]

theorem scalarRows_last (h K t : ℂ) (n r : ℕ) :
    ((scalarRows h K t n (r+1))[r+1]?).getD [] =
      scalarStep h K t n (r+1) (scalarRows h K t n r) := by
  simp [scalarRows,List.getElem?_append,scalarRows_length]

theorem scalarRows_zero (h K t : ℂ) (n q : ℕ) (hq : q<7) :
    ((((scalarRows h K t n 0)[0]?).getD [])[q]?).getD 0 = if q=0 then 1 else 0 := by
  simp [scalarRows,List.getElem?_map,List.getElem?_range hq]

theorem scalarRows_row_length (h K t : ℂ) (n r j : ℕ) (hj : j≤r) :
    (((scalarRows h K t n r)[j]?).getD []).length=7 := by
  rw [scalarRows_earlier h K t n r j hj]
  cases j with
  | zero => simp [scalarRows]
  | succ j => rw [scalarRows_last]; exact scalarStep_length h K t n (j+1) _

end VOA.Classification.COne.OrbIcoW
