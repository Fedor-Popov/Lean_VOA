import VOA.Classification.COne.OrbIcoZSymbolic

/-! A kernel-reducible rational-list backend for two-variable polynomials. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd Polynomial
abbrev BP := List PL
abbrev RawSym := List (ℕ × BP)

def qp : PL → ℚ[X]
  | [] => 0
  | x :: p => Polynomial.C x + Polynomial.X * qp p

def bp : BP → Biv
  | [] => 0
  | p :: r => Polynomial.C (qp p) + Polynomial.X * bp r

theorem qp_add : ∀ p q : PL, qp (paddL p q) = qp p + qp q
  | [], q => by simp [paddL, qp]
  | p, [] => by cases p <;> simp [paddL, qp]
  | x :: p, y :: q => by
    simp only [paddL, qp, qp_add, Polynomial.C_add]
    ring

theorem qp_scale (c : ℚ) : ∀ p : PL, qp (pscaleL c p) = Polynomial.C c * qp p
  | [] => by simp [pscaleL, qp]
  | x :: p => by
    simp only [pscaleL, List.map_cons, qp, Polynomial.C_mul]
    have ih := qp_scale c p
    simp only [pscaleL] at ih
    rw [ih]
    ring

theorem qp_mul : ∀ p q : PL, qp (pmulL p q) = qp p * qp q
  | [], q => by simp [pmulL, qp]
  | x :: p, q => by
    simp only [pmulL, qp_add, qp_scale, qp, qp_mul, Polynomial.C_0]
    ring

private theorem qp_trim_aux : ∀ p : PL,
    qp ((p.dropWhile (· = 0)).reverse) = qp p.reverse := by
  intro p
  induction p with
  | nil => rfl
  | cons x p ih =>
    by_cases hx : x = 0
    · subst hx
      rw [List.dropWhile_cons_of_pos (by simp), ih, List.reverse_cons]
      generalize p.reverse = r
      induction r with
      | nil => simp [qp]
      | cons y r ihr => simp only [List.cons_append, qp, ihr]
    · rw [List.dropWhile_cons_of_neg (by simpa using hx)]

theorem qp_trim (p : PL) : qp (ptrim p) = qp p := by
  unfold ptrim
  have h := qp_trim_aux p.reverse
  simpa only [List.reverse_reverse] using h

def badd : BP → BP → BP
  | [], q => q
  | p, [] => p
  | p :: r, q :: s => paddL p q :: badd r s

def bscale (p : PL) (r : BP) : BP := r.map (pmulL p)

def bmul : BP → BP → BP
  | [], _ => []
  | p :: r, s => badd (bscale p s) ([] :: bmul r s)

def bshift (n : ℕ) : BP → BP
  | [] => []
  | p :: r => badd [p] (bmul [[-(n : ℚ)], [1]] (bshift n r))

theorem bp_add : ∀ p q : BP, bp (badd p q) = bp p + bp q
  | [], q => by simp [badd, bp]
  | p, [] => by cases p <;> simp [badd, bp]
  | p :: r, q :: s => by
    simp only [badd, bp, qp_add, Polynomial.C_add, bp_add]
    ring

theorem bp_scale (p : PL) : ∀ r : BP,
    bp (bscale p r) = Polynomial.C (qp p) * bp r
  | [] => by simp [bscale, bp]
  | q :: r => by
    simp only [bscale, List.map_cons, bp, qp_mul, Polynomial.C_mul]
    have ih := bp_scale p r
    simp only [bscale] at ih
    rw [ih]
    ring

theorem bp_mul : ∀ p q : BP, bp (bmul p q) = bp p * bp q
  | [], q => by simp [bmul, bp]
  | p :: r, q => by
    simp only [bmul, bp_add, bp_scale, bp, bp_mul, qp, Polynomial.C_0]
    ring

theorem bp_shift (n : ℕ) : ∀ p : BP, bp (bshift n p) = shiftB n (bp p)
  | [] => by simp [bshift, shiftB, bp]
  | p :: r => by
    rw [bshift, bp_add, bp_mul, bp_shift n r]
    simp only [bp, qp, Polynomial.C_0, Polynomial.C_1]
    simp only [shiftB, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp]
    simp only [Polynomial.C_neg, Polynomial.C_1]
    ring_nf
    simp [sub_eq_add_neg]

def rawScale (p : BP) (r : RawSym) : RawSym := r.map fun q => (q.1, bmul p q.2)
def rawShift (n : ℕ) (r : RawSym) : RawSym := r.map fun q => (n + q.1, bshift n q.2)
def rawInsert (p : ℕ × BP) : RawSym → RawSym
  | [] => [p]
  | q :: r => if p.1 = q.1 then (q.1, badd p.2 q.2) :: r else q :: rawInsert p r
def rawNorm : RawSym → RawSym
  | [] => []
  | p :: r => rawInsert p (rawNorm r)

def rawFactor (n : ℕ) (d : ℚ) : BP :=
  [[(-1)^n * d, (-1)^n * ((n : ℚ) - 1)], [-(-1)^n]]
def rawSecond (n : ℕ) : BP := [[35 * ((n : ℚ) - 1)], [1]]

def rawWord : List ℕ → RawSym
  | [] => [(0, [[1]])]
  | n :: w => rawNorm
      (rawScale (rawFactor n (71 + w.sum)) (rawWord w) ++
        rawScale (rawSecond n) (rawShift n (rawWord w)))
def rawVector : VVec → RawSym
  | [] => []
  | p :: v => rawNorm (rawScale [[p.1]] (rawWord p.2) ++ rawVector v)

def symMap (r : RawSym) : SymRel := r.map fun p => (p.1, bp p.2)

theorem symMap_append (r s : RawSym) : symMap (r ++ s) = symMap r ++ symMap s := by
  simp [symMap]

theorem symMap_scale (p : BP) (r : RawSym) :
    symMap (rawScale p r) = scaleSym (bp p) (symMap r) := by
  simp [symMap, rawScale, scaleSym, List.map_map, Function.comp_def, bp_mul]

theorem symMap_shift (n : ℕ) (r : RawSym) :
    symMap (rawShift n r) = shiftSym n (symMap r) := by
  simp [symMap, rawShift, shiftSym, List.map_map, Function.comp_def, bp_shift]

theorem symMap_insert (p : ℕ × BP) : ∀ r : RawSym,
    symMap (rawInsert p r) = insertSym (p.1, bp p.2) (symMap r)
  | [] => rfl
  | q :: r => by
    simp only [rawInsert, symMap, List.map_cons, insertSym]
    split_ifs with h
    · simp only [List.map_cons, bp_add]
    · change (q.1, bp q.2) :: symMap (rawInsert p r) = _
      rw [symMap_insert p r]
      rfl

theorem symMap_norm : ∀ r : RawSym, symMap (rawNorm r) = normalizeSym (symMap r)
  | [] => rfl
  | p :: r => by
    rw [rawNorm, symMap_insert, symMap_norm]
    rfl

theorem bp_rawFactor (n : ℕ) (d : ℚ) : bp (rawFactor n d) = symFactor n d := by
  simp [rawFactor, bp, qp, symFactor, Polynomial.C_add, Polynomial.C_mul,
    Polynomial.C_sub, Polynomial.C_neg, Polynomial.C_pow]
  ring

theorem bp_rawSecond (n : ℕ) : bp (rawSecond n) = symSecond n := by
  simp [rawSecond, bp, qp, symSecond]

theorem symMap_word : ∀ w : List ℕ, symMap (rawWord w) = symWord w
  | [] => by simp [rawWord, symWord, symMap, bp, qp]
  | n :: w => by
    rw [rawWord, symMap_norm, symMap_append, symMap_scale, symMap_scale, symMap_shift,
      symMap_word, bp_rawFactor, bp_rawSecond, symWord]

theorem symMap_vector : ∀ v : VVec, symMap (rawVector v) = symVector v
  | [] => rfl
  | p :: v => by
    rw [rawVector, symMap_norm, symMap_append, symMap_scale, symMap_word,
      symMap_vector, symVector]
    simp [bp, qp]

end VOA.Classification.COne.OrbIcoZ
