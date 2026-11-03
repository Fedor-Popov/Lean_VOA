import VOA.DeligneAudit.DeligneSectorSparseData

/-! Integer divisor predicates, with unchanged definitions and public names. -/
namespace VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.Sparse

section Range
variable (n : ℕ)

def qRange (L : QV) : Bool := L.all fun t => decide (t.1 < n) && decide (t.2.1 < n)

end Range

def bpow (e : ℕ) : ℤ := ((2 ^ (64 * e) : ℕ) : ℤ)

def keyE (kb : ℕ) (t : ℕ × ℕ × ℤ) : ℕ := t.1 * kb + t.2.1

def encQ (kb : ℕ) (L : QV) : ℤ := (L.map fun t => t.2.2 * bpow (keyE kb t)).sum

def absSum (L : QV) : ℕ := (L.map fun t => t.2.2.natAbs).sum

def encCheck (kb : ℕ) (L : QV) : Bool :=
  (L.all fun t => decide (t.1 < kb) && decide (t.2.1 < kb)) && decide (absSum L < 2 ^ 63) &&
    decide (encQ kb L = 0)

def encLin (kb : ℕ) (tab : ℕ → QV) (target : QV) (C : List (ℕ × ℤ)) : Bool :=
  (target.all fun t => decide (t.1 < kb) && decide (t.2.1 < kb)) &&
    C.all (fun p => (tab p.1).all fun t => decide (t.1 < kb) && decide (t.2.1 < kb)) &&
    decide (absSum target + (C.map fun p => p.2.natAbs * absSum (tab p.1)).sum < 2 ^ 63) &&
    decide (encQ kb target = (C.map fun p => p.2 * encQ kb (tab p.1)).sum)

def rowTrip (br : ℕ → ℕ → SV) (n x : ℕ) : QV :=
  (List.range n).flatMap fun c => (br x c).map fun p => (c, p.1, p.2)

def colTrip (col : ℕ → ℕ → SV) (n x : ℕ) : QV :=
  (List.range n).flatMap fun e => (col x e).map fun p => (p.1, e, p.2)

def colCheck (br : ℕ → ℕ → SV) (col : ℕ → ℕ → SV) (n x : ℕ) : Bool :=
  encCheck n (rowTrip br n x ++ smulQ (-1) (colTrip col n x))

def opAQc (col : ℕ → ℕ → SV) (x : ℕ) (L : QV) : QV :=
  L.flatMap fun t => (col x t.1).map fun p => (p.1, t.2.1, -(p.2 * t.2.2))

def opBQc (col : ℕ → ℕ → SV) (x : ℕ) (L : QV) : QV :=
  L.flatMap fun t => (col x t.2.1).map fun p => (t.1, p.1, -(p.2 * t.2.2))

section Tree
variable (n : ℕ) (col : ℕ → ℕ → SV) (tab : ℕ → QV) (par : ℕ → ℕ × Bool × ℕ × ℕ × ℕ)

def nodeCheckC (i : ℕ) : Bool :=
  let p := par i
  decide (p.1 < i) && decide (p.2.2.1 < n) && qRange n (tab p.1) &&
    decide (p.2.2.2.1 = (par p.1).2.2.2.1 + 1) &&
    decide (p.2.2.2.2 = (par p.1).2.2.2.2 + (if p.2.1 then 1 else 0)) &&
    encCheck n (tab i ++ smulQ (-1)
      (if p.2.1 then opAQc col p.2.2.1 (tab p.1) ++ smulQ (-1) (opBQc col p.2.2.1 (tab p.1))
       else opAQc col p.2.2.1 (tab p.1) ++ opBQc col p.2.2.1 (tab p.1)))

end Tree

end VOA.DeligneAudit.DeligneDivisor
