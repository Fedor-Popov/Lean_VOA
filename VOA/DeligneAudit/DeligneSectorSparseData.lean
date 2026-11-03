import Mathlib.Data.Int.Basic

/-! Integer sparse operations, isolated from the semantic carrier imports.
Definitions are moved unchanged from DeligneSectorSparse. -/
namespace VOA.DeligneAudit.DeligneSector.Sparse

abbrev SV := List (ℕ × ℤ)

def sget (L : SV) (c : ℕ) : ℤ := (L.map fun p => if p.1 = c then p.2 else 0).sum

def smulSV (k : ℤ) (L : SV) : SV := L.map fun q => (q.1, k * q.2)

def zeroCheck (L : SV) : Bool := L.all fun p => sget L p.1 == 0

section Table
variable (n : ℕ) (br : ℕ → ℕ → SV)

def fZ (a b c : ℕ) : ℤ := sget (br a b) c

def rangeCheck : Bool :=
  (List.range n).all fun a => (List.range n).all fun b => (br a b).all fun p => decide (p.1 < n)

def jacVec (a b x : ℕ) : SV :=
  ((br a x).flatMap fun p => smulSV p.2 (br b p.1)) ++
  ((br b x).flatMap fun p => smulSV (-p.2) (br a p.1)) ++
  ((br a b).flatMap fun p => smulSV p.2 (br p.1 x))

def jacCheck : Bool :=
  (List.range n).all fun a => (List.range n).all fun b => (List.range n).all fun x =>
    zeroCheck (jacVec br a b x)

end Table

abbrev QV := List (ℕ × ℕ × ℤ)

def smulQ (k : ℤ) (L : QV) : QV := L.map fun t => (t.1, t.2.1, k * t.2.2)

def orient (L : QV) : QV := L.map fun t => if t.1 ≤ t.2.1 then t else (t.2.1, t.1, t.2.2)

def qget (L : QV) (a b : ℕ) : ℤ := (L.map fun t => if t.1 = a ∧ t.2.1 = b then t.2.2 else 0).sum

def qzeroCheck (L : QV) : Bool := (orient L).all fun t => qget (orient L) t.1 t.2.1 == 0

def adQ (br : ℕ → ℕ → SV) (x : ℕ) (L : QV) : QV :=
  L.flatMap fun t => ((br x t.1).map fun p => (p.1, t.2.1, t.2.2 * p.2)) ++
    ((br x t.2.1).map fun p => (t.1, p.1, t.2.2 * p.2))

section Words
variable (br : ℕ → ℕ → SV)

def slotZ (n : ℕ) (x : ℕ) (v : SV) : SV :=
  (List.range n).map fun y => (y, -(v.map fun p => fZ br x y p.1 * p.2).sum)

def wordZ (n : ℕ) : List ℕ → SV → SV
  | [], v => v
  | (x :: l), v => slotZ br n x (wordZ n l v)

def svRange (n : ℕ) (v : SV) : Bool := v.all fun p => decide (p.1 < n)

end Words

end VOA.DeligneAudit.DeligneSector.Sparse
