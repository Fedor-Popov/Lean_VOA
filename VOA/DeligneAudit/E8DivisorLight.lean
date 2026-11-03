/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# Light-import mirrors of the Boolean divisor checks (E₈)

The chunked kernel checks of the E₈ pair comparison import only this file and the data files.
They do not import `DeligneDivisorCol`, whose import chain costs about 4 GB of RSS per process.

Each definition here is a verbatim copy of a generic Boolean check:
- `qget`, `smulQ`, `qRange` from `DeligneSectorSparse` and `DeligneDivisorSparse`;
- `bpow`, `keyE`, `encQ`, `absSum`, `encCheck`, `encLin` from `DeligneDivisorEnc`;
- `rowTrip`, `colTrip`, `colCheck`, `opAQc`, `opBQc`, `nodeCheckC` from `DeligneDivisorCol`.

`E8Divisor` proves each copy equal to its original by `rfl` (`*_eq` lemmas) before using the generic
soundness theorems.
-/

namespace VOA.DeligneAudit.DeligneDivisor.E8

/-- Sparse vectors. -/
abbrev SVL := List (ℕ × ℤ)

/-- Sparse two-slot tables. -/
abbrev QVL := List (ℕ × ℕ × ℤ)

/-- Copy of `Sparse.qget`. -/
def qgetL (L : QVL) (a b : ℕ) : ℤ := (L.map fun t => if t.1 = a ∧ t.2.1 = b then t.2.2 else 0).sum

/-- Copy of `Sparse.smulQ`. -/
def smulQL (k : ℤ) (L : QVL) : QVL := L.map fun t => (t.1, t.2.1, k * t.2.2)

/-- Copy of `DeligneDivisor.qRange`. -/
def qRangeL (n : ℕ) (L : QVL) : Bool := L.all fun t => decide (t.1 < n) && decide (t.2.1 < n)

/-- Copy of `bpow`. -/
def bpowL (e : ℕ) : ℤ := ((2 ^ (64 * e) : ℕ) : ℤ)

/-- Copy of `keyE`. -/
def keyEL (kb : ℕ) (t : ℕ × ℕ × ℤ) : ℕ := t.1 * kb + t.2.1

/-- Copy of `encQ`. -/
def encQL (kb : ℕ) (L : QVL) : ℤ := (L.map fun t => t.2.2 * bpowL (keyEL kb t)).sum

/-- Copy of `absSum`. -/
def absSumL (L : QVL) : ℕ := (L.map fun t => t.2.2.natAbs).sum

/-- Copy of `encCheck`. -/
def encCheckL (kb : ℕ) (L : QVL) : Bool :=
  (L.all fun t => decide (t.1 < kb) && decide (t.2.1 < kb)) && decide (absSumL L < 2 ^ 63) &&
    decide (encQL kb L = 0)

/-- Copy of `encLin`. -/
def encLinL (kb : ℕ) (tab : ℕ → QVL) (target : QVL) (C : List (ℕ × ℤ)) : Bool :=
  (target.all fun t => decide (t.1 < kb) && decide (t.2.1 < kb)) &&
    C.all (fun p => (tab p.1).all fun t => decide (t.1 < kb) && decide (t.2.1 < kb)) &&
    decide (absSumL target + (C.map fun p => p.2.natAbs * absSumL (tab p.1)).sum < 2 ^ 63) &&
    decide (encQL kb target = (C.map fun p => p.2 * encQL kb (tab p.1)).sum)

/-- Copy of `rowTrip`. -/
def rowTripL (br : ℕ → ℕ → SVL) (n x : ℕ) : QVL :=
  (List.range n).flatMap fun c => (br x c).map fun p => (c, p.1, p.2)

/-- Copy of `colTrip`. -/
def colTripL (col : ℕ → ℕ → SVL) (n x : ℕ) : QVL :=
  (List.range n).flatMap fun e => (col x e).map fun p => (p.1, e, p.2)

/-- Copy of `colCheck`. -/
def colCheckL (br : ℕ → ℕ → SVL) (col : ℕ → ℕ → SVL) (n x : ℕ) : Bool :=
  encCheckL n (rowTripL br n x ++ smulQL (-1) (colTripL col n x))

/-- Copy of `opAQc`. -/
def opAQcL (col : ℕ → ℕ → SVL) (x : ℕ) (L : QVL) : QVL :=
  L.flatMap fun t => (col x t.1).map fun p => (p.1, t.2.1, -(p.2 * t.2.2))

/-- Copy of `opBQc`. -/
def opBQcL (col : ℕ → ℕ → SVL) (x : ℕ) (L : QVL) : QVL :=
  L.flatMap fun t => (col x t.2.1).map fun p => (t.1, p.1, -(p.2 * t.2.2))

/-- Copy of `nodeCheckC`. -/
def nodeCheckCL (n : ℕ) (col : ℕ → ℕ → SVL) (tab : ℕ → QVL) (par : ℕ → ℕ × Bool × ℕ × ℕ × ℕ)
    (i : ℕ) : Bool :=
  let p := par i
  decide (p.1 < i) && decide (p.2.2.1 < n) && qRangeL n (tab p.1) &&
    decide (p.2.2.2.1 = (par p.1).2.2.2.1 + 1) &&
    decide (p.2.2.2.2 = (par p.1).2.2.2.2 + (if p.2.1 then 1 else 0)) &&
    encCheckL n (tab i ++ smulQL (-1)
      (if p.2.1 then opAQcL col p.2.2.1 (tab p.1) ++ smulQL (-1) (opBQcL col p.2.2.1 (tab p.1))
       else opAQcL col p.2.2.1 (tab p.1) ++ opBQcL col p.2.2.1 (tab p.1)))

end VOA.DeligneAudit.DeligneDivisor.E8
