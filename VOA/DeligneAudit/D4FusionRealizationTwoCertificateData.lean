/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.List.Defs
import VOA.DeligneAudit.D4FusionRealizationTwoIntegerData

/-! Integer-only operations for the two-site certificate. Computational
leaves import no current module, tensor product, or character construction. -/
namespace VOA.DeligneAudit.D4Two.Certificate

/-- Sparse lists may contain repeated coordinates. -/
def coeff (v : SV) (i : ℕ) : ℤ :=
  (v.map fun t => if t.1 = i then t.2 else 0).sum

def scale (a : ℤ) (v : SV) : SV := v.map fun t => (t.1, a * t.2)

def zeroCheck (v : SV) : Bool := v.all fun t => coeff v t.1 == 0

def eqCheck (v w : SV) : Bool := zeroCheck (v ++ scale (-1) w)

def zeroOnCheck (coordinates : List ℕ) (v : SV) : Bool :=
  (v.all fun t => t.1 ∈ coordinates) &&
    coordinates.all fun i => coeff v i == 0

def rangeCheck (n : ℕ) (v : SV) : Bool := v.all fun t => t.1 < n

/-- The pairing of an integer row with an integer vector. -/
def dot (row v : SV) : ℤ := (row.map fun t => t.2 * coeff v t.1).sum

/-- Apply columns of an integer matrix to an integer vector. -/
def applyColumns (cols : ℕ → SV) (v : SV) : SV :=
  v.flatMap fun t => scale t.2 (cols t.1)

/-- The standard flattening uses the coadjoint coordinates followed by the
trivial coordinate at each site. -/
def pairColumn (n : ℕ) (cols : ℕ → SV) (c k ij : ℕ) : SV :=
  let width := n + 1
  let i := ij / width
  let j := ij % width
  let left := if k = 0 then (cols i).map fun t => (t.1 * width + j, t.2)
    else if k = 1 ∧ i = c then [(n * width + j, 1)] else []
  let right := (cols j).map fun t => (i * width + t.1, t.2)
  let tangent := if j = c then [(i * width + n, (k : ℤ))] else []
  left ++ right ++ tangent

/-- One checked parent step; entry zero is checked separately against the
actual tensor generator. -/
def stepCheck (n : ℕ) (cols : ℕ → ℕ → SV) (entries : List Entry) (i : ℕ) : Bool :=
  let e := entries.getD i default
  let p := entries.getD e.parent default
  e.parent < i && e.color < n && e.level == p.level + e.mode &&
    eqCheck e.vector (applyColumns (pairColumn n (cols e.color) e.color e.mode) p.vector)

/-- A same-block dual check; off-block values are handled by disjoint
integer coordinate weights. -/
def dualCheck (entries : List Entry) (i j : ℕ) : Bool :=
  let e := entries.getD i default
  dot e.dual (entries.getD j default).vector == if i = j then e.denominator else 0

/-- A low-level action coefficient is excluded by its exact dual row. -/
def actionCheck (n : ℕ) (cols : ℕ → ℕ → SV) (entries : List Entry)
    (c k i j : ℕ) : Bool :=
  let e := entries.getD i default
  let d := entries.getD j default
  dot d.dual (applyColumns (pairColumn n (cols c) c k) e.vector) == 0

end VOA.DeligneAudit.D4Two.Certificate
