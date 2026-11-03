/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SCLie
import VOA.DeligneAudit.E6Sparse

/-!
# Computable sparse operations for the E₆ sector checks (light imports)

`qInRange` and `adS` (the coadjoint image of a sparse quadratic), used by the kernel checks of
`E6SectorStab*`; their meaning is proved in `E6SectorSparse` (`adDer_quadP`).
-/

namespace VOA.DeligneAudit.E6SectorSparse

open VOA.AffineGeneral.SCLie

/-- All indices of a sparse quadratic are `< N`. -/
def qInRange (N : ℕ) (l : List (ℕ × ℕ × ℤ)) : Bool := l.all fun t => t.1 < N && t.2.1 < N

/-- The coadjoint image of a sparse quadratic. -/
def adS (T : Table) (x : ℕ) (l : List (ℕ × ℕ × ℤ)) : List (ℕ × ℕ × ℤ) :=
  l.flatMap fun t => ((entry T x t.1).map fun p => (p.1, t.2.1, t.2.2 * p.2)) ++
    ((entry T x t.2.1).map fun p => (t.1, p.1, t.2.2 * p.2))

/-- The coadjoint operator `slotA x` on a sparse vector, as a dense list over `y < N`. -/
def slotS (T : Table) (N : ℕ) (x : ℕ) (l : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  ((List.range N).map fun y => (y, -(l.map fun p => p.2 * coef (entry T x y) p.1).sum)).filter
    fun p => p.2 != 0

/-- Coadjoint words on sparse vectors. -/
def wordS (T : Table) (N : ℕ) : List ℕ → List (ℕ × ℤ) → List (ℕ × ℤ)
  | [], v => v
  | x :: l, v => slotS T N x (wordS T N l v)

end VOA.DeligneAudit.E6SectorSparse
