/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorRawRelations
import VOA.DeligneAudit.E6Sparse

/-! Original F4 U3 definitions, with no Lie or sector imports. -/
namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.E6Sparse (quadOf certOf)

/-- Relation `b` of `I₂ⁿˢ`. -/
def relQ (b : ℕ) : List (ℕ × ℕ × ℤ) := quadOf (relRaw.getD b [])

/-- The Casimir. -/
def qQ : List (ℕ × ℕ × ℤ) := quadOf qRaw

/-- The U3 check of current `a`. -/
def u3OK (a : ℕ) : Bool :=
  let c := u3Raw.getD a []
  decide (((c.headD 1 : ℕ) : ℤ) ≠ 0) && (certOf c.tail).all (fun t => t.2.2 < 324) &&
    VOA.DeligneAudit.E6Sparse.u3Check relQ qQ a ((c.headD 1 : ℕ) : ℤ) (certOf c.tail)

end VOA.DeligneAudit.DeligneSector.F4
