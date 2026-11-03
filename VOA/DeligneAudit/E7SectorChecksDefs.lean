/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorLinkDefs

/-! Unchanged light definitions shared by the E7 sector checks. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

/-- `θ(h_i)` on the Cartan indices. -/
def thetaH : Fin 133 → ℕ := fun h => if h = 0 then 1 else if h = 1 then 0 else if h = 2 then 0 else if h = 3 then 0 else if h = 4 then 0 else if h = 5 then 0 else if h = 6 then 0 else 0

/-- The string lengths `θ(h_k)` at the simple lowering vectors. -/
def lowExpE7 : Fin 133 → ℕ := fun i => if i = 76 then 1 else if i = 75 then 0 else if i = 74 then 0 else if i = 73 then 0 else if i = 72 then 0 else if i = 71 then 0 else if i = 70 then 0 else 0

/-- `θ` in simple-root coordinates. -/
def thetaV : Fin 7 → ℤ := ![2, 2, 3, 4, 3, 2, 1]

/-- Weight additivity of the table, rows `lo ≤ x < hi`. -/
def wtChunk (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun x => (List.range 133).all fun y =>
    (entry e7T x y).all fun p => decide (p.1 < 133) &&
      (wtL.getD p.1 [] == List.zipWith (· + ·) (wtL.getD x []) (wtL.getD y []))

end VOA.DeligneAudit.DeligneCarrier.E7
