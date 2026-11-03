/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2SectorTables
import VOA.DeligneAudit.E6SectorDefs

/-!
# `G₂` presentation: propagation steps (Boolean checks)

The relations are a BFS from `P₀` under the lowering generators `F = [4, 13]`, unnormalized,
so every `P_k` (`k ≥ 1`) is `ad(F_i) P_j` exactly for its BFS parent `j < k`. `g2Steps` lists `(g, j, k)`
(recovered from the tables outside Lean), `stepOK` checks `ad(g) P_j - P_k = 0` as a sparse quadratic.
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneSector.G2

open VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse

/-- The propagation steps `(g, j, k)`: `P_k = ad(g) P_j`. -/
def g2Steps : List (ℕ × ℕ × ℕ) := [(4, 0, 1), (4, 1, 2), (13, 1, 3), (13, 2, 4), (4, 3, 5),
  (4, 4, 6), (13, 4, 7), (4, 5, 8), (4, 6, 9), (13, 6, 10), (13, 8, 11), (13, 9, 12), (4, 10, 13),
  (4, 11, 14), (4, 12, 15), (13, 12, 16), (4, 13, 17), (4, 15, 18), (13, 15, 19), (13, 17, 20),
  (13, 18, 21), (4, 19, 22), (4, 21, 23), (13, 21, 24), (13, 23, 25), (4, 25, 26)]

/-- One step: `ad(g) P_j = P_k`, `j < k < 27`, `g < 14`. -/
def stepOK (st : ℕ × ℕ × ℕ) : Bool :=
  decide (st.1 < 14) && decide (st.2.1 < st.2.2) && decide (st.2.2 < 27) &&
    quadZero (adS VOA.AffineGeneral.SCLie.g2T st.1 (relQ st.2.1) ++ scaleQ (-1) (relQ st.2.2))

theorem g2Steps_ok : g2Steps.all stepOK = true := by decide +kernel

theorem g2Steps_targets : g2Steps.map (·.2.2) = List.range' 1 26 := by decide +kernel

end VOA.DeligneAudit.DeligneSector.G2
