/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6CarrierTables
import VOA.AffineGeneral.E6Table

set_option linter.style.longLine false

/-!
# E₆ sector data: Boolean table checks (light imports)
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open VOA.DeligneAudit.E6Sparse VOA.AffineGeneral.SCLie

/-- `θ(h)` on the Cartan basis vectors. -/
def thetaH : Fin 78 → ℕ := fun h => if h = 0 then 0 else if h = 1 then 1 else if h = 2 then 0 else if h = 3 then 0 else if h = 4 then 0 else if h = 5 then 0 else 0

/-- Lowering exponents `θ(h_i)` at the simple lowering vectors. -/
def lowExpE6 : Fin 78 → ℕ := fun i => if i = 47 then 0 else if i = 46 then 1 else if i = 45 then 0 else if i = 44 then 0 else if i = 43 then 0 else if i = 42 then 0 else 0

/-- Weights in simple-root coordinates, as a list table. -/
def wtRaw : List (List ℤ) := [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 0, 0, 1, 1, 1], [0, 0, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 0, 0], [1, 0, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1], [0, 1, 0, 1, 1, 1], [0, 1, 1, 1, 1, 0], [1, 0, 1, 1, 1, 0], [1, 1, 1, 1, 0, 0], [0, 1, 1, 1, 1, 1], [0, 1, 1, 2, 1, 0], [1, 0, 1, 1, 1, 1], [1, 1, 1, 1, 1, 0], [0, 1, 1, 2, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 2, 1, 0], [0, 1, 1, 2, 2, 1], [1, 1, 1, 2, 1, 1], [1, 1, 2, 2, 1, 0], [1, 1, 1, 2, 2, 1], [1, 1, 2, 2, 1, 1], [1, 1, 2, 2, 2, 1], [1, 1, 2, 3, 2, 1], [1, 2, 2, 3, 2, 1], [0, 0, 0, 0, 0, -1], [0, 0, 0, 0, -1, 0], [0, 0, 0, -1, 0, 0], [0, 0, -1, 0, 0, 0], [0, -1, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, -1], [0, 0, 0, -1, -1, 0], [0, 0, -1, -1, 0, 0], [0, -1, 0, -1, 0, 0], [-1, 0, -1, 0, 0, 0], [0, 0, 0, -1, -1, -1], [0, 0, -1, -1, -1, 0], [0, -1, 0, -1, -1, 0], [0, -1, -1, -1, 0, 0], [-1, 0, -1, -1, 0, 0], [0, 0, -1, -1, -1, -1], [0, -1, 0, -1, -1, -1], [0, -1, -1, -1, -1, 0], [-1, 0, -1, -1, -1, 0], [-1, -1, -1, -1, 0, 0], [0, -1, -1, -1, -1, -1], [0, -1, -1, -2, -1, 0], [-1, 0, -1, -1, -1, -1], [-1, -1, -1, -1, -1, 0], [0, -1, -1, -2, -1, -1], [-1, -1, -1, -1, -1, -1], [-1, -1, -1, -2, -1, 0], [0, -1, -1, -2, -2, -1], [-1, -1, -1, -2, -1, -1], [-1, -1, -2, -2, -1, 0], [-1, -1, -1, -2, -2, -1], [-1, -1, -2, -2, -1, -1], [-1, -1, -2, -2, -2, -1], [-1, -1, -2, -3, -2, -1], [-1, -2, -2, -3, -2, -1]]

def wtL (c : ℕ) : List ℤ := wtRaw.getD c []

/-- Weights in simple-root coordinates. -/
def wtE6 (y : Fin 78) (k : Fin 6) : ℤ := (wtL y).getD k 0

def thetaV : Fin 6 → ℤ := ![1, 2, 2, 3, 2, 1]

def cartanE6 : Fin 6 → Fin 6 → ℤ := ![![2, 0, -1, 0, 0, 0], ![0, 2, 0, -1, 0, 0], ![-1, 0, 2, -1, 0, 0], ![0, -1, -1, 2, -1, 0], ![0, 0, 0, -1, 2, -1], ![0, 0, 0, 0, -1, 2]]

theorem e6_wt_pos : ∀ y k, 0 ≤ wtE6 y k + thetaV k := by decide +kernel

/-- Weight additivity of the table, rows `lo ≤ x < hi`. -/
def wtChunk (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun x => (List.range 78).all fun y =>
    (entry e6T x y).all fun p => decide (p.1 < 78) &&
      (List.range 6).all fun k => (wtL p.1).getD k 0 == (wtL x).getD k 0 + (wtL y).getD k 0

theorem wtChunk_0 : wtChunk 0 13 = true := by decide +kernel
theorem wtChunk_1 : wtChunk 13 26 = true := by decide +kernel
theorem wtChunk_2 : wtChunk 26 39 = true := by decide +kernel
theorem wtChunk_3 : wtChunk 39 52 = true := by decide +kernel
theorem wtChunk_4 : wtChunk 52 65 = true := by decide +kernel
theorem wtChunk_5 : wtChunk 65 78 = true := by decide +kernel



end VOA.DeligneAudit.DeligneCarrier.E6
