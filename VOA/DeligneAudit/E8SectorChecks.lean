/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E8SectorDefs

/-!
# `E₈` sector: Boolean table checks (light imports, chunked)
-/

namespace VOA.DeligneAudit.DeligneCarrier.E8

open VOA.DeligneAudit.E7Sparse VOA.DeligneAudit.E6SectorSparse VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

/-- `θ(h_i)` on the Cartan indices. -/
def thetaH : Fin 248 → ℕ := fun h => if h = 0 then 0 else if h = 1 then 0 else if h = 2 then 0 else if h = 3 then 0 else if h = 4 then 0 else if h = 5 then 0 else if h = 6 then 0 else if h = 7 then 1 else 0

/-- The string lengths `θ(h_k)` at the simple lowering vectors. -/
def lowExpE8 : Fin 248 → ℕ := fun i => if i = 135 then 0 else if i = 134 then 0 else if i = 133 then 0 else if i = 132 then 0 else if i = 131 then 0 else if i = 130 then 0 else if i = 129 then 0 else if i = 128 then 1 else 0

/-- `θ` in simple-root coordinates. -/
def thetaV : Fin 8 → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem wtLink : wtLinkOK = true := by decide +kernel

theorem e8_wt_pos : ∀ y k, 0 ≤ E8Lie.wt y k + thetaV k := by decide +kernel

/-- Weight additivity of the table, rows `lo ≤ x < hi`. -/
def wtChunk (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun x => (List.range 248).all fun y =>
    (entry e8T x y).all fun p => decide (p.1 < 248) &&
      (wtL.getD p.1 [] == List.zipWith (· + ·) (wtL.getD x []) (wtL.getD y []))

theorem raising_ok0 : (List.range' 8 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok1 : (List.range' 16 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok2 : (List.range' 24 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok3 : (List.range' 32 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok4 : (List.range' 40 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok5 : (List.range' 48 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok6 : (List.range' 56 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok7 : (List.range' 64 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok8 : (List.range' 72 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok9 : (List.range' 80 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok10 : (List.range' 88 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok11 : (List.range' 96 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok12 : (List.range' 104 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok13 : (List.range' 112 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel

theorem raising_ok14 : (List.range' 120 8).all (fun e => (List.range 248).all fun y => coef (entry e8T e y) 247 == 0) = true := by
  decide +kernel


theorem cartan_ok : (List.range 8).all (fun h => (List.range 248).all fun y =>
    coef (entry e8T h y) 247 == if y = 247 then -((thetaH ⟨h % 248, Nat.mod_lt _ (by norm_num)⟩ : ℕ) : ℤ) else 0) = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCarrier.E8
