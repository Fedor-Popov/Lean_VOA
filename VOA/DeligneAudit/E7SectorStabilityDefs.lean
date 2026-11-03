/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorIntegerTable
import VOA.DeligneAudit.E7CarrierTables
import VOA.DeligneAudit.E7Quad
import VOA.DeligneAudit.E6SectorDefs

/-! Computable E7 stability predicates, isolated from Lie-table comparison proofs.
The four original definitions below are preserved unchanged. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7
open VOA.DeligneAudit.E7Sparse VOA.DeligneAudit.E6SectorSparse VOA.AffineGeneral.SCLie
set_option linter.style.longLine false

/-- The quadratics of `I₂`. -/
def Pq (s : ℕ) : List (ℕ × ℕ × ℤ) := if s < 1539 then relQ s else qQ

/-- Pairs `(λ, s)` from flat `z s` data. -/
def pairsOf : List ℕ → List (ℤ × ℕ)
  | z :: s :: rest => (E7Sparse.decZ z, s) :: pairsOf rest
  | _ => []

/-- One stability certificate. -/
def stabRowOK (g r : ℕ) (c : List ℕ) : Bool :=
  decide (certL c ≠ 0) && (pairsOf c.tail).all (fun p => p.2 ≤ 1539) &&
    quadZero (scaleQ (certL c) (adS e7T g (Pq r)) ++
      scaleQ (-1) ((pairsOf c.tail).flatMap fun p => scaleQ p.1 (Pq p.2)))

/-- Certificates `lo ≤ r < hi` of a generator. -/
def stabPart (g : ℕ) (rows : List (List ℕ)) (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun r => stabRowOK g r (rows.getD r [])

end VOA.DeligneAudit.DeligneCarrier.E7
