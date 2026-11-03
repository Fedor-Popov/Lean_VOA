/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable
import VOA.DeligneAudit.E7SectorDefs

/-!
# `E7`: the sector table is the lattice-model cert table, rows `16..23` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E7

theorem bridgeRow16 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 16 b = (VOA.DeligneAudit.E7Lie.sL 16 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow17 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 17 b = (VOA.DeligneAudit.E7Lie.sL 17 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow18 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 18 b = (VOA.DeligneAudit.E7Lie.sL 18 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow19 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 19 b = (VOA.DeligneAudit.E7Lie.sL 19 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow20 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 20 b = (VOA.DeligneAudit.E7Lie.sL 20 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow21 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 21 b = (VOA.DeligneAudit.E7Lie.sL 21 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow22 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 22 b = (VOA.DeligneAudit.E7Lie.sL 22 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow23 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 23 b = (VOA.DeligneAudit.E7Lie.sL 23 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E7
