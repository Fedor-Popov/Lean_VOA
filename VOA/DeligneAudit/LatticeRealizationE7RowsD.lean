/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7LieTable
import VOA.DeligneAudit.E7SectorDefs

/-!
# `E7`: the sector table is the lattice-model cert table, rows `24..31` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E7

theorem bridgeRow24 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 24 b = (VOA.DeligneAudit.E7Lie.sL 24 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow25 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 25 b = (VOA.DeligneAudit.E7Lie.sL 25 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow26 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 26 b = (VOA.DeligneAudit.E7Lie.sL 26 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow27 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 27 b = (VOA.DeligneAudit.E7Lie.sL 27 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow28 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 28 b = (VOA.DeligneAudit.E7Lie.sL 28 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow29 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 29 b = (VOA.DeligneAudit.E7Lie.sL 29 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow30 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 30 b = (VOA.DeligneAudit.E7Lie.sL 30 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow31 : ∀ b : Fin 133,
    VOA.AffineGeneral.SCLie.entry VOA.DeligneAudit.DeligneCarrier.E7.e7T 31 b = (VOA.DeligneAudit.E7Lie.sL 31 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E7
