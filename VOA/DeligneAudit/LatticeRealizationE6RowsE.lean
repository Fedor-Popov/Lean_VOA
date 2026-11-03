/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable
import VOA.AffineGeneral.E6Table

/-!
# `E6`: the sector table is the lattice-model cert table, rows `32..39` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E6

theorem bridgeRow32 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 32 b = (VOA.DeligneAudit.E6Lat.sL 32 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow33 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 33 b = (VOA.DeligneAudit.E6Lat.sL 33 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow34 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 34 b = (VOA.DeligneAudit.E6Lat.sL 34 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow35 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 35 b = (VOA.DeligneAudit.E6Lat.sL 35 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow36 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 36 b = (VOA.DeligneAudit.E6Lat.sL 36 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow37 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 37 b = (VOA.DeligneAudit.E6Lat.sL 37 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow38 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 38 b = (VOA.DeligneAudit.E6Lat.sL 38 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow39 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 39 b = (VOA.DeligneAudit.E6Lat.sL 39 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E6
