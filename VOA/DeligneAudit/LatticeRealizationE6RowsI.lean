/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable
import VOA.AffineGeneral.E6Table

/-!
# `E6`: the sector table is the lattice-model cert table, rows `64..71` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E6

theorem bridgeRow64 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 64 b = (VOA.DeligneAudit.E6Lat.sL 64 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow65 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 65 b = (VOA.DeligneAudit.E6Lat.sL 65 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow66 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 66 b = (VOA.DeligneAudit.E6Lat.sL 66 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow67 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 67 b = (VOA.DeligneAudit.E6Lat.sL 67 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow68 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 68 b = (VOA.DeligneAudit.E6Lat.sL 68 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow69 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 69 b = (VOA.DeligneAudit.E6Lat.sL 69 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow70 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 70 b = (VOA.DeligneAudit.E6Lat.sL 70 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow71 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 71 b = (VOA.DeligneAudit.E6Lat.sL 71 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E6
