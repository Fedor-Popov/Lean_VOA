/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable
import VOA.AffineGeneral.E6Table

/-!
# `E6`: the sector table is the lattice-model cert table, rows `8..15` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E6

theorem bridgeRow8 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 8 b = (VOA.DeligneAudit.E6Lat.sL 8 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow9 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 9 b = (VOA.DeligneAudit.E6Lat.sL 9 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow10 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 10 b = (VOA.DeligneAudit.E6Lat.sL 10 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow11 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 11 b = (VOA.DeligneAudit.E6Lat.sL 11 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow12 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 12 b = (VOA.DeligneAudit.E6Lat.sL 12 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow13 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 13 b = (VOA.DeligneAudit.E6Lat.sL 13 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow14 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 14 b = (VOA.DeligneAudit.E6Lat.sL 14 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow15 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 15 b = (VOA.DeligneAudit.E6Lat.sL 15 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E6
