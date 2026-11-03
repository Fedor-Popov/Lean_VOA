/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable
import VOA.AffineGeneral.E6Table

/-!
# `E6`: the sector table is the lattice-model cert table, rows `16..23` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E6

theorem bridgeRow16 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 16 b = (VOA.DeligneAudit.E6Lat.sL 16 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow17 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 17 b = (VOA.DeligneAudit.E6Lat.sL 17 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow18 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 18 b = (VOA.DeligneAudit.E6Lat.sL 18 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow19 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 19 b = (VOA.DeligneAudit.E6Lat.sL 19 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow20 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 20 b = (VOA.DeligneAudit.E6Lat.sL 20 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow21 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 21 b = (VOA.DeligneAudit.E6Lat.sL 21 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow22 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 22 b = (VOA.DeligneAudit.E6Lat.sL 22 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow23 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 23 b = (VOA.DeligneAudit.E6Lat.sL 23 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E6
