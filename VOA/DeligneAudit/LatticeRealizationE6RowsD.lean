/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6LatTable
import VOA.AffineGeneral.E6Table

/-!
# `E6`: the sector table is the lattice-model cert table, rows `24..31` (one kernel check per row)
-/

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace VOA.DeligneAudit.LatticeRealization.E6

theorem bridgeRow24 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 24 b = (VOA.DeligneAudit.E6Lat.sL 24 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow25 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 25 b = (VOA.DeligneAudit.E6Lat.sL 25 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow26 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 26 b = (VOA.DeligneAudit.E6Lat.sL 26 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow27 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 27 b = (VOA.DeligneAudit.E6Lat.sL 27 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow28 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 28 b = (VOA.DeligneAudit.E6Lat.sL 28 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow29 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 29 b = (VOA.DeligneAudit.E6Lat.sL 29 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow30 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 30 b = (VOA.DeligneAudit.E6Lat.sL 30 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

theorem bridgeRow31 : ∀ b : Fin 78,
    VOA.AffineGeneral.SCLie.entry VOA.AffineGeneral.SCLie.e6T 31 b = (VOA.DeligneAudit.E6Lat.sL 31 b).map (fun t => ((t.1 : ℕ), t.2)) := by
  decide +kernel

end VOA.DeligneAudit.LatticeRealization.E6
