/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2SectorTables

/-!
# G2 sector data: kernel checks (blocks 0)
-/

namespace VOA.DeligneAudit.DeligneSector.G2

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem u3_b0 : (List.range' 0 14).all u3OK = true := by decide +kernel

theorem stab_b0_0 : (List.range' 0 28).all (stabCheck 0) = true := by decide +kernel

theorem stab_b1_0 : (List.range' 0 28).all (stabCheck 1) = true := by decide +kernel

theorem stab_b2_0 : (List.range' 0 28).all (stabCheck 2) = true := by decide +kernel

theorem stab_b3_0 : (List.range' 0 28).all (stabCheck 3) = true := by decide +kernel

theorem stab_b4_0 : (List.range' 0 28).all (stabCheck 4) = true := by decide +kernel

theorem stab_b5_0 : (List.range' 0 28).all (stabCheck 5) = true := by decide +kernel

theorem wt_b0 : (List.range' 0 14).all (fun a => (List.range 14).all fun b => (br a b).all fun p => (List.range 2).all fun i => wtZ p.1 i == wtZ a i + wtZ b i) = true := by decide +kernel

theorem relRange_ok : relRange = true := by decide +kernel

theorem gen_ok : genCheck 14 br genT gensL = true := by decide +kernel

theorem cover_ok : ((List.range 14).all fun c => decide (c ∈ gensL ++ genT.map (·.1))) = true := by decide +kernel

theorem diag_ok : ((List.range 28).all fun k => (relZ k).all fun t => !(t.1 = 12 ∧ t.2.1 = 12)) = true := by decide +kernel

theorem raising_ok : ∀ e y : Fin 14, e.val ∈ posL → fZ br e y 12 = 0 := by decide +kernel

theorem cycNodes_ok : cycNodes = true := by decide +kernel

theorem cyc_ok : cycCheck = true := by decide +kernel

theorem cycRoot_ok : vecs 0 = [(12, 1)] ∧ (cpar 0).2.2 = 0 := by decide +kernel

theorem vecLen : vecR.length = 24 := by decide +kernel

theorem cartan_ok : ∀ y : Fin 14, fZ br 0 y 12 = (if y.val = 12 then -3 else 0) ∧ fZ br 1 y 12 = (if y.val = 12 then 1 else 0) := by decide +kernel

end VOA.DeligneAudit.DeligneSector.G2
