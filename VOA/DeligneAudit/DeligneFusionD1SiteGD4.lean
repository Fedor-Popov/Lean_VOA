import VOA.DeligneAudit.DeligneFusionD1SiteGCyclic
import VOA.DeligneAudit.DeligneFusionD1SiteGD4Skew
import VOA.DeligneAudit.DeligneSectorD4Cyc

/-!
# A concrete cyclic 29-dimensional D4 current site

The representation is constructed from the finite bracket table and its
Jacobi, skew and coadjoint-word certificates. No fusion or Demazure
identification is used.
-/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.SectorLoop
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem table_jacobi : JacobiCoord (fC 28 br) :=
  jacobiCoord_of_check d4_rangeCheck d4_jacCheck

/-- The actual current representation on the coadjoint space plus a line. -/
def currentRep : CurrentModule (fC 28 br) (Space 28) :=
  rep (fC 28 br) table_jacobi table_skewC

theorem coadjoint_cyclic (c : Fin 28) :
    (Pi.single c 1 : Fin 28 → ℂ) ∈ slotWords (fC 28 br) 27 10 := by
  have h := d4_cycCheck
  simp only [cycCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hN, hw⟩, hz⟩ := h c c.2
  exact single_mem_slotWords_of_check (br := br) 27 10 c (cyc c).1 (cyc c).2 hN
    (fun p hp => ⟨(hw p hp).1, (hw p hp).2⟩) hz

theorem current_cyclic : cyclic (fC 28 br) table_jacobi table_skewC 27 = ⊤ :=
  cyclic_top (fC 28 br) table_jacobi table_skewC 27 10 coadjoint_cyclic

theorem dimension : Module.finrank ℂ (Space 28) = 29 := finrank_space

end

end VOA.DeligneAudit.D1SiteG.D4Check

#print axioms VOA.DeligneAudit.D1SiteG.D4Check.current_cyclic
#print axioms VOA.DeligneAudit.D1SiteG.D4Check.dimension
