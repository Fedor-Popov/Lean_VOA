import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanRank

/-! The quotient current module and its cyclic positive-span image. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl

noncomputable section

theorem twoM_one_inv (c : Fin 28) (r : ℕ) :
    twoM 1 ≤ (twoM 1).comap (twoCurrent.op c r) := by
  rw [twoM_eq_cycSubG]
  exact cycSubG_inv twoCurrent (twoGen 1) c r

abbrev twoOneQuot := PTE 2 ⧸ twoM 1

def twoOneCurrent : CurrentModule D4sector.f twoOneQuot :=
  quotRepG twoCurrent (twoM 1) twoM_one_inv

def twoOneGen : twoOneQuot := (twoM 1).mkQ (twoGen 0)

theorem twoOne_word (l : List (Ltr 28)) :
    wordOp twoOneCurrent l twoOneGen =
      (twoM 1).mkQ (wordOp twoCurrent l (twoGen 0)) := by
  exact quot_wordOpG twoCurrent (twoM 1) twoM_one_inv (twoGen 0) l

theorem twoOne_cyclic_image :
    cycSubG twoOneCurrent twoOneGen = (twoM 0).map (twoM 1).mkQ := by
  rw [twoM_eq_cycSubG 0, cycSubG, cycSubG, Submodule.map_span]
  congr 1
  ext q
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨wordOp twoCurrent l (twoGen 0), ⟨l, rfl⟩, (twoOne_word l).symm⟩
  · rintro ⟨x, ⟨l, rfl⟩, rfl⟩
    exact ⟨l, (twoOne_word l)⟩

theorem twoPositiveSpan_comap :
    twoPositiveSpan = (cycSubG twoOneCurrent twoOneGen).comap (twoM 1).mkQ := by
  rw [twoOne_cyclic_image, Submodule.comap_map_mkQ, twoPositiveSpan, sup_comm]

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoM_one_inv
#print axioms VOA.DeligneAudit.Toroidal.twoOne_word
#print axioms VOA.DeligneAudit.Toroidal.twoOne_cyclic_image
#print axioms VOA.DeligneAudit.Toroidal.twoPositiveSpan_comap
