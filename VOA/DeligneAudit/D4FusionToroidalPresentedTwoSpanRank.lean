import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanCurrent
import VOA.DeligneAudit.D4FusionContactOne

/-! A multiplicity-one local Weyl relation bounds the whole cyclic span. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.D4FusionContact
open VOA.DeligneAudit.DeligneSector

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule D4sector.f V) (w : V)

theorem one_cycSubG_eq_cycDeg_zero
    (h : LocalWeylRelG D4sector R w 1) :
    cycSubG R w = cycDeg R w 0 := by
  apply le_antisymm
  · rw [cycSubG, Submodule.span_le]
    rintro v ⟨l, rfl⟩
    let d := VOA.DeligneAudit.SectorGraded.wordDeg l
    by_cases hd : d = 0
    · exact Submodule.subset_span ⟨l, hd, rfl⟩
    · have hz := localWeyl_one_cycDeg_eq_bot h d (by omega)
      have hm : wordOp R l w ∈ cycDeg R w d :=
        Submodule.subset_span ⟨l, rfl, rfl⟩
      rw [hz] at hm
      have hv : wordOp R l w = 0 := by simpa using hm
      change wordOp R l w ∈ cycDeg R w 0
      rw [hv]
      exact Submodule.zero_mem _
  · rw [cycDeg, Submodule.span_le]
    rintro v ⟨l, _, rfl⟩
    exact wordOp_mem_cycSubG R w l

theorem one_cycSubG_rank_bound
    (h : LocalWeylRelG D4sector R w 1) :
    FiniteDimensional ℂ (cycSubG R w) ∧
      Module.finrank ℂ (cycSubG R w) ≤ 28 := by
  rw [one_cycSubG_eq_cycDeg_zero R w h]
  exact localWeyl_one_zero_bound h

theorem twoM_one_rank_bound_of_localWeyl
    (h : LocalWeylRelG D4sector twoCurrent (twoGen 1) 1) :
    FiniteDimensional ℂ (twoM 1) ∧ Module.finrank ℂ (twoM 1) ≤ 28 := by
  rw [twoM_eq_cycSubG]
  exact one_cycSubG_rank_bound twoCurrent (twoGen 1) h

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.one_cycSubG_eq_cycDeg_zero
#print axioms VOA.DeligneAudit.Toroidal.one_cycSubG_rank_bound
#print axioms VOA.DeligneAudit.Toroidal.twoM_one_rank_bound_of_localWeyl
