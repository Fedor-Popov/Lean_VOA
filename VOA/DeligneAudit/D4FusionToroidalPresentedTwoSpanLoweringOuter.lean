import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanCartanPos

/-! The three outer simple lowering roots kill both positive generators. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem twoGen_negative_comm (i : Fin 12) (s : ℕ) (x : PTE 2) :
    (ρPTE 2).op (negativeIndex i) 0 0
      ((ρPTE 2).op D4sector.c₀ 1 s x) =
    (ρPTE 2).op D4sector.c₀ 1 s
      ((ρPTE 2).op (negativeIndex i) 0 0 x) := by
  have ht : ∀ i : Fin 12, ∀ e : Fin 28,
      fZ br (negativeIndex i) 27 e = 0 := by decide +kernel
  have hf : ∀ e : Fin 28,
      D4sector.f (negativeIndex i) D4sector.c₀ e = 0 := by
    intro e
    change (fZ br (negativeIndex i) 27 e : ℂ) = 0
    rw [ht]
    simp
  have hc := (ρPTE 2).comm (negativeIndex i) D4sector.c₀ 0 1 0 s x
  simp only [hf, zero_smul, Finset.sum_const_zero, ite_self] at hc
  exact sub_eq_zero.mp hc

theorem outer_exp_zero : ∀ i : Fin 12,
    i.val < 4 → i ≠ 2 → D4sector.lowExp (negativeIndex i) = 0 := by
  decide +kernel

theorem twoGen_outer_lowering (s : ℕ) (i : Fin 12)
    (hi : i.val < 4) (hne : i ≠ 2) :
    twoCurrent.op (negativeIndex i) 0 (twoGen s) = 0 := by
  have hv := two_seed_lowering_v_nil i hi
  have he := outer_exp_zero i hi hne
  have hv' : (ρPTE 2).op (negativeIndex i) 0 0 (pTE 2) = 0 := by
    simpa [he] using hv
  have hz : (ρPTE 2).op (negativeIndex i) 0 0 (twoGen s) = 0 := by
    change (ρPTE 2).op (negativeIndex i) 0 0
      ((ρPTE 2).op D4sector.c₀ 1 s (pTE 2)) = 0
    rw [twoGen_negative_comm, hv', map_zero]
  simpa [twoCurrent] using hz

theorem twoOne_outer_lowering (i : Fin 12)
    (hi : i.val < 4) (hne : i ≠ 2) :
    twoOneCurrent.op (negativeIndex i) 0 twoOneGen = 0 := by
  change (twoM 1).mkQ
    (twoCurrent.op (negativeIndex i) 0 (twoGen 0)) = 0
  rw [twoGen_outer_lowering 0 i hi hne, map_zero]

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoGen_negative_comm
#print axioms VOA.DeligneAudit.Toroidal.twoGen_outer_lowering
#print axioms VOA.DeligneAudit.Toroidal.twoOne_outer_lowering
