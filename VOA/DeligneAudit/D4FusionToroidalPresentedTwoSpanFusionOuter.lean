import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanFusionRad

/-! The three outer simple mode-one fusion actions vanish. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem two_outer_mode_one_v (i : Fin 12)
    (hi : i.val < 4) (hne : i ≠ 2) :
    (ρPTE 2).op (negativeIndex i) 0 1 (pTE 2) = 0 := by
  have hv : (ρPTE 2).op (negativeIndex i) 0 0 (pTE 2) = 0 := by
    simpa [outer_exp_zero i hi hne] using two_seed_lowering_v_nil i hi
  have hh := two_generator_cartan_mode_one (negativeCartan i)
    (negativeCartan_lt_four i)
  have hc := (ρPTE 2).comm (negativeCartan i) (negativeIndex i)
    0 0 1 0 (pTE 2)
  have hsum : (∑ c : Fin 28,
      D4sector.f (negativeCartan i) (negativeIndex i) c •
        (ρPTE 2).op c 0 1 (pTE 2)) = 0 := by
    rw [if_pos (by omega)] at hc
    simpa [hv, hh] using hc.symm
  have htable : (∑ c : Fin 28,
      D4sector.f (negativeCartan i) (negativeIndex i) c •
        (ρPTE 2).op c 0 1 (pTE 2)) =
      (negativeWeight i : ℂ) •
        (ρPTE 2).op (negativeIndex i) 0 1 (pTE 2) := by
    change (∑ c : Fin 28, contactF (negativeCartan i) (negativeIndex i) c •
      (ρPTE 2).op c 0 1 (pTE 2)) = _
    simp only [negative_cartan_table, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [htable] at hsum
  exact (smul_eq_zero.mp hsum).resolve_left (negativeWeight_ne_zero i)

theorem two_outer_one_comm (i : Fin 12) (s : ℕ) (x : PTE 2) :
    (ρPTE 2).op (negativeIndex i) 0 1
      ((ρPTE 2).op D4sector.c₀ 1 s x) =
    (ρPTE 2).op D4sector.c₀ 1 s
      ((ρPTE 2).op (negativeIndex i) 0 1 x) := by
  have ht : ∀ i : Fin 12, ∀ e : Fin 28,
      fZ br (negativeIndex i) 27 e = 0 := by decide +kernel
  have hf : ∀ e : Fin 28,
      D4sector.f (negativeIndex i) D4sector.c₀ e = 0 := by
    intro e
    change (fZ br (negativeIndex i) 27 e : ℂ) = 0
    rw [ht]
    simp
  have hc := (ρPTE 2).comm (negativeIndex i) D4sector.c₀ 0 1 1 s x
  simp only [hf, zero_smul, Finset.sum_const_zero, ite_self] at hc
  exact sub_eq_zero.mp hc

theorem twoGen_outer_fusion (s : ℕ) (i : Fin 12)
    (hi : i.val < 4) (hne : i ≠ 2) :
    twoCurrent.op (negativeIndex i) 1 (twoGen s) = 0 := by
  have hv := two_outer_mode_one_v i hi hne
  have hz : (ρPTE 2).op (negativeIndex i) 0 1 (twoGen s) = 0 := by
    change (ρPTE 2).op (negativeIndex i) 0 1
      ((ρPTE 2).op D4sector.c₀ 1 s (pTE 2)) = 0
    rw [two_outer_one_comm, hv, map_zero]
  simpa [twoCurrent] using hz

theorem twoOne_outer_fusion (i : Fin 12)
    (hi : i.val < 4) (hne : i ≠ 2) :
    twoOneCurrent.op (negativeIndex i) 1 twoOneGen = 0 := by
  change (twoM 1).mkQ
    (twoCurrent.op (negativeIndex i) 1 (twoGen 0)) = 0
  rw [twoGen_outer_fusion 0 i hi hne, map_zero]

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_outer_mode_one_v
#print axioms VOA.DeligneAudit.Toroidal.two_outer_one_comm
#print axioms VOA.DeligneAudit.Toroidal.twoGen_outer_fusion
#print axioms VOA.DeligneAudit.Toroidal.twoOne_outer_fusion
