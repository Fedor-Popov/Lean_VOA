import VOA.DeligneAudit.D4FusionToroidalPresentedTwoSpanFusionTheta
import VOA.DeligneAudit.D4FusionContactGradingTable

/-! The eight contact-root fusion actions follow from the highest-root actions. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem two_rad_mode_one_eq (i : Fin 8) (s : ℕ) :
    (ρPTE 2).op (radIndex i.castSucc) 0 1 (twoGen s) =
      (positiveSign i : ℂ) •
        (ρPTE 2).op (positiveIndex i) 0 0
          (twoCurrent.op D4sector.c₀ 1 (twoGen s)) := by
  have he : D4sector.raising (positiveIndex i) := positiveIndex_range i
  have hraise := twoGen_raising s (positiveIndex i) he 0
  have hraise' : (ρPTE 2).op (positiveIndex i) 0 0 (twoGen s) = 0 := by
    simpa [twoCurrent] using hraise
  have hc := (ρPTE 2).comm (positiveIndex i) D4sector.c₀ 0 0 0 1 (twoGen s)
  have hc' : (ρPTE 2).op (positiveIndex i) 0 0
      ((ρPTE 2).op D4sector.c₀ 0 1 (twoGen s)) =
      ∑ e : Fin 28, D4sector.f (positiveIndex i) D4sector.c₀ e •
        (ρPTE 2).op e 0 1 (twoGen s) := by
    rw [hraise', map_zero, sub_zero] at hc
    simpa only [Nat.zero_add, if_pos (by omega)] using hc
  have ht (e : Fin 28) :
      (positiveSign i : ℂ) * D4sector.f (positiveIndex i) D4sector.c₀ e =
        if e = radIndex i.castSucc then 1 else 0 := by
    exact positive_center i e
  have hsum : (positiveSign i : ℂ) •
      (∑ e : Fin 28, D4sector.f (positiveIndex i) D4sector.c₀ e •
        (ρPTE 2).op e 0 1 (twoGen s)) =
      (ρPTE 2).op (radIndex i.castSucc) 0 1 (twoGen s) := by
    simp only [Finset.smul_sum, smul_smul, ht, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, one_smul]
  rw [← hc'] at hsum
  simpa [twoCurrent] using hsum.symm

theorem twoGen_one_rad_fusion (i : Fin 8) :
    twoCurrent.op (radIndex i.castSucc) 1 (twoGen 1) = 0 := by
  have hp : (ρPTE 2).op D4sector.c₀ 0 1 (twoGen 1) = 0 := by
    simpa [twoCurrent] using twoGen_one_theta_fusion
  change (ρPTE 2).op (radIndex i.castSucc) 0 1 (twoGen 1) = 0
  rw [two_rad_mode_one_eq]
  simp [twoCurrent, hp]

theorem twoGen_zero_rad_fusion_mem (i : Fin 8) :
    twoCurrent.op (radIndex i.castSucc) 1 (twoGen 0) ∈ twoM 1 := by
  have hp : (ρPTE 2).op D4sector.c₀ 0 1 (twoGen 0) ∈ twoM 1 := by
    simpa [twoCurrent] using twoGen_zero_theta_fusion_mem
  have hstable := twoM_op_zero 1 (positiveIndex i) 0 hp
  change (ρPTE 2).op (positiveIndex i) 0 0
    ((ρPTE 2).op D4sector.c₀ 0 1 (twoGen 0)) ∈ twoM 1 at hstable
  change (ρPTE 2).op (radIndex i.castSucc) 0 1 (twoGen 0) ∈ twoM 1
  rw [two_rad_mode_one_eq]
  simpa [twoCurrent] using (Submodule.smul_mem (twoM 1) (positiveSign i : ℂ) hstable)

theorem twoOne_rad_fusion (i : Fin 8) :
    twoOneCurrent.op (radIndex i.castSucc) 1 twoOneGen = 0 := by
  change (twoM 1).mkQ
    (twoCurrent.op (radIndex i.castSucc) 1 (twoGen 0)) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (twoGen_zero_rad_fusion_mem i)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_rad_mode_one_eq
#print axioms VOA.DeligneAudit.Toroidal.twoGen_one_rad_fusion
#print axioms VOA.DeligneAudit.Toroidal.twoGen_zero_rad_fusion_mem
#print axioms VOA.DeligneAudit.Toroidal.twoOne_rad_fusion
