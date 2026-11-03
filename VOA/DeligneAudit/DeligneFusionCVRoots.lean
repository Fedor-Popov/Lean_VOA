import VOA.DeligneAudit.DeligneFusionCVTrunc
import VOA.DeligneAudit.DeligneFusionGarlandSl3

/-!
# Rootwise CV relations for the pure-adjoint A₂ presentation

The three root `sl₂[t]` subalgebras of a current module satisfy `CVsl2.SL2`.
For `MabRel ρ w 0 N`, the simple-root partitions are `1^N` and the highest-root
partition is `2^N`. These relations follow from the proved truncated-Weyl
Garland theorem, without any fusion dimension assumption.

This is only the presentation bridge to the enlarged CV family. It supplies
neither that family's sharp upper bound nor `FusionTotalDim`.
-/

namespace VOA.DeligneAudit.A2.CVRoots

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CVsl2

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

theorem sl2_first : SL2 (ρ.op 0) (ρ.op 6) (ρ.op 3) where
  hEF s k := by rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hHF p k := by rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hHE p q := by rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hFF i j := by
    rw [← sub_eq_zero, op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hEE i j := by
    rw [← sub_eq_zero, op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]

theorem sl2_second : SL2 (ρ.op 1) (ρ.op 7) (ρ.op 4) where
  hEF s k := by rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hHF p k := by rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hHE p q := by rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hFF i j := by
    rw [← sub_eq_zero, op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hEE i j := by
    rw [← sub_eq_zero, op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]

theorem sl2_highest : SL2 (ρ.op 2) (fun k => ρ.op 6 k + ρ.op 7 k) (ρ.op 5) where
  hEF s k := by rw [op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hHF p k := by
    rw [add_mul, mul_add, add_sub_add_comm, op_comm_end, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
    module
  hHE p q := by
    rw [add_mul, mul_add, add_sub_add_comm, op_comm_end, op_comm_end]
    simp [Fin.sum_univ_eight, bracketTable]
    module
  hFF i j := by
    rw [← sub_eq_zero, op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]
  hEE i j := by
    rw [← sub_eq_zero, op_comm_end]; simp [Fin.sum_univ_eight, bracketTable]

private theorem bal_self (N : ℕ) (hN : 0 < N) : bal N N = List.replicate N 1 := by
  simp [bal, Nat.div_self hN]

private theorem bal_double (N : ℕ) (hN : 0 < N) :
    bal (2 * N) N = List.replicate N 2 := by
  rw [bal, if_neg (by omega)]
  simp [Nat.ne_of_gt hN]

variable {ρ} {w : V} {N : ℕ}

/-- The first simple root has CV partition `1^N`. -/
theorem first (h : MabRel ρ w 0 N) (hN : 0 < N) :
    CVRel (ρ.op 3) (List.replicate N 1) w := by
  rw [← bal_self N hN]
  apply tw_cvrel (sl2_first ρ) (fun s => h.raising 0 (by decide) s)
    (fun p hp => h.cartan_pos 6 (by decide) p hp) hN
  · rw [Module.End.pow_apply]
    simpa using h.lowering_f1
  · intro j hj
    exact mab_f1_trunc h j (by simpa using hj)

/-- The second simple root has CV partition `1^N`. -/
theorem second (h : MabRel ρ w 0 N) (hN : 0 < N) :
    CVRel (ρ.op 4) (List.replicate N 1) w := by
  rw [← bal_self N hN]
  apply tw_cvrel (sl2_second ρ) (fun s => h.raising 1 (by decide) s)
    (fun p hp => h.cartan_pos 7 (by decide) p hp) hN
  · rw [Module.End.pow_apply]
    simpa using h.lowering_f2
  · intro j hj
    exact mab_f2_trunc h j (by simpa using hj)

/-- The highest root has CV partition `2^N`. -/
theorem highest (h : MabRel ρ w 0 N) (hN : 0 < N) :
    CVRel (ρ.op 5) (List.replicate N 2) w := by
  rw [← bal_double N hN]
  refine tw_cvrel (sl2_highest ρ) (fun s => h.raising 2 (by decide) s)
    (fun p hp => ?_) hN ?_ ?_
  · simp [h.cartan_pos 6 (by decide) p hp, h.cartan_pos 7 (by decide) p hp]
  · simpa using ftheta_pow h
  · intro j hj
    exact mab_ftheta_trunc h j (by simpa using hj)

/-- Rootwise CV presentation data supplied by `MabRel 0 N`, for positive `N`. -/
theorem mabRel_zero_cv (h : MabRel ρ w 0 N) (hN : 0 < N) :
    CVRel (ρ.op 3) (List.replicate N 1) w ∧
      CVRel (ρ.op 4) (List.replicate N 1) w ∧
      CVRel (ρ.op 5) (List.replicate N 2) w :=
  ⟨first h hN, second h hN, highest h hN⟩

end VOA.DeligneAudit.A2.CVRoots

#print axioms VOA.DeligneAudit.A2.CVRoots.mabRel_zero_cv
