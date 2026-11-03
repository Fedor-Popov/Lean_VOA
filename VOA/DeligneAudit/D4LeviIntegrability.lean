import VOA.DeligneAudit.D4FusionKernelTheta
import VOA.DeligneAudit.DeligneFusionFiniteGAlg

/-! Seven two-step adjoint transfers of zero-mode root nilpotence. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.FiniteG
open VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The two-step ad trick with a lowering operator that kills the source. -/
theorem two_step_nil (X Y Z : Module.End ℂ V) (w : V) (N : ℕ)
    (hXY : adR X Y = Z) (hXZ : adR X Z = 0)
    (hX : X w = 0) (hY : (Y ^ N) w = 0) : (Z ^ N) w = 0 := by
  have hXXY : (adR X)^[1 + 1] Y = 0 := by
    simp only [Function.iterate_succ_apply, Function.iterate_one, hXY]
    exact hXZ
  have hY' : ∀ b < 1, (Y ^ N) ((X ^ b) w) = 0 := by
    intro b hb
    have hb0 : b = 0 := by omega
    subst b
    simpa using hY
  have ht := top_nil X Y 1 1 N w hXXY (by simpa using hX) hY'
  simpa only [Function.iterate_one, hXY] using ht

/-- Source letters of the transfers: f1, f3, f4, f4, f4, f3, f1. -/
def stepA : Fin 7 → Fin 28 := ![19, 17, 16, 16, 16, 17, 19]
/-- Previous letters: f2, f2, f2, f23, X, X, f234. -/
def stepB : Fin 7 → Fin 28 := ![18, 18, 18, 21, 22, 22, 23]
/-- New letters: X, f23, f24, f234, U, U', Y. -/
def stepZ : Fin 7 → Fin 28 := ![22, 21, 20, 23, 24, 25, 26]
def stepSign : Fin 7 → ℤ := ![-1, 1, 1, -1, -1, -1, 1]

theorem step_table : ∀ i : Fin 7, ∀ e : Fin 28,
    stepSign i * fZ br (stepA i) (stepB i) e =
      if e = stepZ i then 1 else 0 := by
  decide +kernel

theorem step_next_zero : ∀ i : Fin 7, ∀ e : Fin 28,
    fZ br (stepA i) (stepZ i) e = 0 := by
  decide +kernel

variable (ρ : CurrentModule fD4 V)

/-- One root power transfers at exactly the same exponent. -/
theorem step_nil (i : Fin 7) (w : V) (N : ℕ)
    (hA : ρ.op (stepA i) 0 w = 0)
    (hB : ((ρ.op (stepB i) 0) ^ N) w = 0) :
    ((ρ.op (stepZ i) 0) ^ N) w = 0 := by
  let X : Module.End ℂ V := (stepSign i : ℂ) • ρ.op (stepA i) 0
  let Y : Module.End ℂ V := ρ.op (stepB i) 0
  let Z : Module.End ℂ V := ρ.op (stepZ i) 0
  have htable : ∀ e : Fin 28,
      (stepSign i : ℂ) * fD4 (stepA i) (stepB i) e =
        if e = stepZ i then 1 else 0 := by
    intro e
    simpa only [fD4, fC, fZ, Int.cast_mul, Int.cast_ite,
      Int.cast_one, Int.cast_zero] using
      congrArg (fun n : ℤ => (n : ℂ)) (step_table i e)
  have hXY : adR X Y = Z := by
    rw [adR_apply]
    have hc := op_comm_end4 (ρ := ρ) (stepA i) (stepB i)
    calc
      X * Y - Y * X = (stepSign i : ℂ) •
          (ρ.op (stepA i) 0 * ρ.op (stepB i) 0 -
            ρ.op (stepB i) 0 * ρ.op (stepA i) 0) := by
              simp [X, Y, smul_sub, smul_mul_assoc, mul_smul_comm]
      _ = ∑ e : Fin 28,
          ((stepSign i : ℂ) * fD4 (stepA i) (stepB i) e) •
            ρ.op e 0 := by
              rw [hc, Finset.smul_sum]
              simp only [smul_smul]
      _ = Z := by
        simp [htable, Z]
  have hXZ : adR X Z = 0 := by
    rw [adR_apply]
    have hc := op_comm_end4 (ρ := ρ) (stepA i) (stepZ i)
    have hzero : ∀ e : Fin 28, fD4 (stepA i) (stepZ i) e = 0 := by
      intro e
      change (fZ br (stepA i) (stepZ i) e : ℂ) = 0
      rw [step_next_zero i e]
      norm_num
    change (stepSign i : ℂ) • ρ.op (stepA i) 0 * ρ.op (stepZ i) 0 -
      ρ.op (stepZ i) 0 * ((stepSign i : ℂ) • ρ.op (stepA i) 0) = 0
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc]
    simp [hzero]
  have hX : X w = 0 := by simp [X, hA]
  exact two_step_nil X Y Z w N hXY hXZ hX hB

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.two_step_nil
#print axioms VOA.DeligneAudit.D4Levi.step_table
#print axioms VOA.DeligneAudit.D4Levi.step_next_zero
#print axioms VOA.DeligneAudit.D4Levi.step_nil
