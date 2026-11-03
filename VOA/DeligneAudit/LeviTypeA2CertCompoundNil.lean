import VOA.DeligneAudit.LeviTypeA2CertCompoundCount
import VOA.DeligneAudit.DeligneFusionFiniteGAlg
import VOA.DeligneAudit.LeviTypeAStepSl2

/-! Sharp compound-root zero-mode nilpotence from the two simple-root relations. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.FiniteG VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private theorem compound_nil_large (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) :
    (ρ.op 5 0 ^ (p + 1 + 2 * q)) w = 0 := by
  let X : Module.End ℂ V := ρ.op 4 0
  let Y : Module.End ℂ V := ρ.op 3 0
  have hXY : adR X Y = ρ.op 5 0 := by
    rw [adR_apply, op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  have hXXY : (adR X)^[2] Y = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by omega, Function.iterate_add_apply]
    simp only [Function.iterate_one, hXY, adR_apply]
    rw [op_comm_end]
    simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
  have hYYX : (adR Y)^[2] X = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by omega, Function.iterate_add_apply]
    have hYX : adR Y X = -ρ.op 5 0 := by
      rw [adR_apply, op_comm_end]
      simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
    simp only [Function.iterate_one, hYX, adR_apply]
    have hcomm : Y * ρ.op 5 0 - ρ.op 5 0 * Y = 0 := by
      rw [op_comm_end]
      simp [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
    calc
      Y * -ρ.op 5 0 - -ρ.op 5 0 * Y =
          -(Y * ρ.op 5 0 - ρ.op 5 0 * Y) := by simp only [mul_neg, neg_mul]; abel
      _ = 0 := by rw [hcomm]; simp
  have hYpow : ∀ b : ℕ, (Y ^ (p + 1 + 2 * b)) ((X ^ b) w) = 0 := by
    intro b
    induction b with
    | zero => simpa [X, Y, Module.End.pow_apply] using h.lowering_first
    | succ b ih =>
        have ht := pow_kill_of_ad Y X 2 (p + 1 + 2 * b) ((X ^ b) w)
          hYYX ih
        have hexp : p + 1 + 2 * (b + 1) = 2 + (p + 1 + 2 * b) := by omega
        rw [hexp, pow_add, pow_succ' X b]
        rw [show p + 1 + 2 * b + 2 = 2 + (p + 1 + 2 * b) by omega,
          pow_add] at ht
        simpa only [pow_two, Module.End.mul_apply] using ht
  have hXw : (X ^ (q + 1)) w = 0 := by
    simpa [X, Module.End.pow_apply] using h.lowering_second
  have hYN : ∀ b < q + 1,
      (Y ^ (p + 1 + 2 * q)) ((X ^ b) w) = 0 := by
    intro b hb
    exact pow_kill_mono Y (hYpow b) (by omega)
  have ht := top_nil X Y 1 (q + 1) (p + 1 + 2 * q) w
    hXXY hXw hYN
  simpa only [Function.iterate_one, hXY] using ht

/-- The compound-root lowering operator has its sharp highest-weight power. -/
theorem a2_compound_nilpotence (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) : A2CompoundNilpotence ρ w p q := by
  let E : Module.End ℂ V := ρ.op 2 0
  let F : Module.End ℂ V := ρ.op 5 0
  let H : Module.End ℂ V := ρ.op 6 0 + ρ.op 7 0
  have hEF : ∀ v, E (F v) - F (E v) = H v := by
    intro v
    have hc : E * F - F * E = H := by
      rw [op_comm_end]
      simp [H, Fin.sum_univ_eight, VOA.AffineSl3.bracketTable]
    exact congrArg (fun T : Module.End ℂ V => T v) hc
  have hHF : ∀ v, H (F v) - F (H v) = (-2 : ℂ) • F v := by
    intro v
    have hc : H * F - F * H = (-2 : ℂ) • F := by
      dsimp [H]
      rw [show (ρ.op 6 0 + ρ.op 7 0) * F -
          F * (ρ.op 6 0 + ρ.op 7 0) =
          (ρ.op 6 0 * F - F * ρ.op 6 0) +
          (ρ.op 7 0 * F - F * ρ.op 7 0) by noncomm_ring]
      rw [op_comm_end, op_comm_end]
      simp [F, Fin.sum_univ_eight, VOA.AffineSl3.bracketTable, two_smul]
    exact congrArg (fun T : Module.End ℂ V => T v) hc
  have hE : E w = 0 := h.raising 2 (by decide) 0
  have hH : H w = ((p + q : ℕ) : ℂ) • w := by
    simp [H, h.cartan_first, h.cartan_second, Nat.cast_add, add_smul]
  have hN : F^[p + 1 + 2 * q] w = 0 := by
    simpa [F, ← Module.End.pow_apply] using compound_nil_large ρ w p q h
  have hsharp := sl2_lowering_of_nilpotent E F H hEF hHF w
    (p + q) (p + 1 + 2 * q) hE hH hN (by omega)
  simpa [A2CompoundNilpotence, F, Module.End.pow_apply] using hsharp

/-- Every nonzero radical key lies in the explicit finite box. -/
theorem a2KeyBox_contains_nonzero_unconditional (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q)
    (k : A2RadicalKey) (hk : a2KeyLayer ρ w k ≠ ⊥) :
    k ∈ a2KeyBox p q :=
  a2KeyBox_contains_nonzero_of_compoundNilpotence ρ w p q h
    (a2_compound_nilpotence ρ w p q h) k hk

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_compound_nilpotence
#print axioms VOA.DeligneAudit.A3Sector.a2KeyBox_contains_nonzero_unconditional
