import VOA.DeligneAudit.D4LeviRaiseOrder

/-! Simple Levi lowerings have adjoint square zero on the radical. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.FiniteG

def simpleLowerIndex : Fin 3 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

private theorem op_comm_end (a b : Fin 28) (r s : ℕ) :
    ρ.op a r * ρ.op b s - ρ.op b s * ρ.op a r =
      ∑ c, D4sector.f a b c • ρ.op c (r + s) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  exact ρ.comm a b r s v

theorem simple_lower_ad (i : Fin 3) (j : Fin 6) (s : ℕ) :
    adR (ρ.op (lowerColour (simpleLowerIndex i)) 0)
      (ρ.op (radicalColour j) s) =
      match lowerAction (simpleLowerIndex i) j with
      | none => 0
      | some (k, n) => (n : ℂ) • ρ.op (radicalColour k) s := by
  rw [adR_apply]
  rw [op_comm_end ρ]
  simp only [Nat.zero_add]
  change (∑ c : Fin 28,
      fD4 (lowerColour (simpleLowerIndex i)) (radicalColour j) c •
        ρ.op c s) = _
  cases h : lowerAction (simpleLowerIndex i) j with
  | none => simp [lower_coefficient, h]
  | some p =>
      rcases p with ⟨k, n⟩
      simp [lower_coefficient, h, Finset.sum_ite_eq']

private theorem adR_smul (X Z : Module.End ℂ V) (c : ℂ) :
    adR X (c • Z) = c • adR X Z := by
  simp [adR_apply, smul_sub, mul_smul_comm, smul_mul_assoc]

theorem simple_lower_ad_two (i : Fin 3) (j : Fin 6) (s : ℕ) :
    (adR (ρ.op (lowerColour (simpleLowerIndex i)) 0))^[2]
      (ρ.op (radicalColour j) s) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 by decide, Function.iterate_add_apply]
  simp only [Function.iterate_one]
  rw [simple_lower_ad]
  cases h : lowerAction (simpleLowerIndex i) j with
  | none => simp [h]
  | some p =>
      rcases p with ⟨k, n⟩
      have h2 : lowerAction (simpleLowerIndex i) k = none := by
        fin_cases i <;> fin_cases j <;>
          simp [simpleLowerIndex, lowerAction] at h ⊢
        all_goals rcases h with ⟨rfl, rfl⟩ <;> decide
      rw [adR_smul, simple_lower_ad, h2]
      simp

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.simple_lower_ad
#print axioms VOA.DeligneAudit.D4Levi.simple_lower_ad_two
