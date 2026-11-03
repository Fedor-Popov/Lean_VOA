import VOA.DeligneAudit.D4FusionContactCore
import VOA.DeligneAudit.D4FusionContactGradingTable

/-! # Exact center/positive-contact operator identities -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def center : Module.End ℂ V := R.op 27 0

def root (i : Fin 8) : Module.End ℂ V := R.op (radIndex i.castSucc) 0

def raise (i : Fin 8) : Module.End ℂ V := (positiveSign i : ℂ) • R.op (positiveIndex i) 0

theorem center_root_comm (i : Fin 8) : center R * root R i = root R i * center R := by
  have hc := contact_comm (R := R) i.castSucc 8 0 0
  have hz : contactCoeff i.castSucc 8 = 0 := by fin_cases i <;> rfl
  rw [show radIndex 8 = (27 : Fin 28) from rfl, hz, Int.cast_zero, zero_smul] at hc
  exact (sub_eq_zero.mp hc).symm

theorem raise_center_comm (i : Fin 8) :
    raise R i * center R - center R * raise R i = root R i := by
  ext v
  change (positiveSign i : ℂ) • R.op (positiveIndex i) 0 (R.op 27 0 v) -
    R.op 27 0 ((positiveSign i : ℂ) • R.op (positiveIndex i) 0 v) = _
  rw [map_smul, ← smul_sub, R.comm]
  simp only [Finset.smul_sum, smul_smul, positive_center, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

theorem raise_center_pow (i : Fin 8) (n : ℕ) :
    raise R i * center R ^ (n + 1) - center R ^ (n + 1) * raise R i =
      (n + 1) • (center R ^ n * root R i) := by
  induction n with
  | zero => simpa only [Nat.zero_add, pow_one, pow_zero, one_mul, one_nsmul] using
      raise_center_comm R i
  | succ n ih =>
      have hm : center R ^ n * root R i * center R = center R ^ (n + 1) * root R i := by
        rw [mul_assoc, ← center_root_comm R i, ← mul_assoc, ← pow_succ]
      calc
        raise R i * center R ^ (n + 1 + 1) - center R ^ (n + 1 + 1) * raise R i =
            (raise R i * center R ^ (n + 1) - center R ^ (n + 1) * raise R i) * center R +
              center R ^ (n + 1) * (raise R i * center R - center R * raise R i) := by
          rw [pow_succ]
          noncomm_ring
        _ = (n + 1) • (center R ^ n * root R i * center R) +
            center R ^ (n + 1) * root R i := by rw [ih, raise_center_comm, smul_mul_assoc]
        _ = (n + 1 + 1) • (center R ^ (n + 1) * root R i) := by
          simp only [hm, add_nsmul, one_nsmul]

variable {R} {w : V} {m : ℕ}

theorem raise_kills (h : HighestRel R w m) (i : Fin 8) : raise R i w = 0 := by
  change (positiveSign i : ℂ) • R.op (positiveIndex i) 0 w = 0
  rw [h.raising _ (positiveIndex_range i) 0, smul_zero]

/-- The first cubic polarization is an actual equality, using only
the source center cube and the proved highest-vector relations. -/
theorem root_center_square_zero (h : HighestRel R w m)
    (hC : (center R ^ 3) w = 0) (i : Fin 8) :
    root R i ((center R ^ 2) w) = 0 := by
  have hc := congrArg (fun T : Module.End ℂ V => T w) (raise_center_pow R i 2)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    hC, raise_kills h i, map_zero, sub_self] at hc
  have hz : (center R ^ 2 * root R i) w = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ] at hc
    exact (smul_eq_zero.mp hc.symm).resolve_left (by norm_num)
  have hcomm : Commute (center R) (root R i) := center_root_comm R i
  rw [(hcomm.pow_left 2).eq] at hz
  exact hz

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.raise_center_pow
#print axioms VOA.DeligneAudit.D4FusionContact.root_center_square_zero
