import VOA.DeligneAudit.D4FusionContactCurrentSL2Table
import VOA.DeligneAudit.D4FusionContactCore
import VOA.DeligneAudit.DeligneFusionECalc

/-! # Actual highest-root sl₂ current operators and source highest relations -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def currentHighestE (r : ℕ) : Module.End ℂ V := -R.op 15 r

def currentHighestH (r : ℕ) : Module.End ℂ V :=
  R.op 0 r + R.op 1 r + R.op 1 r + R.op 2 r + R.op 3 r

def currentCenter (r : ℕ) : Module.End ℂ V := R.op 27 r

private theorem current_comm_end (a b : Fin 28) (r s : ℕ) :
    R.op a r * R.op b s - R.op b s * R.op a r =
      ∑ c : Fin 28, contactF a b c • R.op c (r+s) := by
  ext v
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] using R.comm a b r s v

theorem current_highest_EF (r s : ℕ) :
    currentHighestE R r * currentCenter R s - currentCenter R s * currentHighestE R r =
      currentHighestH R (r+s) := by
  have hs : (∑ c : Fin 28, contactF 15 27 c • R.op c (r+s)) =
      -currentHighestH R (r+s) := by
    simp only [highest_root_ef, add_smul, ite_smul, zero_smul,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      neg_smul, one_smul, currentHighestH]
    abel
  calc
    _ = -(R.op 15 r * R.op 27 s - R.op 27 s * R.op 15 r) := by
      dsimp only [currentHighestE, currentCenter]
      noncomm_ring
    _ = _ := by rw [current_comm_end, hs, neg_neg]

private theorem current_cartan_comm (b : Fin 28) (r s : ℕ) :
    currentHighestH R r * R.op b s - R.op b s * currentHighestH R r =
      ∑ c : Fin 28, (contactF 0 b c + contactF 1 b c + contactF 1 b c +
        contactF 2 b c + contactF 3 b c) • R.op c (r+s) := by
  calc
    _ = (R.op 0 r * R.op b s - R.op b s * R.op 0 r) +
        (R.op 1 r * R.op b s - R.op b s * R.op 1 r) +
        (R.op 1 r * R.op b s - R.op b s * R.op 1 r) +
        (R.op 2 r * R.op b s - R.op b s * R.op 2 r) +
        (R.op 3 r * R.op b s - R.op b s * R.op 3 r) := by
      dsimp only [currentHighestH]
      noncomm_ring
    _ = _ := by simp only [current_comm_end, add_smul, Finset.sum_add_distrib]

theorem current_highest_HF (r s : ℕ) :
    currentHighestH R r * currentCenter R s - currentCenter R s * currentHighestH R r =
      (-2 : ℂ) • currentCenter R (r+s) := by
  change currentHighestH R r * R.op 27 s - R.op 27 s * currentHighestH R r = _
  rw [current_cartan_comm]
  simp only [highest_root_hf, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, currentCenter]

theorem current_highest_HE (r s : ℕ) :
    currentHighestH R r * currentHighestE R s - currentHighestE R s * currentHighestH R r =
      (2 : ℂ) • currentHighestE R (r+s) := by
  calc
    _ = -(currentHighestH R r * R.op 15 s - R.op 15 s * currentHighestH R r) := by
      dsimp only [currentHighestE]
      noncomm_ring
    _ = _ := by
      rw [current_cartan_comm]
      simp only [highest_root_he, ite_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, currentHighestE, smul_neg]

theorem current_center_comm (r s : ℕ) :
    currentCenter R r * currentCenter R s = currentCenter R s * currentCenter R r := by
  have hh := contact_comm (R := R) 8 8 r s
  have hz : contactCoeff 8 8 = 0 := by decide
  rw [hz, Int.cast_zero, zero_smul] at hh
  exact sub_eq_zero.mp hh

theorem current_highest_EE (r s : ℕ) :
    currentHighestE R r * currentHighestE R s = currentHighestE R s * currentHighestE R r := by
  have hh := current_comm_end R 15 15 r s
  simp only [highest_root_ee, zero_smul, Finset.sum_const_zero] at hh
  simpa only [currentHighestE, neg_mul_neg] using sub_eq_zero.mp hh

variable {R} {w : V} {m : ℕ}

theorem current_highest_E_kills (h : HighestRel R w m) (r : ℕ) :
    currentHighestE R r w = 0 := by
  change -R.op 15 r w = 0
  rw [h.raising 15 (by decide) r, neg_zero]

theorem current_highest_H_pos (h : HighestRel R w m) (r : ℕ) (hr : 1 ≤ r) :
    currentHighestH R r w = 0 := by
  simp only [currentHighestH, LinearMap.add_apply,
    h.cartan_pos 0 (by decide) r hr, h.cartan_pos 1 (by decide) r hr,
    h.cartan_pos 2 (by decide) r hr, h.cartan_pos 3 (by decide) r hr, add_zero]

theorem current_highest_H_zero (h : HighestRel R w m) :
    currentHighestH R 0 w = (((2*m : ℕ) : ℤ) : ℂ) • w := by
  have h0 : R.op 0 0 w = 0 := by simpa using h.cartan_zero 0 (by decide)
  have h1 : R.op 1 0 w = (m : ℂ) • w := by simpa using h.cartan_zero 1 (by decide)
  have h2 : R.op 2 0 w = 0 := by simpa using h.cartan_zero 2 (by decide)
  have h3 : R.op 3 0 w = 0 := by simpa using h.cartan_zero 3 (by decide)
  simp only [currentHighestH, LinearMap.add_apply, h0, h1, h2, h3, zero_add, add_zero]
  rw [← add_smul]
  congr 1
  push_cast
  ring

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.current_highest_EF
#print axioms VOA.DeligneAudit.D4FusionContact.current_highest_HF
#print axioms VOA.DeligneAudit.D4FusionContact.current_highest_HE
