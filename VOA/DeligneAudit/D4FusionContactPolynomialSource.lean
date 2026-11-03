import VOA.DeligneAudit.D4FusionContactPolynomialSimpleTable
import VOA.DeligneAudit.D4FusionContactPolynomialRankOne
import VOA.DeligneAudit.D4FusionContactCurrentCenter

/-!
# The seven m=2 contact coefficient seeds from the actual source

All relations are exact in the original module, before taking the PBW
associated graded. They use source sl₂, fusion truncation and the actual
sharp highest-root nilpotence; no dimension or presentation premise.
-/

namespace VOA.DeligneAudit.D4FusionContact.PolynomialSource

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4
open PolynomialRankOne

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule contactF V)

def simpleE (r : ℕ) : Module.End ℂ V := R.op 6 r

def simpleH (r : ℕ) : Module.End ℂ V := R.op 1 r

def simpleF (r : ℕ) : Module.End ℂ V := R.op 18 r

private theorem comm_end (a b : Fin 28) (r s : ℕ) :
    R.op a r * R.op b s - R.op b s * R.op a r =
      ∑ c : Fin 28, contactF a b c • R.op c (r+s) := by
  ext v
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] using R.comm a b r s v

theorem simple_EF (r s : ℕ) : simpleE R r * simpleF R s - simpleF R s * simpleE R r =
    simpleH R (r+s) := by
  rw [show simpleE R r * simpleF R s - simpleF R s * simpleE R r =
      R.op 6 r * R.op 18 s - R.op 18 s * R.op 6 r from rfl, comm_end]
  simp only [simple_ef, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, simpleH]

theorem simple_HF (r s : ℕ) : simpleH R r * simpleF R s - simpleF R s * simpleH R r =
    (-2 : ℂ) • simpleF R (r+s) := by
  rw [show simpleH R r * simpleF R s - simpleF R s * simpleH R r =
      R.op 1 r * R.op 18 s - R.op 18 s * R.op 1 r from rfl, comm_end]
  simp only [simple_hf, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, simpleF]

theorem simple_FF (r s : ℕ) : simpleF R r * simpleF R s = simpleF R s * simpleF R r := by
  have hh := comm_end R 18 18 r s
  simp only [simple_ff, zero_smul, Finset.sum_const_zero] at hh
  exact sub_eq_zero.mp hh

variable {R} {w : V} {m : ℕ}

theorem simple_E_kills (h : HighestRel R w m) (r : ℕ) : simpleE R r w = 0 :=
  h.raising 6 (by decide) r

theorem simple_H_pos (h : HighestRel R w m) (r : ℕ) (hr : 1 ≤ r) : simpleH R r w = 0 :=
  h.cartan_pos 1 (by decide) r hr

/-- The exact seven coefficient seed relations used by the m=2 candidate. -/
structure SeedRel (R : CurrentModule contactF V) (w : V) : Prop where
  a_cube : (simpleF R 0 ^ 3) w = 0
  a_pair : simpleF R 0 (simpleF R 1 w) = 0
  a_square : simpleF R 1 (simpleF R 1 w) = 0
  c_five : (currentCenter R 0 ^ 5) w = 0
  c31 : (currentCenter R 0 ^ 3) (currentCenter R 1 w) = 0
  c12 : currentCenter R 0 (currentCenter R 1 (currentCenter R 1 w)) = 0
  c03 : currentCenter R 1 (currentCenter R 1 (currentCenter R 1 w)) = 0

variable {R : CurrentModule D4sector.f V}

/-- The actual m=2 local-Weyl/fusion source supplies every seed. -/
theorem source_seedRel (h : LocalWeylRelG D4sector R w 2) : SeedRel R w := by
  have hw := highestRel_of_localWeyl h
  have hA3 : (simpleF R 0 ^ 3) w = 0 := by
    have hi : D4sector.lowering (18 : Fin 28) := by
      change 16 ≤ (18 : Fin 28).val ∧ (18 : Fin 28).val < 20
      decide
    have he : D4sector.lowExp (18 : Fin 28) = 1 := rfl
    simpa only [he, Nat.mul_one, Module.End.pow_apply] using h.lowering (18 : Fin 28) hi
  have hA2 : simpleF R 2 w = 0 := by
    exact h.fusion (18 : Fin 28) (by change 16 ≤ (18 : Fin 28).val; decide)
  have hA10 : simpleF R 1 (simpleF R 0 w) = 0 := by
    simpa using first_derivative_of_nil (simple_EF R) (simple_HF R) (simple_FF R)
      (simple_E_kills hw) (simple_H_pos hw) 3 (by omega) hA3
  have hA11 := square_one_of_pair (simple_HF R) (simple_FF R) (simple_H_pos hw) hA2 hA10
  have hC5 : (currentCenter R 0 ^ 5) w = 0 := by
    simpa using localWeyl_current_center_pow h
  have hC2 : currentCenter R 2 w = 0 := by
    exact h.fusion (27 : Fin 28) (by change 16 ≤ (27 : Fin 28).val; decide)
  have hC31 : currentCenter R 1 ((currentCenter R 0 ^ 3) w) = 0 := by
    simpa using first_derivative_of_nil (current_highest_EF R) (current_highest_HF R)
      (current_center_comm R) (current_highest_E_kills hw) (current_highest_H_pos hw)
      5 (by omega) hC5
  have hC21 := second_derivative_of_five (current_highest_EF R) (current_highest_HF R)
    (current_center_comm R) (current_highest_E_kills hw) (current_highest_H_pos hw) hC2 hC31
  have hC03 := cube_one_of_pair21 (current_highest_HF R) (current_center_comm R)
    (current_highest_H_pos hw) hC2 hC21
  refine ⟨hA3, ?_, hA11, hC5, ?_, ?_, hC03⟩
  · rw [← Module.End.mul_apply, simple_FF R 0 1, Module.End.mul_apply]
    exact hA10
  · rw [← Module.End.mul_apply,
      ← (Commute.pow_right (current_center_comm R 1 0) 3).eq, Module.End.mul_apply]
    exact hC31
  · have he : currentCenter R 0 * currentCenter R 1 * currentCenter R 1 =
        currentCenter R 1 * currentCenter R 1 * currentCenter R 0 := by
      rw [current_center_comm R 0 1, mul_assoc, current_center_comm R 0 1, ← mul_assoc]
    simpa only [← Module.End.mul_apply, ← mul_assoc, he] using hC21

end
end VOA.DeligneAudit.D4FusionContact.PolynomialSource

#print axioms VOA.DeligneAudit.D4FusionContact.PolynomialSource.source_seedRel
