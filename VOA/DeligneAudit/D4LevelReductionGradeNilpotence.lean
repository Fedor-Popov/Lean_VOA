import VOA.DeligneAudit.D4LevelReductionGradeEigenspaces

/-! Nilpotence of operators that raise or lower the intrinsic vector-node grade. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

/-- A unit grade shift is nilpotent on the finite interval of truncated-module grades. -/
theorem truncatedGrade_shift_nilpotent (m : ℕ) (hm : 1 ≤ m)
    (T : Module.End ℂ (TruncatedModule m)) (d : ℤ) (hd : d = 1 ∨ d = -1)
    (hT : ∀ κ : ℤ, ∀ v ∈ truncatedGradeSpace m κ,
      T v ∈ truncatedGradeSpace m (κ + d)) : IsNilpotent T := by
  have hpow (n : ℕ) (κ : ℤ) (v : TruncatedModule m)
      (hv : v ∈ truncatedGradeSpace m κ) :
      (T ^ n) v ∈ truncatedGradeSpace m (κ + (n : ℤ) * d) := by
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      simpa only [pow_succ', Module.End.mul_apply, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, add_assoc] using hT _ _ ih
  refine ⟨6 * m + 1, LinearMap.ker_eq_top.mp ?_⟩
  apply top_unique
  rw [← truncatedGradeSpace_spans m hm]
  apply iSup_le
  intro κ v hv
  change (T ^ (6 * m + 1)) v = 0
  by_cases hκ : κ < -5 * (m : ℤ) ∨ (m : ℤ) < κ
  · have hz : v = 0 := by
      simpa only [truncatedGradeSpace_eq_bot_of_grade_outside m hm κ hκ,
        Submodule.mem_bot] using hv
    rw [hz, map_zero]
  have hp := hpow (6 * m + 1) κ v hv
  have hout : κ + ((6 * m + 1 : ℕ) : ℤ) * d < -5 * (m : ℤ) ∨
      (m : ℤ) < κ + ((6 * m + 1 : ℕ) : ℤ) * d := by
    rcases hd with rfl | rfl <;> push_cast <;> omega
  simpa only [truncatedGradeSpace_eq_bot_of_grade_outside m hm _ hout,
    Submodule.mem_bot] using hp

/-- A Cartan commutator with eigenvalue twice a unit step gives a nilpotent operator. -/
theorem truncatedGrade_commutator_nilpotent (m : ℕ) (hm : 1 ≤ m)
    (T : Module.End ℂ (TruncatedModule m)) (d : ℤ) (hd : d = 1 ∨ d = -1)
    (hT : ∀ v, doubledGradeCartan (univRepG D4sector.f (lwSpec D4sector m)) (T v) -
      T (doubledGradeCartan (univRepG D4sector.f (lwSpec D4sector m)) v) =
        (2 * (d : ℂ)) • T v) : IsNilpotent T := by
  apply truncatedGrade_shift_nilpotent m hm T d hd
  intro κ v hv
  have he := Module.End.mem_eigenspace_iff.mp hv
  apply Module.End.mem_eigenspace_iff.mpr
  rw [sub_eq_iff_eq_add.mp (hT v), he, map_smul]
  push_cast
  module

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGrade_shift_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGrade_commutator_nilpotent
