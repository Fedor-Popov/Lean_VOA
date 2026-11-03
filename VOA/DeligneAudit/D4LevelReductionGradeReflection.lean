import VOA.DeligneAudit.D4LevelReductionGradeNilpotence
import VOA.DeligneAudit.D4LevelReductionSl2Reflection

/-!
Grade reversal from the diagonal sl2 of the orthogonal roots alpha-one and theta.
Its Cartan element is twice the node-one fundamental coweight, so its single
reflection suffices for grade symmetry without reflecting the Levi-level filtration.
-/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

/-- The sum of the positive alpha-one and highest-root zero modes. -/
noncomputable def gradeRaisingOperator : Module.End ℂ V :=
  ρ.op (7 : Fin 28) 0 + ρ.op (15 : Fin 28) 0

/-- The negative root modes, with the highest-root sign in the D4 table. -/
noncomputable def gradeLoweringOperator : Module.End ℂ V :=
  ρ.op (19 : Fin 28) 0 - ρ.op (27 : Fin 28) 0

/-- The diagonal root triple has Cartan element twice the fundamental coweight. -/
theorem gradeRaisingLowering_comm :
    ⁅gradeRaisingOperator ρ, gradeLoweringOperator ρ⁆ = doubledGradeCartan ρ := by
  have hc (z : Fin 28) :
      D4sector.f (7 : Fin 28) (19 : Fin 28) z - D4sector.f (7 : Fin 28) (27 : Fin 28) z +
        D4sector.f (15 : Fin 28) (19 : Fin 28) z - D4sector.f (15 : Fin 28) (27 : Fin 28) z =
          (if z = 0 then (2 : ℂ) else 0) + (if z = 1 then 2 else 0) +
            (if z = 2 then 1 else 0) + (if z = 3 then 1 else 0) := by
    have hi : ∀ z : Fin 28,
        fZ br 7 19 z - fZ br 7 27 z + fZ br 15 19 z - fZ br 15 27 z =
          (if z = 0 then (2 : ℤ) else 0) + (if z = 1 then 2 else 0) +
            (if z = 2 then 1 else 0) + (if z = 3 then 1 else 0) := by
      decide +kernel
    change fD4 7 19 z - fD4 7 27 z + fD4 15 19 z - fD4 15 27 z = _
    simpa only [fD4, fC, Int.cast_sub, Int.cast_add, Int.cast_ite,
      Int.cast_ofNat, Int.cast_one, Int.cast_zero] using
      congrArg (fun n : ℤ => (n : ℂ)) (hi z)
  ext v
  change gradeRaisingOperator ρ (gradeLoweringOperator ρ v) -
    gradeLoweringOperator ρ (gradeRaisingOperator ρ v) = doubledGradeCartan ρ v
  calc
    _ = (ρ.op (7 : Fin 28) 0 (ρ.op (19 : Fin 28) 0 v) -
          ρ.op (19 : Fin 28) 0 (ρ.op (7 : Fin 28) 0 v)) -
        (ρ.op (7 : Fin 28) 0 (ρ.op (27 : Fin 28) 0 v) -
          ρ.op (27 : Fin 28) 0 (ρ.op (7 : Fin 28) 0 v)) +
        (ρ.op (15 : Fin 28) 0 (ρ.op (19 : Fin 28) 0 v) -
          ρ.op (19 : Fin 28) 0 (ρ.op (15 : Fin 28) 0 v)) -
        (ρ.op (15 : Fin 28) 0 (ρ.op (27 : Fin 28) 0 v) -
          ρ.op (27 : Fin 28) 0 (ρ.op (15 : Fin 28) 0 v)) := by
      simp only [gradeRaisingOperator, gradeLoweringOperator, LinearMap.add_apply,
        LinearMap.sub_apply, map_add, map_sub]
      abel
    _ = ∑ z : Fin 28,
        (D4sector.f (7 : Fin 28) (19 : Fin 28) z - D4sector.f (7 : Fin 28) (27 : Fin 28) z +
          D4sector.f (15 : Fin 28) (19 : Fin 28) z - D4sector.f (15 : Fin 28) (27 : Fin 28) z) •
            ρ.op z 0 v := by
      rw [ρ.comm, ρ.comm, ρ.comm, ρ.comm]
      simp only [zero_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← sub_smul, ← add_smul]
      rfl
    _ = _ := by
      simp only [hc, add_smul, ite_smul, zero_smul, one_smul, Finset.sum_add_distrib]
      simp [doubledGradeCartan]

/-- The diagonal raising operator raises the doubled grade by two. -/
theorem gradeCartan_raising_comm :
    ⁅doubledGradeCartan ρ, gradeRaisingOperator ρ⁆ = (2 : ℂ) • gradeRaisingOperator ρ := by
  ext v
  have hfirst := doubledGradeCartan_comm ρ (7 : Fin 28) 0 v
  have hsecond := doubledGradeCartan_comm ρ (15 : Fin 28) 0 v
  simp only [currentAlphaGrade, Int.cast_one, mul_one] at hfirst hsecond
  change doubledGradeCartan ρ (gradeRaisingOperator ρ v) -
    gradeRaisingOperator ρ (doubledGradeCartan ρ v) = (2 : ℂ) • gradeRaisingOperator ρ v
  simp only [gradeRaisingOperator, LinearMap.add_apply, map_add]
  rw [sub_eq_iff_eq_add.mp hfirst, sub_eq_iff_eq_add.mp hsecond]
  module

/-- The diagonal lowering operator lowers the doubled grade by two. -/
theorem gradeCartan_lowering_comm :
    ⁅doubledGradeCartan ρ, gradeLoweringOperator ρ⁆ = -(2 : ℂ) • gradeLoweringOperator ρ := by
  ext v
  have hfirst := doubledGradeCartan_comm ρ (19 : Fin 28) 0 v
  have hsecond := doubledGradeCartan_comm ρ (27 : Fin 28) 0 v
  simp only [currentAlphaGrade, Int.cast_neg, Int.cast_one, mul_neg, mul_one]
    at hfirst hsecond
  change doubledGradeCartan ρ (gradeLoweringOperator ρ v) -
    gradeLoweringOperator ρ (doubledGradeCartan ρ v) = -(2 : ℂ) • gradeLoweringOperator ρ v
  simp only [gradeLoweringOperator, LinearMap.sub_apply, map_sub]
  rw [sub_eq_iff_eq_add.mp hfirst, sub_eq_iff_eq_add.mp hsecond]
  module

/-- Opposite intrinsic vector-node grades have equal dimensions at every multiplicity. -/
theorem truncatedGradeSpace_finrank_neg (m : ℕ) (hm : 1 ≤ m) (κ : ℤ) :
    Module.finrank ℂ (truncatedGradeSpace m (-κ)) =
      Module.finrank ℂ (truncatedGradeSpace m κ) := by
  haveI := (truncatedModule_rank_le_leviCoinvariants m hm).1
  let ρ := univRepG D4sector.f (lwSpec D4sector m)
  have hE : IsNilpotent (gradeRaisingOperator ρ) := by
    apply truncatedGrade_commutator_nilpotent m hm _ 1 (Or.inl rfl)
    intro v
    simpa using LinearMap.congr_fun (gradeCartan_raising_comm ρ) v
  have hF : IsNilpotent (gradeLoweringOperator ρ) := by
    apply truncatedGrade_commutator_nilpotent m hm _ (-1) (Or.inr rfl)
    intro v
    simpa using LinearMap.congr_fun (gradeCartan_lowering_comm ρ) v
  have he := sl2_nilpotent_eigenspace_finrank_eq (doubledGradeCartan ρ)
    (gradeRaisingOperator ρ) (gradeLoweringOperator ρ) (gradeRaisingLowering_comm ρ)
    (gradeCartan_raising_comm ρ) (gradeCartan_lowering_comm ρ) hE hF (2 * (κ : ℂ))
  unfold truncatedGradeSpace
  rw [Int.cast_neg, mul_neg]
  exact he.symm

/-- Grade reflection tightens the support to the symmetric interval from minus m to m. -/
theorem truncatedGradeSpace_eq_bot_of_outside_interval (m : ℕ) (hm : 1 ≤ m) (κ : ℤ)
    (hκ : κ < -(m : ℤ) ∨ (m : ℤ) < κ) : truncatedGradeSpace m κ = ⊥ := by
  rcases hκ with hκ | hκ
  · haveI := (truncatedModule_rank_le_leviCoinvariants m hm).1
    apply Submodule.finrank_eq_zero.mp
    rw [← truncatedGradeSpace_finrank_neg m hm κ,
      truncatedGradeSpace_eq_bot_of_grade_outside m hm (-κ) (Or.inr (by omega)),
      finrank_bot]
  · exact truncatedGradeSpace_eq_bot_of_grade_outside m hm κ (Or.inr hκ)

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.gradeRaisingLowering_comm
#print axioms VOA.DeligneAudit.D4LevelReduction.gradeCartan_raising_comm
#print axioms VOA.DeligneAudit.D4LevelReduction.gradeCartan_lowering_comm
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_finrank_neg
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedGradeSpace_eq_bot_of_outside_interval
