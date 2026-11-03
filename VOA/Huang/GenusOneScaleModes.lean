import VOA.Huang.GenusOneModeWeight
import VOA.Modularity.SqGradedBlockSlash
import VOA.Modularity.AKModularODE

/-! # Square-mode homogeneity and scaling on insertion modules -/
namespace VOA.Huang.GenusOne.SquareModule
open VOA Complex
open scoped BigOperators MatrixGroups
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

theorem sqMode_weight {a : V} {α β : ℂ} {w : M}
    (ha : Lsq W 0 a = β • a) (hw : sqL A 0 w = α • w) (j : ℤ) :
    sqL A 0 (sqMode A j a w) = (β + α - j - 1) • sqMode A j a w := by
  have hc := Lsq_zero_sqMode_comm A a j w
  rw [ha, hw, map_smul, map_smul, LinearMap.smul_apply] at hc
  linear_combination (norm := module) hc

/-- Exponent arithmetic is on a fixed nonzero base, so no power-of-a-product
branch rule is needed. -/
theorem insertionScale_sqMode (D : DirectSum.IsInternal (insertionSqWeight A))
    {a : V} {β : ℂ} (ha : Lsq W 0 a = β • a) (j : ℤ) {z : ℂ} (hz : z ≠ 0) (w : M) :
    insertionScale D z (sqMode A j a w) =
      z ^ (-(β - j - 1)) • sqMode A j a (insertionScale D z w) := by
  refine insertionSqWeight_induction D (P := fun w =>
    insertionScale D z (sqMode A j a w) =
      z ^ (-(β - j - 1)) • sqMode A j a (insertionScale D z w)) ?_ ?_ ?_ w
  · intro α x hx
    rw [insertionScale_of_weight D (sqMode_weight ha hx j),
      insertionScale_of_weight D hx, map_smul, smul_smul, ← Complex.cpow_add _ _ hz]
    congr 2
    ring
  · simp
  · intro x y hx hy
    simp only [map_add, smul_add, hx, hy]

theorem sqAct_vacuum (j : ℤ) :
    sqAct A W.vacuum 0 j = (if j = -1 then (1 : ℂ) else 0) • LinearMap.id := by
  ext w
  rw [sqAct_apply, finsum_eq_single _ (-1) (fun i hi => by
    rw [A.vacuum_YM, mode_one, if_neg hi, LinearMap.zero_apply, smul_zero])]
  rw [A.vacuum_YM, mode_one, if_pos rfl, Module.End.one_apply]
  by_cases hj : j = -1
  · subst j
    simp only [sqBracketCoeffZ_vacuum_neg_one, one_smul, if_true,
      LinearMap.id_apply]
  · rw [sqBracketCoeffZ_vacuum_of_ne j hj, zero_smul, if_neg hj,
      zero_smul, LinearMap.zero_apply]

/-- The shifted conformal state, in the state VOA. -/
noncomputable def shiftedOmega (W : VertexOperatorAlgebra V) : V :=
  W.conformalVector - (W.centralCharge / 24) • W.vacuum

theorem sqMode_shiftedOmega (A : OrdVModule W M) (n : ℤ) :
    sqMode A (n + 1) (shiftedOmega W) = sqL A n := by
  rw [shiftedOmega, map_sub, map_smul,
    sqMode_of_mem_grading A W.conformal_mem,
    sqMode_of_mem_grading A W.vacuum_mem_grading_zero]
  simp only [show (2 : ℤ).toNat = 2 from rfl, Int.toNat_zero, sqAct_vacuum, sqL]
  by_cases hn : n = -2
  · subst n; norm_num
  · rw [if_neg hn, if_neg (by omega : n + 1 ≠ -1), zero_smul, smul_zero]

theorem shiftedOmega_weight : Lsq W 0 (shiftedOmega W) = (2 : ℂ) • shiftedOmega W := by
  rw [shiftedOmega, map_sub, map_smul, Lsq_zero_conformalVector,
    Lsq_vacuum_eq_zero W (by norm_num : (-1 : ℤ) ≤ 0), smul_zero, sub_zero]
  module

/-- Module Virasoro square modes shift square weight by minus their index. -/
theorem sqL_weight {α : ℂ} {w : M} (hw : sqL A 0 w = α • w) (n : ℤ) :
    sqL A 0 (sqL A n w) = (α - n) • sqL A n w := by
  have h := sqMode_weight (A := A) shiftedOmega_weight hw (n + 1)
  rw [sqMode_shiftedOmega] at h
  convert h using 1; push_cast; congr 1; ring

/-- Scaling intertwines every square Virasoro mode, on all module vectors. -/
theorem insertionScale_sqL (D : DirectSum.IsInternal (insertionSqWeight A))
    (n : ℤ) {z : ℂ} (hz : z ≠ 0) (w : M) :
    insertionScale D z (sqL A n w) = z ^ n • sqL A n (insertionScale D z w) := by
  have h := insertionScale_sqMode D shiftedOmega_weight (n + 1) hz w
  rw [sqMode_shiftedOmega] at h
  convert h using 1
  congr 1
  rw [show -((2 : ℂ) - ((n + 1 : ℤ) : ℂ) - 1) = (n : ℂ) by push_cast; ring,
    Complex.cpow_intCast]

end VOA.Huang.GenusOne.SquareModule
