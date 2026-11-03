import VOA.Modules.LogTensorContraNilModes
import VOA.Core.InternalGradingOperator
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Actual logarithmic L(0) and opposite-coordinate exponentials

The semisimple grading exponential and the finite Jordan exponential define an
invertible operator on the actual generalized module. Their product has the
expected group law. Combining it with the locally nilpotent L(1) exponential
defines the genuine opposite-coordinate state operator at a chosen log branch.
-/
namespace VOA.LogTensor.Contra
open Module (End)
open VOA.Huang.LiRegular
open scoped BigOperators
noncomputable section
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- exp(c L(0)_ss), defined on the internal generalized weight decomposition. -/
def scalarExp (N : LogVModule W M) (c : ℂ) : End ℂ M := by
  classical
  exact internalWeightOperator N.weight N.isInternal (fun α => Complex.exp (c*α))

theorem scalarExp_apply_of_mem (N : LogVModule W M) (c : ℂ) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : scalarExp N c x = Complex.exp (c*α) • x := by
  classical
  exact Module.End.mem_eigenspace_iff.mp
    (grading_le_eigenspace_internalWeightOperator N.weight N.isInternal
      (fun α => Complex.exp (c*α)) α hx)

theorem scalarExp_add (N : LogVModule W M) (c d : ℂ) :
    scalarExp N c * scalarExp N d = scalarExp N (c+d) := by
  apply N.ext_on_weight
  intro α x hx
  change scalarExp N c (scalarExp N d x) = scalarExp N (c+d) x
  rw [scalarExp_apply_of_mem N d hx,map_smul,
    scalarExp_apply_of_mem N c hx,scalarExp_apply_of_mem N (c+d) hx,smul_smul,
    ← Complex.exp_add]
  congr 2
  ring

theorem scalarExp_zero (N : LogVModule W M) : scalarExp N 0 = 1 := by
  apply N.ext_on_weight
  intro α x hx
  simp only [scalarExp_apply_of_mem N 0 hx,zero_mul,Complex.exp_zero,
    one_smul,Module.End.one_apply]

/-- The inverse grading exponential is obtained by changing c to -c. -/
def scalarExpEquiv (N : LogVModule W M) (c : ℂ) : M ≃ₗ[ℂ] M where
  toLinearMap := scalarExp N c
  invFun := scalarExp N (-c)
  left_inv := fun x => by
    have h := DFunLike.congr_fun (scalarExp_add N (-c) c) x
    simpa [scalarExp_zero] using h
  right_inv := fun x => by
    have h := DFunLike.congr_fun (scalarExp_add N c (-c)) x
    simpa [scalarExp_zero] using h

/-- The actual exponential exp(c L(0)), including the Jordan part. -/
def L0exp (N : LogVModule W M) (c : ℂ) : M ≃ₗ[ℂ] M :=
  (nilExp N c).trans (scalarExpEquiv N c)

theorem L0exp_apply_of_mem (N : LogVModule W M) (c : ℂ) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : L0exp N c x = Complex.exp (c*α) • nilExp N c x :=
  scalarExp_apply_of_mem N c (nilExp_mem_weight N c hx)

theorem L0exp_mem_weight (N : LogVModule W M) (c : ℂ) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : L0exp N c x ∈ N.weight α := by
  rw [L0exp_apply_of_mem N c hx]
  exact (N.weight α).smul_mem _ (nilExp_mem_weight N c hx)

theorem L0exp_add (N : LogVModule W M) (c d : ℂ) :
    (L0exp N d).trans (L0exp N c) = L0exp N (c+d) := by
  apply LinearEquiv.toLinearMap_injective
  apply N.ext_on_weight
  intro α x hx
  change L0exp N c (L0exp N d x) = L0exp N (c+d) x
  rw [L0exp_apply_of_mem N c (L0exp_mem_weight N d hx),
    L0exp_apply_of_mem N d hx,map_smul,L0exp_apply_of_mem N (c+d) hx,
    nilExp_add,smul_smul,← Complex.exp_add]
  congr 2
  ring

theorem L0exp_finite (N : LogVModule W M) (c : ℂ) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) {k : ℕ} (hk : (N.L0nil ^ k) x = 0) :
    L0exp N c x = Complex.exp (c*α) •
      ∑ j ∈ Finset.range k, (c^j/(j.factorial : ℂ)) • (N.L0nil^j) x := by
  rw [L0exp_apply_of_mem N c hx,nilExp_finite N c hk]

/-- exp(c L(1)) is finite on every vector of a lower-bounded generalized module. -/
def L1exp (N : C2Rigid.GWModule W M) (c : ℂ) : M ≃ₗ[ℂ] M where
  toLinearMap := expOp (L1_locallyNilpotent N) c
  invFun := expOp (L1_locallyNilpotent N) (-c)
  left_inv := expOp_cancel_neg (L1_locallyNilpotent N) c
  right_inv := expOp_neg_cancel (L1_locallyNilpotent N) c

/-- The opposite-coordinate state map e^(z L(1)) e^(((2r+1)πi-2 log z)L(0)). -/
def oppositeCoordinate (N : LogVModule W M) (r : ℤ) (ell : ℂ) : M ≃ₗ[ℂ] M :=
  (L0exp N (((2*r+1 : ℤ) : ℂ) * (Real.pi * Complex.I) - 2*ell)).trans
    (L1exp N.toGW (Complex.exp ell))

end
end VOA.LogTensor.Contra
