import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Actual local endomorphisms on a finite tensor product

A local endomorphism is the tensor product of identities with the selected
factor replaced. These maps are linear and multiplicative in the selected
endomorphism, and operators at distinct sites commute. No current-module
or cyclicity assertion is assumed.
-/

namespace VOA.DeligneAudit.D1TensorG

open scoped TensorProduct

noncomputable section

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
variable {W : Type*} [AddCommGroup W] [Module K W]

abbrev Tensor := ⨂[K] _ : ι, W

/-- Apply an endomorphism at one actual tensor factor. -/
def localOp (j : ι) (A : Module.End K W) : Module.End K (Tensor (K := K) (ι := ι) (W := W)) :=
  PiTensorProduct.map (Function.update (fun _ : ι => (1 : Module.End K W)) j A)

theorem localOp_tprod (j : ι) (A : Module.End K W) (v : ι → W) :
    localOp j A (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (Function.update v j (A (v j))) := by
  rw [localOp, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = j
  · subst i
    simp
  · simp [Function.update_of_ne h]

theorem localOp_add (j : ι) (A B : Module.End K W) :
    localOp j (A + B) = localOp j A + localOp j B :=
  PiTensorProduct.map_update_add (R := K)
    (f := fun _ : ι => (1 : Module.End K W)) j A B

theorem localOp_smul (j : ι) (c : K) (A : Module.End K W) :
    localOp j (c • A) = c • localOp j A :=
  PiTensorProduct.map_update_smul (R := K)
    (f := fun _ : ι => (1 : Module.End K W)) j c A

theorem localOp_zero (j : ι) : localOp j (0 : Module.End K W) = 0 := by
  have h := localOp_smul j (0 : K) (0 : Module.End K W)
  simpa only [zero_smul] using h

/-- The exact linear map on endomorphisms at a selected site. -/
def localMap (j : ι) : Module.End K W →ₗ[K] Module.End K (Tensor (K := K) (ι := ι) (W := W)) where
  toFun := localOp j
  map_add' := localOp_add j
  map_smul' := localOp_smul j

theorem localMap_apply (j : ι) (A : Module.End K W) : localMap j A = localOp j A := rfl

theorem localOp_mul (j : ι) (A B : Module.End K W) :
    localOp j (A * B) = localOp j A * localOp j B := by
  rw [localOp, localOp, localOp, ← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = j
  · subst i
    simp
  · simp [Function.update_of_ne h]

/-- Operators on different tensor factors commute exactly. -/
theorem localOp_comm {i j : ι} (hij : i ≠ j) (A B : Module.End K W) :
    localOp i A * localOp j B = localOp j B * localOp i A := by
  rw [localOp, localOp, ← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [Function.update_of_ne hij]
  · by_cases hj : k = j
    · subst k
      simp [Function.update_of_ne hij.symm]
    · simp [Function.update_of_ne hi, Function.update_of_ne hj]

end
end VOA.DeligneAudit.D1TensorG

#print axioms VOA.DeligneAudit.D1TensorG.localOp_tprod
#print axioms VOA.DeligneAudit.D1TensorG.localOp_mul
#print axioms VOA.DeligneAudit.D1TensorG.localOp_comm
