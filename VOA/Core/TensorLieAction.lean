/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Tensoring two explicit Lie actions

This construction takes actual Lie homomorphisms instead of relying on a
chosen typeclass action on each carrier. It is useful when several different
representations live on the same underlying vector space.
-/
namespace VOA
noncomputable section
open scoped TensorProduct
open Module (End)
variable {L V W : Type*} [LieRing L] [LieAlgebra ℂ L]
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The sum of the two factor actions on their algebraic tensor product. -/
def tensorLieAction (R : L →ₗ⁅ℂ⁆ End ℂ V) (S : L →ₗ⁅ℂ⁆ End ℂ W) :
    L →ₗ⁅ℂ⁆ End ℂ (V ⊗[ℂ] W) where
  toFun x := (R x).rTensor W + (S x).lTensor V
  map_add' x y := by simp [map_add, LinearMap.rTensor_add, LinearMap.lTensor_add]; abel
  map_smul' c x := by simp [map_smul, LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]
  map_lie' {x y} := by
    ext v w
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.coe_comp,
      LieHom.map_lie, Ring.lie_def, LinearMap.add_apply, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      map_add, TensorProduct.add_tmul, TensorProduct.tmul_add,
      TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel

/-- On a pure tensor the action is the usual two-term Leibniz rule. -/
theorem tensorLieAction_tmul (R : L →ₗ⁅ℂ⁆ End ℂ V) (S : L →ₗ⁅ℂ⁆ End ℂ W)
    (x : L) (v : V) (w : W) :
    tensorLieAction R S x (v ⊗ₜ[ℂ] w)=R x v ⊗ₜ w+v ⊗ₜ S x w := by
  simp [tensorLieAction]

/-- Scalar actions add their eigenvalues on the full tensor carrier. -/
theorem tensorLieAction_scalar (R : L →ₗ⁅ℂ⁆ End ℂ V) (S : L →ₗ⁅ℂ⁆ End ℂ W)
    (x : L) (a b : ℂ) (ha : R x=a • 1) (hb : S x=b • 1) :
    tensorLieAction R S x=(a+b) • 1 := by
  ext v w
  simp [tensorLieAction_tmul, ha, hb, TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul]

/-- Eigenvalues also add for specified eigenvectors in the two factors. -/
theorem tensorLieAction_eigen (R : L →ₗ⁅ℂ⁆ End ℂ V) (S : L →ₗ⁅ℂ⁆ End ℂ W)
    (x : L) (v : V) (w : W) (a b : ℂ) (ha : R x v=a • v) (hb : S x w=b • w) :
    tensorLieAction R S x (v ⊗ₜ[ℂ] w)=(a+b) • (v ⊗ₜ[ℂ] w) := by
  simp [tensorLieAction_tmul, ha, hb, TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul]

/-- Over the complex field, a pure tensor of two nonzero vectors is nonzero. -/
theorem complex_tmul_ne_zero {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    v ⊗ₜ[ℂ] w ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  intro h
  have hh := congrArg (fun z => TensorProduct.lid ℂ W ((f.rTensor W) z)) h
  simp [hf] at hh
  exact hw hh

end
end VOA
