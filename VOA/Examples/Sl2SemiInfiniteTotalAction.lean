/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteRelative
import VOA.Examples.Sl2SemiInfiniteGhostAffine

/-!
# The diagonal affine action on matter tensored with three ghost pairs

The actual total-current fields act by the sum of the two tensor-factor actions.
Their full integer-mode commutator has level `k + 4`. In particular their zero
modes form the horizontal sl2 action used in the relative invariant condition.
No matter translation hypothesis is needed for this result.
-/

namespace VOA.Sl2SemiInfinite
open Module (End)
open AffineVOA
open scoped BigOperators TensorProduct
universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- Every total-current mode is the sum of the actual factor modes. -/
theorem totalCurrentMode_tmul (A : AffineSl2Action V k) (a : Fin 3) (n : ℤ)
    (x : M) (y : Sl2GhostSpace) :
    mode (TensorVA.tenY V sl2GhostSVA (totalCurrentState A a)) n (x ⊗ₜ[ℂ] y) =
      mode (V.Y (A.current a)) n x ⊗ₜ[ℂ] y +
        x ⊗ₜ[ℂ] mode (ghostCurrentField a) n y := by
  unfold totalCurrentState
  rw [map_add, mode_add, LinearMap.add_apply]
  change TensorVA.tenY V sl2GhostSVA (A.current a ⊗ₜ[ℂ] sl2GhostSVA.vacuum)
      (-n - 1) (x ⊗ₜ[ℂ] y) +
    TensorVA.tenY V sl2GhostSVA (V.vacuum ⊗ₜ[ℂ] ghostCurrent a)
      (-n - 1) (x ⊗ₜ[ℂ] y) = _
  rw [tenY_left_unit, tenY_right_unit_even V sl2GhostSVA (ghostCurrent_even a)]
  rfl

/-- Full diagonal current commutator; the matter and ghost levels add. -/
theorem totalCurrentMode_commutator (A : AffineSl2Action V k) (a b : Fin 3) (m n : ℤ) :
    mode (TensorVA.tenY V sl2GhostSVA (totalCurrentState A a)) m *
        mode (TensorVA.tenY V sl2GhostSVA (totalCurrentState A b)) n -
      mode (TensorVA.tenY V sl2GhostSVA (totalCurrentState A b)) n *
        mode (TensorVA.tenY V sl2GhostSVA (totalCurrentState A a)) m =
      (∑ c, fabc a b c •
        mode (TensorVA.tenY V sl2GhostSVA (totalCurrentState A c)) (m + n)) +
      if m + n = 0 then ((m : ℂ) * (k + 4) * kappa a b) • LinearMap.id else 0 := by
  apply TensorProduct.ext'
  intro x y
  have hM := congrArg (fun f : End ℂ M => f x) (A.current_comm a b m n)
  have hG := congrArg (fun f : End ℂ Sl2GhostSpace => f y)
    (ghostCurrent_mode_commutator a b m n)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at hM hG
  simp only [LinearMap.sub_apply, Module.End.mul_apply, totalCurrentMode_tmul,
    map_add, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  have heq :
      ((mode (V.Y (A.current a)) m (mode (V.Y (A.current b)) n x) ⊗ₜ[ℂ] y +
          mode (V.Y (A.current b)) n x ⊗ₜ[ℂ] mode (ghostCurrentField a) m y) +
        (mode (V.Y (A.current a)) m x ⊗ₜ[ℂ] mode (ghostCurrentField b) n y +
          x ⊗ₜ[ℂ] mode (ghostCurrentField a) m (mode (ghostCurrentField b) n y))) -
      ((mode (V.Y (A.current b)) n (mode (V.Y (A.current a)) m x) ⊗ₜ[ℂ] y +
          mode (V.Y (A.current a)) m x ⊗ₜ[ℂ] mode (ghostCurrentField b) n y) +
        (mode (V.Y (A.current b)) n x ⊗ₜ[ℂ] mode (ghostCurrentField a) m y +
          x ⊗ₜ[ℂ] mode (ghostCurrentField b) n (mode (ghostCurrentField a) m y))) =
      (mode (V.Y (A.current a)) m (mode (V.Y (A.current b)) n x) -
        mode (V.Y (A.current b)) n (mode (V.Y (A.current a)) m x)) ⊗ₜ[ℂ] y +
      x ⊗ₜ[ℂ] (mode (ghostCurrentField a) m (mode (ghostCurrentField b) n y) -
        mode (ghostCurrentField b) n (mode (ghostCurrentField a) m y)) := by
    simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [heq, hM, hG]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_add, Finset.sum_add_distrib]
  by_cases hmn : m + n = 0
  · simp only [if_pos hmn, LinearMap.smul_apply, LinearMap.id_apply,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    have hscalar : ((m : ℂ) * k * kappa a b) + ((m : ℂ) * 4 * kappa a b) =
        (m : ℂ) * (k + 4) * kappa a b := by ring
    rw [← hscalar, add_smul, TensorProduct.add_tmul]
    abel
  · simp only [if_neg hmn, LinearMap.zero_apply, TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, add_zero]

/-- The total horizontal zero modes satisfy the sl2 bracket. -/
theorem totalCurrentZero_commutator (A : AffineSl2Action V k) (a b : Fin 3) :
    totalCurrentZero A a * totalCurrentZero A b -
      totalCurrentZero A b * totalCurrentZero A a =
      ∑ c, fabc a b c • totalCurrentZero A c := by
  simpa only [totalCurrentZero, zero_add, Int.cast_zero, zero_mul, ite_true,
    zero_smul, add_zero] using totalCurrentMode_commutator A a b 0 0

/-- The actual total current states form an affine sl2 action at level `k + 4`. -/
noncomputable def totalAffineAction (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V)
    (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    AffineSl2Action (matterGhostSVA V hV hg) (k + 4) where
  current := totalCurrentState A
  current_weight a := by
    apply Submodule.add_mem
    · simpa only [add_zero] using tmul_mem_tenGrading_add V sl2GhostSVA
        (A.current_weight a) sl2GhostSVA.vacuum_mem
    · simpa only [zero_add] using tmul_mem_tenGrading_add V sl2GhostSVA
        V.vacuum_mem (ghostCurrent_weight a)
  current_even := totalCurrentState_even A
  current_comm := totalCurrentMode_commutator A

end VOA.Sl2SemiInfinite
