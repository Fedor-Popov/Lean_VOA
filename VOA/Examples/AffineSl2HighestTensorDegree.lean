/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2TensorHighest

/-!
# The full affine degree action on highest tensor models

The shifted energy is minus (oscillator energy plus ghost charge)/d.
Tensor sums provide the actual affine derivation, annihilating the tensor
highest vector. This retains the degree generator needed for the universal
induced highest module, in addition to its current commutators.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial AffineVOA
open scoped TensorProduct
noncomputable section

/-- The actual degree generator for a dilated and shifted vacuum action. -/
def shiftedDegree (d : ℕ) : End ℂ WakFock := -((d : ℂ)⁻¹) • (Dwt+Dch)

/-- Energy plus ghost charge has exactly the unscaled loop degree on all
shifted currents; the central correction commutes with it. -/
theorem energyCharge_shiftedJ (d : ℕ) (k : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅Dwt+Dch,shiftedJ d k a n⁆=(-((d : ℂ)*(n : ℂ))) • shiftedJ d k a n := by
  rcases fin3_cases a with rfl|rfl|rfl
  · rw [shiftedJ_E,← J_E k 0,add_lie,degree_J,charge_J,J_E]
    norm_num [colourCharge,Fin.ext_iff]
    module
  · rw [shiftedJ_F,← J_F,add_lie,degree_J,charge_J,J_F]
    norm_num [colourCharge,Fin.ext_iff]
    module
  · rw [shiftedJ_H,lie_add,add_lie,← J_H,degree_J,charge_J,J_H]
    have hs : ⁅Dwt+Dch,k • (1 : End ℂ WakFock)⁆=0 := by rw [lie_smul,lie_one',smul_zero]
    by_cases hn : n=0
    · subst n; simp [hs,colourCharge,Fin.ext_iff]
    · simp only [if_neg hn,lie_zero,add_zero]
      norm_num [colourCharge,Fin.ext_iff]

/-- Every shifted current has its required affine degree n at positive
dilation, with the reciprocal scalar cancellation proved explicitly. -/
theorem shiftedDegree_comm (d : ℕ) (hd : 0<d) (k : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅shiftedDegree d,shiftedJ d k a n⁆=(n : ℂ) • shiftedJ d k a n := by
  have hd0 : (d : ℂ)≠0 := by exact_mod_cast (ne_of_gt hd)
  rw [shiftedDegree,smul_lie,energyCharge_shiftedJ,smul_smul]
  congr 1
  field_simp

/-- The actual shifted degree kills polynomial one. -/
theorem shiftedDegree_one (d : ℕ) : shiftedDegree d (1 : WakFock)=0 := by
  simp [shiftedDegree,Dwt,Dch,Eul_one']

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Degree acts on a tensor product by its two factor contributions. -/
def tensorDegree (D : End ℂ V) (E : End ℂ W) : End ℂ (V ⊗[ℂ] W) :=
  D.rTensor W+E.lTensor V

/-- Tensor degree and tensor currents obey the same degree commutator.
All mixed-factor terms vanish by actual operator commutation. -/
theorem tensorDegree_comm (D : End ℂ V) (E : End ℂ W)
    (A : Fin 3→ℤ→End ℂ V) (B : Fin 3→ℤ→End ℂ W)
    (hA : ∀ a n,⁅D,A a n⁆=(n : ℂ) • A a n)
    (hB : ∀ a n,⁅E,B a n⁆=(n : ℂ) • B a n)
    (a : Fin 3) (n : ℤ) :
    ⁅tensorDegree D E,tensorCurrent A B a n⁆=(n : ℂ) • tensorCurrent A B a n := by
  let F := End.rTensorAlgHom ℂ V W
  let G := End.lTensorAlgHom ℂ W V
  have ha := congrArg F (hA a n)
  have hb := congrArg G (hB a n)
  simp only [Ring.lie_def,map_sub,map_mul,map_smul] at ha hb
  have h1 := (current_tensor_factors_commute D (B a n)).eq
  have h2 := (current_tensor_factors_commute (A a n) E).eq
  change F D*G (B a n)=G (B a n)*F D at h1
  change F (A a n)*G E=G E*F (A a n) at h2
  change (F D+G E)*(F (A a n)+G (B a n))-
    (F (A a n)+G (B a n))*(F D+G E)=(n : ℂ) • (F (A a n)+G (B a n))
  have he : (F D+G E)*(F (A a n)+G (B a n))-
      (F (A a n)+G (B a n))*(F D+G E)=
      (F D*F (A a n)-F (A a n)*F D)+(G E*G (B a n)-G (B a n)*G E) := by
    simp only [add_mul,mul_add]
    rw [h1,h2]
    abel
  rw [he,ha,hb,smul_add]

/-- The actual degree operator on the triple highest tensor carrier. -/
def highestTensorDegree : End ℂ HighestTensorFock :=
  tensorDegree (tensorDegree (shiftedDegree 2) (shiftedDegree 3)) (shiftedDegree 4)

/-- Every actual triple current has the required affine degree. -/
theorem highestTensorDegree_comm (a b c : ℂ) (i : Fin 3) (n : ℤ) :
    ⁅highestTensorDegree,highestTensorJ a b c i n⁆=(n : ℂ) • highestTensorJ a b c i n :=
  tensorDegree_comm _ _ _ _
    (tensorDegree_comm _ _ _ _ (shiftedDegree_comm 2 (by decide) a)
      (shiftedDegree_comm 3 (by decide) b)) (shiftedDegree_comm 4 (by decide) c) i n

/-- The tensor highest vector has degree zero. -/
theorem highestTensorDegree_vacuum : highestTensorDegree highestTensorVacuum=0 := by
  simp [highestTensorDegree,highestTensorVacuum,tensorDegree,shiftedDegree_one]

end
end VOA.Wak.Charged
