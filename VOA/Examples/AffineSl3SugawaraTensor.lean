/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3VacuumWeightOne

/-!
# The actual inverse trace tensor for sl3 Sugawara

Opposite root generators have inverse pairing one. The Cartan inverse is
one third of the matrix with diagonal two and off-diagonal one. This is
verified against the actual trace table and trace-dual generators. The
raised structure tensor is alternating in its two exterior indices.
-/
namespace VOA.AffineSl3
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

/-- Inverse of the trace Gram matrix in the ordered eight-generator basis. -/
def kappaInv : Fin 8 → Fin 8 → ℂ
  | 0,3 => 1 | 3,0 => 1
  | 1,4 => 1 | 4,1 => 1
  | 2,5 => 1 | 5,2 => 1
  | 6,6 => 2/3 | 7,7 => 2/3
  | 6,7 => 1/3 | 7,6 => 1/3
  | _,_ => 0

/-- The inverse trace tensor is symmetric, including its non-diagonal Cartan block. -/
theorem kappaInv_symm (a b : Fin 8) : kappaInv a b=kappaInv b a := by
  fin_cases a <;> fin_cases b <;> norm_num [kappaInv]

/-- The actual trace Gram table is symmetric. -/
theorem kappa_symm (a b : Fin 8) : formTable a b=formTable b a := by
  rw [← form_generator_eq_table,← form_generator_eq_table]
  exact form_invariant.symm _ _

/-- Multiplying the trace matrix by the proposed inverse gives the identity. -/
theorem kappaInv_kappa (a c : Fin 8) :
    (∑ b,formTable a b*kappaInv b c)=if a=c then 1 else 0 := by
  fin_cases a <;> fin_cases c <;>
    norm_num [Fin.sum_univ_succ,Fin.succ,formTable,kappaInv]

/-- Expanding an actual trace-dual generator gives precisely a row of the inverse tensor. -/
theorem dualGenerator_expand (a : Fin 8) :
    dualGenerator a=∑ b,kappaInv a b • generator b := by
  fin_cases a <;>
    simp [dualGenerator,generator,kappaInv,Fin.sum_univ_succ] <;> module

/-- Structure constants with the first index raised by the actual inverse trace form. -/
def graised (a c d : Fin 8) : ℂ := ∑ b,kappaInv a b*structureConstant b c d

/-- Raised structure coefficients are actual trace pairings of a bracket
with the dual generator. This ties the coordinate tensor to Lie invariance. -/
theorem graised_eq_form (a c d : Fin 8) :
    graised a c d=form ⁅dualGenerator a,generator c⁆ (dualGenerator d) := by
  rw [dualGenerator_expand, sum_lie]
  simp only [smul_lie,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    RingHom.id_apply,form_dual_coordinates,smul_eq_mul]
  rfl

/-- Invariance and symmetry of the actual trace form make the raised tensor
antisymmetric in its exterior indices, without enumerating triples. -/
theorem graised_antisymm (a c d : Fin 8) : graised a c d= -graised d c a := by
  rw [graised_eq_form,graised_eq_form,form_invariant.invariant]
  rw [← lie_skew (generator c) (dualGenerator d),map_neg]
  rw [form_invariant.symm (dualGenerator a) ⁅dualGenerator d,generator c⁆]

/-- The symmetric inverse tensor contracts an antisymmetric bracket to zero. -/
theorem kappaInv_fabc_antisymm_zero (d : Fin 8) :
    (∑ a,∑ b,kappaInv a b*structureConstant a b d)=0 := by
  have h : (∑ a,∑ b,kappaInv a b*structureConstant a b d)=
      -(∑ a,∑ b,kappaInv a b*structureConstant a b d) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [kappaInv_symm b a,structureConstant_antisymm b a d]
    ring
  have h2 : (2 : ℂ)*(∑ a,∑ b,kappaInv a b*structureConstant a b d)=0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Coordinate form of the actual adjoint Casimir: the normal-ordering
structure contraction has coefficient six, independently of the affine level. -/
theorem struct_casimir_contract (c e : Fin 8) :
    (∑ a,∑ d,(∑ b,kappaInv a b*structureConstant b c d)*structureConstant a d e)=
      if c=e then (6 : ℂ) else 0 := by
  have h := congrArg (fun x : Sl3 => coordinatesLinear x e) (adjoint_casimir (generator c))
  have hc (x : Sl3) : coordinatesLinear x = coordinates x := rfl
  simp only [dualGenerator_expand,sum_lie,smul_lie,lie_sum,lie_smul,generator_bracket,
    map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    RingHom.id_apply,smul_eq_mul] at h
  simp only [hc,coordinates_generator,Pi.single_apply,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true,Finset.mul_sum] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    ring
  · simp only [eq_comm]
end
end VOA.AffineSl3
