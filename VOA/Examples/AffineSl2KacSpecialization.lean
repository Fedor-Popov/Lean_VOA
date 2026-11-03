/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2KacProduct
import VOA.Examples.VirasoroWardClosedKernel

/-!
# Full actual affine Kac determinant at every complex level

The nonreal calculation is an identity between continuous polynomial scalar
functions. Extending that identity to all parameters preserves colliding
factor multiplicities without summing dimensions of colliding nullspaces.
At critical level the explicit oscillator prefactor can vanish; the formula
still holds and no noncritical nondegeneracy is asserted there.
-/
namespace VOA.Wak.Charged
open Polynomial Filter Topology
open AffineVOA.HighestModule
noncomputable section
local instance kacAllFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c
local instance kacAllDecidable (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Scalar evaluation of the actual highest-weight determinant is the
original two-variable highest-word determinant at the same parameters. -/
theorem weightDeterminant_eval_highest (k h : ℂ) (n : ℕ) (c : ℤ) :
    (weightDeterminant k n c).eval h=MvPolynomial.eval ![k,h] (highestDeterminant n c) := by
  change Polynomial.evalRingHom h (weightGramPolynomial k n c).det=_
  rw [RingHom.map_det]
  change ((weightGramPolynomial k n c).map (Polynomial.eval h)).det=_
  rw [weightGramPolynomial_eval]
  exact (highestDeterminant_verma k h n c).symm

/-- The actual determinant, evaluated at fixed highest weight, is continuous
in shifted level because its entries are the proved two-variable polynomials. -/
theorem weightDeterminant_eval_continuous (n : ℕ) (c : ℤ) (h : ℂ) :
    Continuous (fun t : ℂ => (weightDeterminant (t-2) n c).eval h) := by
  simp only [weightDeterminant_eval_highest]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- Every pure derivative weight depends continuously on the level. -/
theorem annihilationWeight_continuous (v : Fin 3×ℕ) : Continuous (fun k : ℂ => annihilationWeight k v) := by
  unfold annihilationWeight
  split_ifs <;> fun_prop

/-- The exact finite oscillator multiplier is continuous in the level,
including at critical level where some factors may vanish. -/
theorem derivativeMultiplier_continuous (w : List (Fin 3×ℕ)) (e : Occupation) :
    Continuous (fun k : ℂ => derivativeMultiplier k w e) := by
  induction w generalizing e with
  | nil => exact continuous_const
  | cons v w ih =>
    exact ((annihilationWeight_continuous v).mul continuous_const).mul (ih _)

/-- The evaluated finite Kac product is continuous even when distinct roots
collide. Its index set and exponents do not depend on the parameter. -/
theorem affineKacProduct_eval_continuous (n : ℕ) (c : ℤ) (h : ℂ) :
    Continuous (fun t : ℂ => (affineKacProduct t n c).eval h) := by
  simp only [affineKacProduct,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,realRootWeight]
  fun_prop

/-- The complete normalized actual affine Verma Kac formula holds at EVERY
complex shifted level and joint block. All roots, full descendant lower
multiplicities, degree exhaustion and specialization are proved internally. -/
theorem weightDeterminant_eq_affineKacProduct_all (t : ℂ) (n : ℕ) (c : ℤ) :
    weightDeterminant (t-2) n c=
      Polynomial.C (∏ i : JointIndex n c,derivativeMultiplier (t-2) i.val.toMultiset.toList.reverse 0)*
        affineKacProduct t n c := by
  apply Polynomial.funext
  intro h
  rw [Polynomial.eval_mul,Polynomial.eval_C]
  have hc : Continuous (fun z : ℂ =>
      (∏ i : JointIndex n c,derivativeMultiplier (z-2) i.val.toMultiset.toList.reverse 0)*
        (affineKacProduct z n c).eval h) := by
    apply Continuous.mul
    · apply continuous_finset_prod
      intro i hi
      exact (derivativeMultiplier_continuous _ _).comp (continuous_id.sub continuous_const)
    · exact affineKacProduct_eval_continuous n c h
  haveI := mem_closure_iff_nhdsWithin_neBot.mp (VirasoroWardTopology.nonreal_dense t)
  apply tendsto_nhds_unique_of_eventuallyEq (l:=nhdsWithin t {z : ℂ | z.im≠0})
    ((weightDeterminant_eval_continuous n c h).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := congrArg (Polynomial.eval h) (weightDeterminant_eq_affineKacProduct z hz n c)
  simpa only [Polynomial.eval_mul,Polynomial.eval_C] using he

end
end VOA.Wak.Charged
