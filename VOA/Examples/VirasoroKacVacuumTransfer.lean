/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroKacScalarRoot
import VOA.Examples.VirasoroDeterminantObstruction

/-!
# From an ordinary Verma Kac product to vacuum rigidity

The actual first translated coefficient supplies the vacuum determinant
multiplied by a weight-one determinant. Label separation excludes zeros in
that second determinant. The reduced finite Kac product has a simple zero,
so product and chain rules force the actual vacuum determinant's derivative
to be nonzero. The ordinary general Kac identity is an explicit hypothesis
here (it follows from the screening roots, `VirasoroScreeningKacRoots.lean`; the unconditional
rigidity theorem is `VirModule.minimal_graded_rigidity`).
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirSimple Deform
open scoped Classical
set_option maxHeartbeats 1200000

/-- The weight-one Kac product is nonzero strictly below the first vacuum
singular level. This uses the rational label threshold, not a character. -/
theorem kacWeightProduct_one_minimal_ne (p q n : ℕ) (hq : 2 ≤ q)
    (hpq : q < p) (hcop : p.Coprime q) (hn : n < (p-1)*(q-1)) :
    (kacWeightProduct ((p:ℂ)/q) n).eval 1 ≠ 0 := by
  simp only [kacWeightProduct,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro he
  have hone : VirMinimalArithmetic.minimalKacWeight p q (i.1.val+1) (i.2.val+1) = 1 := by
    apply Rat.cast_injective (α := ℂ)
    rw [← fusionKacWeight_minimal p q _ _ (by omega) (by omega)]
    simpa only [Nat.cast_add,Nat.cast_one,Rat.cast_one] using he.symm
  have hh := VirMinimalArithmetic.minimalKacWeight_one_above_vacuum_level
    hq hpq (by omega) (by omega) hcop hone
  have hi' := (Finset.mem_filter.mp hi).2
  omega

/-- Actual Verma determinants are differentiable along the rational charge
curve away from zero, by evaluation of their two-variable polynomial matrix. -/
theorem vermaKacGramDet_differentiableAt (n : ℕ) (h t : ℂ) (ht : t ≠ 0) :
    DifferentiableAt ℂ (fun z => (vermaGramMatrix (vermaBSACharge z) h n).det) t := by
  have he : (fun z => (vermaGramMatrix (vermaBSACharge z) h n).det) =
      (fun z => MvPolynomial.eval (fun i : Fin 2 => if i=0 then vermaBSACharge z else h)
        (vermaGramPolynomial n).det) := by
    funext z
    simpa using (vermaGramPolynomial_det_eval (vermaBSACharge z) h n).symm
  rw [he]
  have hd (P : MvPolynomial (Fin 2) ℂ) :
      DifferentiableAt ℂ (fun z => MvPolynomial.eval
        (fun i : Fin 2 => if i=0 then vermaBSACharge z else h) P) t := by
    induction P using MvPolynomial.induction_on with
    | C a => simp only [MvPolynomial.eval_C]; fun_prop
    | add P Q hP hQ => simpa only [map_add] using hP.add hQ
    | mul_X P i hP =>
      simp only [map_mul,MvPolynomial.eval_X]
      apply hP.mul
      split_ifs
      · unfold vermaBSACharge; fun_prop (disch := assumption)
      · fun_prop
  exact hd _

/-- A simple zero of a scalar along a differentiable parameter curve
transfers to the polynomial factor when its other factor is nonzero.
The argument needs no division of functions or assumed determinant order. -/
theorem polynomial_simple_of_curve_product (P : Polynomial ℂ)
    (c g s : ℂ → ℂ) (t A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hc : DifferentiableAt ℂ c t) (hg : DifferentiableAt ℂ g t)
    (hs : DifferentiableAt ℂ s t) (hgn : g t ≠ 0)
    (hs0 : s t = 0) (hsd : _root_.deriv s t ≠ 0)
    (he : (fun z => A * P.eval (c z) * g z) =ᶠ[nhds t] (fun z => B * s z)) :
    P.eval (c t) = 0 ∧ P.derivative.eval (c t) ≠ 0 := by
  have he0 := he.eq_of_nhds
  have hz : P.eval (c t) = 0 := by
    have hh : A * P.eval (c t) * g t = 0 := by simpa [hs0] using he0
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hgn)).resolve_left hA
  refine ⟨hz, ?_⟩
  intro hd
  have hleft := ((((P.hasDerivAt (c t)).comp t hc.hasDerivAt).const_mul A).mul hg.hasDerivAt)
  have hright := hs.hasDerivAt.const_mul B
  have hdEq := (hleft.congr_of_eventuallyEq he.symm).unique hright
  have hh : B * _root_.deriv s t = 0 := by
    simpa [hz,hd] using hdEq.symm
  exact (mul_ne_zero hB hsd) hh

/-- The full ordinary Verma Kac formula through the first vacuum level
implies an actual simple vacuum determinant zero. All multiplicity and
normalization transfers are proved; the displayed Kac identity is a
hypothesis here (supplied downstream by the screening construction). -/
theorem vacuum_simple_of_verma_kac (p q n : ℕ) (hq : 2 ≤ q)
    (hpq : q < p) (hcop : p.Coprime q) (hn : n+1 = (p-1)*(q-1))
    (hk : ∀ z : ℂ, z ≠ 0 → ∀ k ≤ n+1,
      (vermaWeightGramPolynomial (vermaBSACharge z) k).det =
        Polynomial.C (∏ w : VermaPartitions k, vermaDiagonalContraction w.val) *
          kacWeightProduct z k) :
    let P := (VirDeformModes.NormalOrdering.partitionGramPolynomial (n+1)).det
    P.eval (vermaBSACharge ((p:ℂ)/q)) = 0 ∧
      P.derivative.eval (vermaBSACharge ((p:ℂ)/q)) ≠ 0 := by
  let t : ℂ := (p:ℂ)/q
  have ht : t ≠ 0 := div_ne_zero (by exact_mod_cast (by omega : p ≠ 0))
    (by exact_mod_cast (by omega : q ≠ 0))
  have hg : (vermaGramMatrix (vermaBSACharge t) 1 n).det ≠ 0 := by
    rw [← vermaWeightDeterminant_eval, hk t ht n (by omega),
      Polynomial.eval_mul,Polynomial.eval_C]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun w _ => vermaDiagonalContraction_ne_zero w.val)
    · exact kacWeightProduct_one_minimal_ne p q n hq hpq hcop (by omega)
  obtain ⟨hs0,hsd⟩ := kacVacuumScalar_minimal_simple p q n hq hpq hcop hn
  apply polynomial_simple_of_curve_product _ vermaBSACharge
    (fun z => (vermaGramMatrix (vermaBSACharge z) 1 n).det)
    (fun z => kacVacuumScalar z n) t (2^Fintype.card (VermaPartitions n))
    (∏ w : VermaPartitions (n+1),vermaDiagonalContraction w.val)
  · exact pow_ne_zero _ (by norm_num)
  · exact Finset.prod_ne_zero_iff.mpr (fun w _ => vermaDiagonalContraction_ne_zero w.val)
  · unfold vermaBSACharge; fun_prop (disch := assumption)
  · exact vermaKacGramDet_differentiableAt n 1 t ht
  · exact kacScalarSubproduct_differentiable n _ t ht
  · exact hg
  · exact hs0
  · exact hsd
  · filter_upwards [eventually_ne_nhds ht] with z hz
    have hh := vacuumDeterminant_kac_coefficient z n (hk z hz (n+1) le_rfl)
    have hm := (Polynomial.evalRingHom (vermaBSACharge z)).map_det
      (VirDeformModes.NormalOrdering.partitionGramPolynomial (n+1))
    change ((VirDeformModes.NormalOrdering.partitionGramPolynomial (n+1)).det).eval
      (vermaBSACharge z) =
      ((VirDeformModes.NormalOrdering.partitionGramPolynomial (n+1)).map
        (Polynomial.eval (vermaBSACharge z))).det at hm
    rw [← hm] at hh
    exact hh

/-- The actual deformation and reconstruction theorems turn the proved
ordinary transfer into rigidity, conditional only on the full ordinary
Verma Kac identity. This theorem is not unconditional minimal-model rigidity. -/
theorem graded_rigidity_of_verma_kac (p q n : ℕ) (hq : 2 ≤ q)
    (hpq : q < p) (hcop : p.Coprime q) (hn : n+1 = (p-1)*(q-1))
    (hk : ∀ z : ℂ, z ≠ 0 → ∀ k ≤ n+1,
      (vermaWeightGramPolynomial (vermaBSACharge z) k).det =
        Polynomial.C (∏ w : VermaPartitions k, vermaDiagonalContraction w.val) *
          kacWeightProduct z k) :
    IsRigidGraded (virasoroSimple (vermaBSACharge ((p:ℂ)/q))) := by
  obtain ⟨hz,hd⟩ := vacuum_simple_of_verma_kac p q n hq hpq hcop hn hk
  exact VirDeformModes.NormalOrdering.graded_rigidity_of_simple_determinant _ (n+1) hz hd

end VOA.InverseDS.VirasoroVerma
