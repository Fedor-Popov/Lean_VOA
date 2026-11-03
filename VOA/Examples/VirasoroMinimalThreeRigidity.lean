/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroThreeMovingNormIdentity
import VOA.Examples.VirasoroBoundaryRigidity

/-!
# From the moving-source norm identity to M(p,3) rigidity

Earlier diagonals stay nonzero in a neighborhood of the minimal parameter.
The actual norm identity can therefore be differentiated there. Its scalar
factor vanishes simply, and its remaining factor is the proved nonzero Ward
residual. Radical cancellation identifies this with the fixed charge norm
derivative, which supplies the existing graded-rigidity theorem.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirDeformModes.NormalOrdering Filter Topology

/-- The central-charge curve is differentiable at every nonzero parameter. -/
theorem threeMovingCharge_differentiable (t : ℂ) (ht : t≠0) :
    DifferentiableAt ℂ vermaBSACharge t := by
  unfold vermaBSACharge
  fun_prop (disch := assumption)

/-- The actual norm of an earlier moving coefficient is differentiable:
its finite fixed-level PBW coordinates and all canonical word pairings are
ordinary differentiable scalar functions. -/
theorem threeMovingStateNorm_differentiable (t : ℂ) (ht : t≠0) (r : ℕ)
    (hd : ∀ j, 0<j → j≤r → threeMovingDiagonal t j≠0) :
    DifferentiableAt ℂ (fun z => (VirGram4.canB (vermaBSACharge z)).form
      (threeMovingVacuum z r) (threeMovingVacuum z r)) t := by
  classical
  let w (i : VermaPartitions r) := chargeWordExpression (negWord 0 0 i.val)
  let v (i : VermaPartitions r) (z : ℂ) := threeLevelCoordinate r i (threeMovingState 0 z r)
  have hv (i : VermaPartitions r) : DifferentiableAt ℂ (v i) t :=
    threeMovingState_coordinate_differentiable t ht r hd _
  have hc := threeMovingCharge_differentiable t ht
  have he (z : ℂ) : wordExpressionEval (vermaBSACharge z) (∑ i, v i z • w i)=threeMovingVacuum z r := by
    have hrec := congrArg chargeWordExpression
      (threeLevelReconstruct_eq r (threeMovingState 0 z r) (threeMovingState_level 0 z r))
    have hrec' : (∑ i, v i z • w i)=chargeWordExpression (threeMovingState 0 z r) := by
      simpa only [threeLevelReconstruct,LinearMap.sum_apply,LinearMap.smulRight_apply,
        map_sum,map_smul,w,v] using hrec
    rw [hrec',chargeWordExpression_eval,chargeTransport_threeMovingState]
    rfl
  simp only [← he,← wordExpressionPair_eval,map_sum,map_smul,LinearMap.sum_apply,
    LinearMap.smul_apply,Polynomial.eval_finsetSum,Polynomial.eval_smul,smul_eq_mul,
    Finset.mul_sum]
  apply DifferentiableAt.fun_sum
  intro i hi
  apply DifferentiableAt.fun_sum
  intro j hj
  fun_prop

/-- The undivided actual norm sum remains differentiable at a terminal
resonance: it only uses earlier coefficient norms. -/
theorem threeMovingNormSum_differentiable (t : ℂ) (ht : t≠0) (r : ℕ)
    (hd : ∀ j, 0<j → j<r → threeMovingDiagonal t j≠0) :
    DifferentiableAt ℂ (fun z => threeMovingNormSum z r) t := by
  unfold threeMovingNormSum
  apply DifferentiableAt.fun_sum
  intro j hj
  have hA := threeMovingCoefficient_differentiable t ht r j
  have hw := threeMovingWeight_differentiable t ht
  have hq := threeMovingStateNorm_differentiable t ht j
    (fun k hk hkj => hd k hk (by omega))
  fun_prop

/-- Only finitely many earlier denominators occur, so their nonvanishing
persists on a genuine neighborhood of the minimal parameter. -/
theorem threeMoving_interior_eventually (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    ∀ᶠ t in 𝓝 ((3:ℂ)/(p:ℂ)), t≠0 ∧
      ∀ j, 0<j → j<(p-1)*2 → threeMovingDiagonal t j≠0 := by
  have ht := minimal_three_parameter_ne_zero p (by omega)
  have he : ∀ j : Fin ((p-1)*2), ∀ᶠ t in 𝓝 ((3:ℂ)/(p:ℂ)),
      0<j.val → threeMovingDiagonal t j≠0 := by
    intro j
    by_cases hj : 0<j.val
    · exact ((threeMovingDiagonal_differentiable _ ht j).continuousAt.eventually_ne
        (minimalThree_state_diagonal_ne_zero p hp hcop j hj j.isLt)).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hj h))
  filter_upwards [eventually_ne_nhds ht,Filter.eventually_all.mpr he] with t ht h
  exact ⟨ht,fun j hj hjR => h ⟨j,hjR⟩ hj⟩

/-- The moving diagonal has a simple zero at the minimal parameter. Its
velocity is R(2R+1)/2, a manifestly nonzero rational number for R>0. -/
theorem threeMovingDiagonal_minimal_hasDerivAt (p : ℕ) (hp : 2≤p) :
    HasDerivAt (fun t => threeMovingDiagonal t ((p-1)*2))
      ((((p-1)*2:ℕ):ℂ)*(2*(((p-1)*2:ℕ):ℂ)+1)/2) ((3:ℂ)/(p:ℂ)) := by
  let R := (p-1)*2
  let t0 : ℂ := 3/(p:ℂ)
  have ht := minimal_three_parameter_ne_zero p (by omega)
  have hs : (R:ℂ)=2*(p:ℂ)-2 := by
    dsimp [R]
    have hn : (p-1)*2+2=2*p := by omega
    have he : ((((p-1)*2:ℕ):ℂ)+2)=2*(p:ℂ) := by exact_mod_cast hn
    linear_combination he
  have hpoly := ((((hasDerivAt_id t0).const_mul ((R:ℂ)+1)).sub_const 2).const_mul ((R:ℂ)/4)).mul
    (((hasDerivAt_id t0).const_mul ((R:ℂ)+2)).sub_const 6)
  have hv : (R:ℂ)/4*((R:ℂ)+1)*(((R:ℂ)+2)*t0-6)+
      ((R:ℂ)/4*(((R:ℂ)+1)*t0-2))*((R:ℂ)+2)=
      (R:ℂ)*(2*(R:ℂ)+1)/2 := by
    rw [hs]
    dsimp [t0]
    have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
    field_simp
    ring
  simp only [mul_one,id_eq,Pi.mul_apply] at hpoly
  rw [hv] at hpoly
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ht] with t ht
  exact threeMovingDiagonal_polynomial t ht R

/-- The actual norm derivative cannot vanish: differentiating the proved
moving norm identity gives a nonzero diagonal velocity times the nonzero
actual Ward sum, while the radical chain rule gives charge velocity times
this fixed derivative. -/
theorem minimalThreeNormPolynomial_derivative_ne_zero (p : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3) :
    (minimalThreeNormPolynomial p hp hcop).derivative.eval (vermaBSACharge ((3:ℂ)/(p:ℂ)))≠0 := by
  let R := (p-1)*2
  let t0 : ℂ := 3/(p:ℂ)
  have ht := minimal_three_parameter_ne_zero p (by omega)
  have hq := threeMovingNormSum_differentiable t0 ht R
    (fun j hj hjR => minimalThree_state_diagonal_ne_zero p hp hcop j hj hjR)
  have hd := threeMovingDiagonal_minimal_hasDerivAt p hp
  have hprod := hd.neg.mul hq.hasDerivAt
  have hz := threeMovingDiagonal_minimal_terminal p hp
  simp only [Pi.neg_apply,Pi.mul_apply,hz,neg_zero,zero_mul,add_zero] at hprod
  have hnorm := hprod.congr_of_eventuallyEq (by
    filter_upwards [threeMoving_interior_eventually p hp hcop] with t ht
    exact threeMoving_source_norm t ht.1 R (by dsimp [R]; omega) ht.2)
  have hcharge := threeMovingCharge_differentiable t0 ht
  have hactual := threeMovingNorm_hasDerivAt p hp hcop vermaBSACharge
    (_root_.deriv vermaBSACharge t0) hcharge.hasDerivAt rfl
  have he := hactual.unique hnorm
  have hC : threeMovingNormSum t0 R≠0 := by
    rw [threeMovingNormSum_at_minimal p hp hcop]
    exact mul_ne_zero (div_ne_zero (pow_ne_zero _ ht) (by norm_num))
      (minimalThreeNormResidual_ne_zero p hp hcop)
  have hD : (R:ℂ)*(2*(R:ℂ)+1)/2≠0 := by
    apply div_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (show R≠0 by dsimp [R]; omega)
      · exact_mod_cast (show 2*R+1≠0 by omega)
    · norm_num
  intro hzero
  rw [hzero,mul_zero] at he
  exact (mul_ne_zero (neg_ne_zero.mpr hD) hC) he.symm

/-- Every coprime M(p,3) vacuum minimal model is graded first-order rigid.
All ordinary singular-state and norm-derivative inputs are discharged. -/
theorem minimal_three_graded_rigidity (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    Deform.IsRigidGraded (VirSimple.virasoroSimple (minimalCentralCharge p 3)) := by
  rw [← fusionThree_minimal_charge p hp]
  apply minimalThree_graded_rigidity_of_response p hp hcop
  rw [← minimalThreeNormPolynomial_derivative p hp hcop]
  exact minimalThreeNormPolynomial_derivative_ne_zero p hp hcop

/-- Exchanging minimal-model labels gives the full coprime M(3,q) family
with no remaining rigidity assumptions. -/
theorem minimal_left_three_graded_rigidity (q : ℕ) (hq : 2≤q) (hcop : Nat.Coprime 3 q) :
    Deform.IsRigidGraded (VirSimple.virasoroSimple (minimalCentralCharge 3 q)) := by
  rw [minimalCharge_swap]
  exact minimal_three_graded_rigidity q hq hcop.symm

end VOA.InverseDS.VirasoroVerma
