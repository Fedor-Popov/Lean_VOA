/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaChargeResponse
import VOA.Examples.VirasoroBSADiagonalResponse

/-!
# The q=3 scalar response as an actual canonical pairing

Move the first creation mode in each PBW word across the invariant form.
Quasiprimary covariance expresses every positive mode using the second-mode
response. Moving the remaining L1 powers back produces a fixed finite row
expression. Its actual pairing with the fixed response equals the norm
quotient, including at the singular charge. Nonvanishing is not assumed
or proved by this identification.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirDeformModes.NormalOrdering

/-- The row contributed by one creation word. Vacuum and initial L_-1
terms pair to zero against the positive-weight quasiprimary source.
An initial L_(-m-2) contributes the signed inverse-factorial translate. -/
noncomputable def normResponseRowWord : List ℕ → VirWordExpression
  | [] => 0
  | 0 :: _ => 0
  | (m+1) :: w => positiveLadderCoefficient m •
      ((wordExpressionMode (-1))^m)
        (Finsupp.single (w.map (fun (i : ℕ) => -(i:ℤ)-1)) (1:ℂ))

/-- Store the adjoint response row of any charge-zero state using its
finite PBW expansion. This is a linear, charge-independent construction. -/
noncomputable def normResponseRowExpression : Verma 0 0 →ₗ[ℂ] VirWordExpression :=
  (Finsupp.linearCombination ℂ (fun w : {w : List ℕ // SortedWord w} =>
    normResponseRowWord w.val)).comp (vermaSortedBasis 0 0).repr.toLinearMap

/-- A PBW basis state contributes exactly the row of its creation word. -/
theorem normResponseRowExpression_basis (w : {w : List ℕ // SortedWord w}) :
    normResponseRowExpression (vermaSortedBasis 0 0 w)=normResponseRowWord w.val := by
  change (Finsupp.linearCombination ℂ (fun u : {w : List ℕ // SortedWord w} =>
    normResponseRowWord u.val)) ((vermaSortedBasis 0 0).repr (vermaSortedBasis 0 0 w)) = _
  rw [Module.Basis.repr_self,Finsupp.linearCombination_single,one_smul]

/-- For each literal creation word, actual adjointness and the proved
positive-mode response give the charge factor and its canonical row pairing. -/
theorem minimalThree_word_pair_factor (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) (w : List ℕ) :
    (VirGram4.canB c).form (vacuumProjection c (negWord c 0 w))
      (minimalThreeChargeVacuum p hp hcop c) =
    (c-vermaBSACharge ((3:ℂ)/(p:ℂ))) *
      (VirGram4.canB c).form (wordExpressionEval c (normResponseRowWord w))
        (wordExpressionEval c (minimalThreeSecondResponseExpression p hp hcop)) := by
  cases w with
  | nil =>
    simp only [negWord_nil,vacuumProjection_highest,normResponseRowWord,map_zero,
      LinearMap.zero_apply,mul_zero]
    exact (VirGram4.canB c).orthogonal_of_ne
      (show (0:ℤ)≠(((p-1)*2:ℕ):ℤ) by omega)
      (virasoroVOA c).vacuum_mem (minimalThreeChargeVacuum_level p hp hcop c)
  | cons i w =>
    rw [negWord_cons,vacuumProjection_mode,VirGram4.canB_adj]
    cases i with
    | zero =>
      norm_num only [Nat.cast_zero,neg_zero,zero_sub,neg_neg]
      rw [minimalThreeChargeVacuum_L1]
      simp [normResponseRowWord]
    | succ m =>
      have he : -(-(((m+1:ℕ):ℤ))-1)=(m:ℤ)+2 := by push_cast; ring
      rw [he,minimalThreeChargeVacuum_positive_factor]
      simp only [normResponseRowWord,map_smul,LinearMap.smul_apply,smul_eq_mul,
        wordExpressionEval_mode_pow,wordExpressionEval_single,one_smul,
        bsaTranslation_power_adj,vacuumProjection_negWord]

/-- Extend the word identity to every actual PBW state. Both rows are
linear in that state, so no coordinate-dependent assumption remains. -/
theorem minimalThree_state_pair_factor (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) (v : Verma 0 0) :
    (VirGram4.canB c).form (vacuumProjection c (chargeTransport 0 c 0 v))
      (minimalThreeChargeVacuum p hp hcop c) =
    (c-vermaBSACharge ((3:ℂ)/(p:ℂ))) *
      (VirGram4.canB c).form (wordExpressionEval c (normResponseRowExpression v))
        (wordExpressionEval c (minimalThreeSecondResponseExpression p hp hcop)) := by
  have hv : v∈Submodule.span ℂ (Set.range (vermaSortedBasis 0 0)) := by
    rw [Module.Basis.span_eq]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w,rfl⟩ := hv
    rw [normResponseRowExpression_basis,vermaSortedBasis_apply,chargeTransport_word]
    exact minimalThree_word_pair_factor p hp hcop c w.val
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add,LinearMap.add_apply,hx,hy]
    ring
  | smul a x _ hx =>
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,hx]
    ring

/-- The fixed row whose pairing with the actual second response is the
scalar obstruction for the q=3 family. -/
noncomputable def minimalThreeNormRow (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    VirWordExpression := normResponseRowExpression (minimalThreeChargeSource p hp hcop 0)

/-- The actual norm factors by charge difference with an explicit actual
canonical pairing as quotient, at every charge. -/
theorem minimalThree_actual_norm_pair_factor (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) :
    (VirGram4.canB c).form (minimalThreeChargeVacuum p hp hcop c)
      (minimalThreeChargeVacuum p hp hcop c) =
    (c-vermaBSACharge ((3:ℂ)/(p:ℂ))) *
      (VirGram4.canB c).form (wordExpressionEval c (minimalThreeNormRow p hp hcop))
        (wordExpressionEval c (minimalThreeSecondResponseExpression p hp hcop)) := by
  have hh := minimalThree_state_pair_factor p hp hcop c (minimalThreeChargeSource p hp hcop 0)
  rw [chargeTransport_minimalThree_source] at hh
  exact hh

/-- The polynomial quotient is exactly the universal pairing of the two
fixed response expressions. Polynomial cancellation makes this identification
valid at the root too, where numerical division would not be legitimate. -/
theorem minimalThreeNormResponse_eq_pair (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    minimalThreeNormResponse p hp hcop =
      wordExpressionPair (minimalThreeNormRow p hp hcop)
        (minimalThreeSecondResponseExpression p hp hcop) := by
  have he : minimalThreeNormPolynomial p hp hcop =
      (Polynomial.X-Polynomial.C (vermaBSACharge ((3:ℂ)/(p:ℂ)))) *
      wordExpressionPair (minimalThreeNormRow p hp hcop)
        (minimalThreeSecondResponseExpression p hp hcop) := by
    apply Polynomial.funext
    intro c
    simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
      minimalThreeNormPolynomial_eval,wordExpressionPair_eval]
    exact minimalThree_actual_norm_pair_factor p hp hcop c
  rw [minimalThreeNormPolynomial_factor] at he
  exact mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero _) he

/-- The remaining norm derivative is an ACTUAL canonical scalar pairing
of the fixed row and fixed second response at the singular charge. This
theorem identifies it but does not claim that the scalar is nonzero. -/
theorem minimalThreeNorm_derivative_eq_pair (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    (minimalThreeNormPolynomial p hp hcop).derivative.eval (vermaBSACharge ((3:ℂ)/(p:ℂ))) =
      (VirGram4.canB (vermaBSACharge ((3:ℂ)/(p:ℂ)))).form
        (wordExpressionEval (vermaBSACharge ((3:ℂ)/(p:ℂ))) (minimalThreeNormRow p hp hcop))
        (wordExpressionEval (vermaBSACharge ((3:ℂ)/(p:ℂ)))
          (minimalThreeSecondResponseExpression p hp hcop)) := by
  rw [minimalThreeNormPolynomial_derivative,minimalThreeNormResponse_eq_pair,wordExpressionPair_eval]

end VOA.InverseDS.VirasoroVerma
