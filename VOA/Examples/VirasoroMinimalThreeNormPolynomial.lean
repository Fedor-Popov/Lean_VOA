/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import VOA.Examples.VirasoroVermaChargeTransport
import VOA.Examples.VirasoroBSAWordPolynomial

/-!
# A fixed word expression and actual norm polynomial for M(p,3)

Charge transport removes the choices in the source construction. One finite
word expression, obtained at charge zero, evaluates to the actual vacuum
source at every charge. Its canonical norm is therefore a polynomial.
Its root is proved; the derivative's nonvanishing remains a scalar problem.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirDeformModes VirDeformModes.NormalOrdering

/-- Interpret an arbitrary negative Verma word after vacuum projection.
Letters i encode L_(-i-1), so L_(-1) is retained until the actual quotient. -/
theorem vacuumProjection_negWord (c : ℂ) (w : List ℕ) :
    vacuumProjection c (negWord c 0 w) =
      virWord (Lop c) (w.map (fun (i : ℕ) => -(i:ℤ)-1)) (vacVec c) := by
  induction w with
  | nil => simp [virWord]
  | cons i w ih => simp only [negWord_cons,vacuumProjection_mode,List.map_cons,virWord,
      Module.End.mul_apply,ih]

/-- Expand a charge-zero Verma state into its finite sorted-word coordinates
and store the literal mode words. The expression has no variable charge. -/
noncomputable def chargeWordExpression : Verma 0 0 →ₗ[ℂ] VirWordExpression :=
  (Finsupp.linearCombination ℂ (fun w : {w : List ℕ // SortedWord w} =>
    Finsupp.single (w.val.map (fun (i : ℕ) => -(i:ℤ)-1)) (1:ℂ))).comp
      (vermaSortedBasis 0 0).repr.toLinearMap

/-- A PBW basis state becomes exactly its literal finite word expression. -/
theorem chargeWordExpression_basis (w : {w : List ℕ // SortedWord w}) :
    chargeWordExpression (vermaSortedBasis 0 0 w) =
      Finsupp.single (w.val.map (fun (i : ℕ) => -(i:ℤ)-1)) (1:ℂ) := by
  change (Finsupp.linearCombination ℂ (fun u : {w : List ℕ // SortedWord w} =>
    Finsupp.single (u.val.map (fun (i : ℕ) => -(i:ℤ)-1)) (1:ℂ)))
      ((vermaSortedBasis 0 0).repr (vermaSortedBasis 0 0 w)) = _
  rw [Module.Basis.repr_self,Finsupp.linearCombination_single,one_smul]

/-- The stored expression evaluates to the actual transported state after
vacuum projection, at every charge. This proves regularity without making
a continuity assumption about the earlier chosen family. -/
theorem chargeWordExpression_eval (c : ℂ) (v : Verma 0 0) :
    wordExpressionEval c (chargeWordExpression v) =
      vacuumProjection c (chargeTransport 0 c 0 v) := by
  have he : (wordExpressionEval c).comp chargeWordExpression =
      (vacuumProjection c).comp (chargeTransport 0 c 0).toLinearMap := by
    apply (vermaSortedBasis 0 0).ext
    intro w
    change wordExpressionEval c (chargeWordExpression (vermaSortedBasis 0 0 w)) = _
    rw [chargeWordExpression_basis,wordExpressionEval_single,one_smul]
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,vermaSortedBasis_apply,
      chargeTransport_word,vacuumProjection_negWord]
  exact LinearMap.congr_fun he v

/-- A single fixed finite expression for the entire actual q=3 vacuum
source family, defined using its charge-zero PBW coordinates. -/
noncomputable def minimalThreeExpression (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    VirWordExpression := chargeWordExpression (minimalThreeChargeSource p hp hcop 0)

/-- The fixed expression agrees with the actual
vacuum source constructed earlier at every charge, not merely at the minimal-model charge. -/
theorem minimalThreeExpression_eval (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    wordExpressionEval c (minimalThreeExpression p hp hcop) =
      minimalThreeChargeVacuum p hp hcop c := by
  rw [minimalThreeExpression,chargeWordExpression_eval,chargeTransport_minimalThree_source]
  rfl

/-- The universal canonical norm polynomial of the actual q=3 source. -/
noncomputable def minimalThreeNormPolynomial (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    Polynomial ℂ := wordExpressionPair (minimalThreeExpression p hp hcop)
      (minimalThreeExpression p hp hcop)

/-- Evaluation of this polynomial is exactly the canonical norm of the
actual source at any charge, so its formal derivative is the relevant
ordinary charge derivative. No norm-product formula is assumed. -/
theorem minimalThreeNormPolynomial_eval (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    (minimalThreeNormPolynomial p hp hcop).eval c =
      (VirGram4.canB c).form (minimalThreeChargeVacuum p hp hcop c)
        (minimalThreeChargeVacuum p hp hcop c) := by
  rw [minimalThreeNormPolynomial,wordExpressionPair_eval,minimalThreeExpression_eval]

/-- At the minimal-model charge the actual source is a positive-weight
singular state, hence its canonical norm polynomial vanishes there. This
root statement makes no assertion about its multiplicity. -/
theorem minimalThreeNormPolynomial_root (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    (minimalThreeNormPolynomial p hp hcop).eval (vermaBSACharge ((3:ℂ)/(p:ℂ)))=0 := by
  rw [minimalThreeNormPolynomial_eval]
  exact canB_singular_right_zero _ (n:=(p-1)*2) (by omega) _
    (minimalThreeChargeVacuum_level p hp hcop _)
    (minimalThreeChargeVacuum_L1 p hp hcop _)
    (minimalThreeChargeVacuum_L2_at_root p hp hcop) _

/-- Divide the actual norm polynomial by its known minimal-charge factor.
Polynomial division is regular at the root; no scalar division by c-c0
is used in this definition. Nonvanishing of this quotient at c0 is open. -/
noncomputable def minimalThreeNormResponse (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    Polynomial ℂ := minimalThreeNormPolynomial p hp hcop /ₘ
      (Polynomial.X-Polynomial.C (vermaBSACharge ((3:ℂ)/(p:ℂ))))

/-- The known singular root gives an exact polynomial factorization of
the actual norm. The quotient need not be nonzero at that root. -/
theorem minimalThreeNormPolynomial_factor (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    minimalThreeNormPolynomial p hp hcop =
      (Polynomial.X-Polynomial.C (vermaBSACharge ((3:ℂ)/(p:ℂ))))*
        minimalThreeNormResponse p hp hcop := by
  exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
    (minimalThreeNormPolynomial_root p hp hcop)).symm

/-- The charge derivative of the actual norm equals the quotient's value
at the minimal charge. This identifies the precise remaining scalar. -/
theorem minimalThreeNormPolynomial_derivative (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    (minimalThreeNormPolynomial p hp hcop).derivative.eval (vermaBSACharge ((3:ℂ)/(p:ℂ))) =
      (minimalThreeNormResponse p hp hcop).eval (vermaBSACharge ((3:ℂ)/(p:ℂ))) := by
  conv_lhs => rw [minimalThreeNormPolynomial_factor p hp hcop]
  simp

/-- The actual canonical norm, viewed as a complex-valued function of
charge, has the indicated derivative. The finite-word identification
supplies all analytic regularity required by this statement. -/
theorem minimalThree_actual_norm_hasDerivAt (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) :
    HasDerivAt (fun d : ℂ => (VirGram4.canB d).form
      (minimalThreeChargeVacuum p hp hcop d) (minimalThreeChargeVacuum p hp hcop d))
      ((minimalThreeNormPolynomial p hp hcop).derivative.eval c) c := by
  simpa only [minimalThreeNormPolynomial_eval] using
    (minimalThreeNormPolynomial p hp hcop).hasDerivAt c

/-- The actual source supplies the radical relation internally. A nonzero
value of its ordinary scalar response would therefore imply M(p,3)
rigidity. That remaining nonvanishing is explicitly a hypothesis here. -/
theorem minimalThree_graded_rigidity_of_response (p : ℕ) (hp : 2≤p)
    (hcop : Nat.Coprime p 3)
    (hq : (minimalThreeNormResponse p hp hcop).eval (vermaBSACharge ((3:ℂ)/(p:ℂ)))≠0) :
    Deform.IsRigidGraded (VirSimple.virasoroSimple (vermaBSACharge ((3:ℂ)/(p:ℂ)))) := by
  apply graded_rigidity_of_wordExpression _ (minimalThreeExpression p hp hcop)
  · rw [minimalThreeExpression_eval]
    exact singular_mem_maxIdeal _ (n:=(p-1)*2) (by omega) _
      (minimalThreeChargeVacuum_level p hp hcop _)
      (minimalThreeChargeVacuum_L1 p hp hcop _)
      (minimalThreeChargeVacuum_L2_at_root p hp hcop)
  · change (minimalThreeNormPolynomial p hp hcop).derivative.eval _≠0
    rw [minimalThreeNormPolynomial_derivative]
    exact hq

end VOA.InverseDS.VirasoroVerma
