/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSAIntermediateNorm

/-!
# The actual BSA scalar response is a polynomial norm derivative

Finite sums of unreduced mode words retain coefficients independent of the
central charge. We construct such expressions for the BSA states and their
responses, and evaluate their canonical pairings with the existing universal
word polynomials. The actual scalar factor Q_N is thereby a polynomial.
Its value at c_N is exactly the terminal norm derivative. Its nonvanishing
remains an ordinary scalar problem; no norm-product formula is assumed.
-/
namespace VOA.VirModule
open VirDeformModes VirDeformModes.NormalOrdering Module

/-- A finite linear combination of mode words. Unlike a normal form, this
stores words before commuting them, so its coefficients never involve the
central charge. -/
abbrev VirWordExpression := List ℤ →₀ ℂ

/-- Interpret a finite word expression in the actual universal vacuum module
at the supplied charge. -/
noncomputable def wordExpressionEval (c : ℂ) : VirWordExpression →ₗ[ℂ] VirUniv c :=
  Finsupp.linearCombination ℂ (fun w => virWord (Lop c) w (vacVec c))

/-- Prefix every word with one mode, retaining its scalar coefficient. -/
noncomputable def wordExpressionMode (m : ℤ) : VirWordExpression →ₗ[ℂ] VirWordExpression :=
  Finsupp.lmapDomain ℂ ℂ (List.cons m)

/-- A single expression term evaluates to its coefficient times the literal
mode word applied to the vacuum. -/
theorem wordExpressionEval_single (c : ℂ) (w : List ℤ) (a : ℂ) :
    wordExpressionEval c (Finsupp.single w a) = a • virWord (Lop c) w (vacVec c) :=
  Finsupp.linearCombination_single ℂ a w

/-- Prefixing a word expression agrees with applying that mode after
interpretation in the vacuum module. -/
theorem wordExpressionEval_mode (c : ℂ) (m : ℤ) (f : VirWordExpression) :
    wordExpressionEval c (wordExpressionMode m f) = Lop c m (wordExpressionEval c f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single w a =>
    simp only [wordExpressionMode, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      wordExpressionEval_single, virWord, Module.End.mul_apply, map_smul]

/-- Repeated prefixing likewise evaluates to a power of the actual mode.
This handles the L₁ iterates appearing in the scalar norm response. -/
theorem wordExpressionEval_mode_pow (c : ℂ) (m : ℤ) (k : ℕ) (f : VirWordExpression) :
    wordExpressionEval c (((wordExpressionMode m)^k) f) =
      ((Lop c m)^k) (wordExpressionEval c f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ', Module.End.mul_apply, wordExpressionEval_mode, ih]

/-- The universal polynomial pairing of two finite word expressions. Both
slots are linear, matching the canonical bilinear form without conjugation. -/
noncomputable def wordExpressionPair :
    VirWordExpression →ₗ[ℂ] VirWordExpression →ₗ[ℂ] Polynomial ℂ :=
  Finsupp.linearCombination ℂ (fun u =>
    Finsupp.linearCombination ℂ (fun v => wordPolynomial (u.reverse.map Neg.neg ++ v)))

/-- Specializing the polynomial pairing at any charge gives precisely the
actual canonical invariant-form pairing of the evaluated expressions. -/
theorem wordExpressionPair_eval (c : ℂ) (f g : VirWordExpression) :
    (wordExpressionPair f g).eval c =
      (VirGram4.canB c).form (wordExpressionEval c f) (wordExpressionEval c g) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f h hf hh => simp only [map_add, LinearMap.add_apply, Polynomial.eval_add, hf, hh]
  | single u a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g h hg hh => simp only [map_add, Polynomial.eval_add, hg, hh]
    | single v b =>
      simp only [wordExpressionPair, Finsupp.linearCombination_single, LinearMap.smul_apply,
        Polynomial.eval_smul, wordExpressionEval_single, map_smul, smul_eq_mul]
      rw [show (wordPolynomial (u.reverse.map Neg.neg ++ v)).eval c =
        (VirGram4.canB c).form (virWord (Lop c) u (vacVec c))
          (virWord (Lop c) v (vacVec c)) by
            simpa only [show (virasoroVOA c).L = Lop c from
              funext (virasoroVOA_L_eq_Lop c)] using universal_gram_entry c u v]
      ring

/-- A charge-independent word expression for every intermediate BSA state.
The coefficients are exactly those of the already constructed state recursion. -/
noncomputable def bsaStateExpression (N : ℕ) : ℕ → VirWordExpression
  | 0 => Finsupp.single [] 1
  | r+1 => (-bsaParameter N / (((r:ℂ)+1)*((N:ℂ)-((r:ℂ)+1)))) •
      ∑ j : Fin (r+1), wordExpressionMode ((j:ℤ)-((r:ℤ)+1)) (bsaStateExpression N j)
termination_by r => r

/-- The undivided source expression, including the terminal source. -/
noncomputable def bsaSourceExpression (N r : ℕ) : VirWordExpression :=
  ∑ j : Fin r, wordExpressionMode ((j:ℤ)-(r:ℤ)) (bsaStateExpression N j)

/-- The formal state expression evaluates to the
actual BSA state constructed above, simultaneously at every charge and every level. -/
theorem bsaStateExpression_eval (c : ℂ) (N r : ℕ) :
    wordExpressionEval c (bsaStateExpression N r) = bsaState c N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [bsaStateExpression, wordExpressionEval_single, virWord, bsaState_zero]
    | succ r =>
      rw [bsaStateExpression, bsaState]
      simp only [map_smul, map_sum, wordExpressionEval_mode]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j j.isLt]

/-- The source expression evaluates to the actual source, so there is no
change of vector when passing from module calculations to word polynomials. -/
theorem bsaSourceExpression_eval (c : ℂ) (N r : ℕ) :
    wordExpressionEval c (bsaSourceExpression N r) = bsaSource c N r := by
  simp only [bsaSourceExpression, bsaSource, map_sum, wordExpressionEval_mode,
    bsaStateExpression_eval]

/-- The intermediate charge response as a finite, unreduced word expression.
Its coefficients are independent of the charge, including the forcing term. -/
noncomputable def bsaResponseExpression (N : ℕ) : ℕ → VirWordExpression
  | r => (-bsaParameter N / (((r:ℂ)+2)*((N:ℂ)-((r:ℂ)+2)))) •
      ((1/2:ℂ) • bsaStateExpression N r +
        ∑ j : Fin r, wordExpressionMode ((j:ℤ)-(r:ℤ)) (bsaResponseExpression N j))
termination_by r => r

/-- The undivided response expression used at the terminal index. -/
noncomputable def bsaSourceResponseExpression (N r : ℕ) : VirWordExpression :=
  (1/2:ℂ) • bsaStateExpression N r +
    ∑ j : Fin r, wordExpressionMode ((j:ℤ)-(r:ℤ)) (bsaResponseExpression N j)

/-- The recursive response expression evaluates to the actual L₂ response,
not an independently postulated response vector. -/
theorem bsaResponseExpression_eval (c : ℂ) (N r : ℕ) :
    wordExpressionEval c (bsaResponseExpression N r) = bsaL2Response c N r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [bsaResponseExpression, bsaL2Response]
    simp only [map_smul, map_add, map_sum, wordExpressionEval_mode, bsaStateExpression_eval]
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j j.isLt]

/-- The undivided word response equals the actual terminal response upon
evaluation at every charge. -/
theorem bsaSourceResponseExpression_eval (c : ℂ) (N r : ℕ) :
    wordExpressionEval c (bsaSourceResponseExpression N r) = bsaL2SourceResponse c N r := by
  simp only [bsaSourceResponseExpression, bsaL2SourceResponse, map_add, map_smul,
    map_sum, wordExpressionEval_mode, bsaStateExpression_eval, bsaResponseExpression_eval]

/-- The universal norm polynomial of the fixed terminal BSA expression. -/
noncomputable def bsaNormPolynomial (N : ℕ) : Polynomial ℂ :=
  wordExpressionPair (bsaSourceExpression N N) (bsaSourceExpression N N)

/-- The polynomial whose evaluations are the scalar terminal norm responses. -/
noncomputable def bsaNormResponsePolynomial (N r : ℕ) : Polynomial ℂ :=
  ∑ j : Fin (r+1), positiveLadderCoefficient (r-j.val) •
    wordExpressionPair (bsaStateExpression N j)
      (((wordExpressionMode 1)^(r-j.val)) (bsaSourceResponseExpression N r))

/-- At every charge the norm polynomial computes the actual terminal norm. -/
theorem bsaNormPolynomial_eval (c : ℂ) (N : ℕ) :
    (bsaNormPolynomial N).eval c =
      (VirGram4.canB c).form (bsaSource c N N) (bsaSource c N N) := by
  simp only [bsaNormPolynomial, wordExpressionPair_eval, bsaSourceExpression_eval]

/-- The scalar pairing constructed above is a polynomial in the charge.
This supplies the missing regularity at the singular charge without limits
or an assumption that the norm quotient is differentiable. -/
theorem bsaNormResponsePolynomial_eval (c : ℂ) (N r : ℕ) :
    (bsaNormResponsePolynomial N r).eval c = bsaScalarNormResponse c N r := by
  simp only [bsaNormResponsePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    wordExpressionPair_eval, wordExpressionEval_mode_pow, bsaStateExpression_eval,
    bsaSourceResponseExpression_eval, smul_eq_mul, bsaScalarNormResponse]

/-- The actual module norm factorization is an identity of universal
polynomials, since it holds after specialization at every complex charge. -/
theorem bsaNormPolynomial_factor (N r : ℕ) (hN : N=r+2) (hr : 0<r) :
    bsaNormPolynomial N =
      (Polynomial.X-Polynomial.C (bsaCharge N))*bsaNormResponsePolynomial N r := by
  apply Polynomial.funext
  intro c
  rw [bsaNormPolynomial_eval, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, bsaNormResponsePolynomial_eval]
  exact bsaSource_norm_factor c N r hN hr

/-- The derivative of the genuine universal BSA norm at its singular charge
is exactly the actual scalar response computed earlier. Only its nonvanishing
remains to be proved; no representation-theoretic norm formula is used here. -/
theorem bsaNormPolynomial_derivative (N r : ℕ) (hN : N=r+2) (hr : 0<r) :
    (bsaNormPolynomial N).derivative.eval (bsaCharge N) =
      bsaScalarNormResponse (bsaCharge N) N r := by
  rw [bsaNormPolynomial_factor N r hN hr, Polynomial.derivative_mul]
  simp [bsaNormResponsePolynomial_eval]


/-- A finite-support expression can be read as the finite family of its
nonzero coefficients. This is the indexing required by the existing
word-relation rigidity criterion. -/
theorem wordExpressionEval_support (c : ℂ) (f : VirWordExpression) :
    wordExpressionEval c f =
      ∑ w : f.support, f w • virWord (Lop c) w (vacVec c) := by
  classical
  simp only [wordExpressionEval, Finsupp.linearCombination_apply, Finsupp.sum]
  exact (Finset.sum_attach f.support (fun w => f w • virWord (Lop c) w (vacVec c))).symm

/-- The expression norm polynomial is exactly the relation polynomial of
its finite support. Thus passing to word expressions changes no derivative
in the already established rigidity criterion. -/
theorem wordExpressionPair_eq_relation (f : VirWordExpression) :
    wordExpressionPair f f = relationPolynomial (fun w : f.support => w.val)
      (fun w : f.support => f w) := by
  classical
  apply Polynomial.funext
  intro c
  rw [wordExpressionPair_eval, relationPolynomial_eval, wordExpressionEval_support]
  rw [show (virasoroVOA c).L = Lop c from funext (virasoroVOA_L_eq_Lop c)]

/-- A genuine radical word expression with nonzero universal norm derivative
satisfies the existing graded-rigidity theorem. The radical and derivative
are ordinary module and polynomial conditions, not deformation assumptions. -/
theorem graded_rigidity_of_wordExpression (c : ℂ) (f : VirWordExpression)
    (hf : wordExpressionEval c f ∈ VirSimple.maxIdealVir c)
    (hd : (wordExpressionPair f f).derivative.eval c ≠ 0) :
    Deform.IsRigidGraded (VirSimple.virasoroSimple c) := by
  classical
  have hq : (VirSimple.maxIdealVir c).mkQ (wordExpressionEval c f) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hf
  rw [wordExpressionEval_support] at hq
  simp only [map_sum, map_smul] at hq
  have hL : Lop c = (virasoroVOA c).L := (funext (virasoroVOA_L_eq_Lop c)).symm
  rw [hL] at hq
  simp only [virWord_mkQ] at hq
  apply graded_rigidity_of_relation c (fun w : f.support => w.val)
    (fun w : f.support => f w) hq
  simpa only [wordExpressionPair_eq_relation] using hd

/-- For the explicit BSA family, the ONE remaining scalar input is the
nonvanishing of the actual norm response at c_N. Its identification with
the derivative and its genuine quotient relation are proved internally.
This conditional theorem does not assert that the scalar input holds. -/
theorem graded_rigidity_of_bsa_scalar (N r : ℕ) (hN : N=r+2) (hr : 0<r)
    (hq : bsaScalarNormResponse (bsaCharge N) N r ≠ 0) :
    Deform.IsRigidGraded
      (VirSimple.virasoroSimple (bsaCharge N)) := by
  apply graded_rigidity_of_wordExpression (bsaCharge N) (bsaSourceExpression N N)
  · rw [bsaSourceExpression_eval]
    exact bsaSource_mem_maxIdeal N (by omega)
  · change (bsaNormPolynomial N).derivative.eval (bsaCharge N) ≠ 0
    rw [bsaNormPolynomial_derivative N r hN hr]
    exact hq

end VOA.VirModule
