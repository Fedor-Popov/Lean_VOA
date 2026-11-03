import VOA.DeligneAudit.DeligneFusionCVRectPolynomialCurrent
import VOA.DeligneAudit.DeligneFusionCVRectCutoff
import VOA.DeligneAudit.DeligneFusionCVRectIntegrationIdeal

/-!
# Actual CV relations imply the reversed coefficient ideal

The proof evaluates the canonical two-color variables in the actual cyclic
representation. Its high modes vanish as operators, so fixed-degree reflection
converts each reversed coefficient to a full CV coefficient. Ideal closure then
uses the genuine polynomial annihilator ideal.
-/

namespace VOA.DeligneAudit.A2.CVRectPolynomial

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVPolarization
open VOA.DeligneAudit.A2.CVRectIntegrationIdeal
open VOA.DeligneAudit.A2.CVRectIntegrationOrder

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Evaluation of the canonical sum-indexed current coordinates. -/
def canonicalOperatorEval (R : CurrentModule bracketTable V) (N : ℕ) :
    MvPolynomial (Fin N ⊕ Fin N) ℂ →ₐ[ℂ] Module.End ℂ V :=
  (operatorEval R N).comp (colorCoordinates N).toAlgHom

@[simp] theorem canonicalOperatorEval_X_left (R : CurrentModule bracketTable V)
    (N : ℕ) (i : Fin N) :
    canonicalOperatorEval R N (MvPolynomial.X (Sum.inl i)) = R.op 3 i.val := by
  simp [canonicalOperatorEval, colorOp]

@[simp] theorem canonicalOperatorEval_X_right (R : CurrentModule bracketTable V)
    (N : ℕ) (i : Fin N) :
    canonicalOperatorEval R N (MvPolynomial.X (Sum.inr i)) = R.op 5 i.val := by
  simp [canonicalOperatorEval, colorOp]

/-- A reversed coefficient evaluates to the corresponding coefficient of
the reflected operator polynomials. -/
theorem canonical_reverse_coefficient (R : CurrentModule bracketTable V)
    (N p q j : ℕ) :
    canonicalOperatorEval R N
      (PowerSeries.coeff j (CVRectSplit.reverseLeft N N ^ p * CVRectSplit.reverseRight N N ^ q)) =
      ((Polynomial.reflect (N - 1) (finiteCurrent N (R.op 3))) ^ p *
        (Polynomial.reflect (N - 1) (finiteCurrent N (R.op 5))) ^ q).coeff j := by
  let φ := (canonicalOperatorEval R N).toRingHom
  change φ (PowerSeries.coeff j _) = _
  rw [← PowerSeries.coeff_map, map_mul, map_pow, map_pow,
    map_reverseLeft N φ (R.op 3) (by intro i; exact canonicalOperatorEval_X_left R N i),
    map_reverseRight N φ (R.op 5) (by intro i; exact canonicalOperatorEval_X_right R N i),
    ← Polynomial.coe_pow, ← Polynomial.coe_pow, ← Polynomial.coe_mul, Polynomial.coeff_coe]

/-- Exact high-mode cutoffs identify forward polynomial coefficients with
the full mixed current coefficients. -/
theorem finite_coefficient_eq_mixed (R : CurrentModule bracketTable V) (N p q s : ℕ)
    (hF : ∀ j, N ≤ j → R.op 3 j = 0) (hG : ∀ j, N ≤ j → R.op 5 j = 0) :
    ((finiteCurrent N (R.op 3)) ^ p * (finiteCurrent N (R.op 5)) ^ q).coeff s =
      mixedCoeff (R.op 3) (R.op 5) p q s := by
  rw [← Polynomial.coeff_coe, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_pow,
    finiteCurrent_series N (R.op 3) hF, finiteCurrent_series N (R.op 5) hG]
  rfl

/-- The concrete excess order attached to capacities one, two and three. -/
def canonicalOrder (r n e : ℕ) (p q : ℕ) : ℕ := excess (parts r n e) (p + q)

def canonicalCoefficientIdeal (r n e : ℕ) :
    Ideal (MvPolynomial (Fin (r + n + e) ⊕ Fin (r + n + e)) ℂ) :=
  coefficientIdeal (CVRectSplit.reverseLeft (r + n + e) (r + n + e))
    (CVRectSplit.reverseRight (r + n + e) (r + n + e)) (canonicalOrder r n e)

/-- Every actual reversed coefficient generator annihilates the source cyclic vector. -/
theorem canonical_coefficient_zero (R : CurrentModule bracketTable V) (w : V)
    {e n r : ℕ} (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0)
    (p q j : ℕ) (hj : j < canonicalOrder r n e p q) :
    vectorEval R w (r + n + e) (colorCoordinates (r + n + e)
      (PowerSeries.coeff j (CVRectSplit.reverseLeft (r + n + e) (r + n + e) ^ p *
        CVRectSplit.reverseRight (r + n + e) (r + n + e) ^ q))) = 0 := by
  let R' := cyclicRep R w
  let w' := cyclicVector R w
  let N := r + n + e
  have hh := cyclic_rel R w h
  have hF : ∀ s, N ≤ s → R'.op 3 s = 0 := by
    intro s hs
    simpa only [currentMode, Bool.false_eq_true, ↓reduceIte] using
      high_currentMode_zero R w h false s hs
  have hG : ∀ s, N ≤ s → R'.op 5 s = 0 := by
    intro s hs
    simpa only [currentMode, ↓reduceIte] using high_currentMode_zero R w h true s hs
  have hz : canonicalOperatorEval R' N
      (PowerSeries.coeff j (CVRectSplit.reverseLeft N N ^ p * CVRectSplit.reverseRight N N ^ q))
        w' = 0 := by
    rw [canonical_reverse_coefficient]
    by_cases hdegree : j ≤ (N - 1) * (p + q)
    · rw [CVRectReflection.coeff_two_color _ _ (N - 1) p q j
        (finiteCurrent_natDegree_le N _) (finiteCurrent_natDegree_le N _) hdegree,
        finite_coefficient_eq_mixed R' N p q _ hF hG]
      obtain ⟨k, hk⟩ := CVRectCutoff.excess_cv_region r n e (p + q) j hj hdegree
      apply theta_cvrel_mixed R' (hh.raising 1 (by decide) 0) ?_ p q _ k
        (CVRectCutoff.multiplicity_pos hj) hk
      simpa only [Nat.add_zero] using hh.highest
    · rw [CVRectReflection.coeff_two_color_high _ _ (N - 1) p q j
        (finiteCurrent_natDegree_le N _) (finiteCurrent_natDegree_le N _) (by omega),
        LinearMap.zero_apply]
  rw [← vectorEval_cyclic_coe]
  simpa only [canonicalOperatorEval, AlgHom.comp_apply,
    vectorEval] using congrArg (fun v : CVRectSingle.cyclicSpan R w => (v : V)) hz

/-- The canonical coefficient ideal maps into the genuine polynomial annihilator ideal. -/
theorem canonicalCoefficientIdeal_le (R : CurrentModule bracketTable V) (w : V)
    {e n r : ℕ} (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0) :
    Ideal.map (colorCoordinates (r + n + e)).toRingHom (canonicalCoefficientIdeal r n e) ≤
      annihilatorIdeal R w (r + n + e) := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨p, q, j, hj, rfl⟩
  exact canonical_coefficient_zero R w h p q j hj

/-- Coordinate renaming identifies the actual scalar-restricted coefficient quotients. -/
def canonicalQuotientLinearEquiv (r n e : ℕ) :
    (MvPolynomial (Fin (r + n + e) ⊕ Fin (r + n + e)) ℂ ⧸
      (canonicalCoefficientIdeal r n e).restrictScalars ℂ) ≃ₗ[ℂ]
    (MvPolynomial (Variables (r + n + e)) ℂ ⧸
      (Ideal.map (colorCoordinates (r + n + e)).toRingHom
        (canonicalCoefficientIdeal r n e)).restrictScalars ℂ) :=
  (Ideal.quotientEquivAlg (canonicalCoefficientIdeal r n e) _
    (colorCoordinates (r + n + e)) rfl).toLinearEquiv

/-- A bound on the concrete canonical coefficient quotient transfers to
the actual CV cyclic module. -/
theorem cyclicSpan_bound_of_canonical (R : CurrentModule bracketTable V) (w : V)
    {e n r : ℕ} (h : CV3Rel R w (e, 0) (n, 0) (r, 0) 0)
    [FiniteDimensional ℂ
      (MvPolynomial (Fin (r + n + e) ⊕ Fin (r + n + e)) ℂ ⧸
        (canonicalCoefficientIdeal r n e).restrictScalars ℂ)] :
    FiniteDimensional ℂ (CVRectSingle.cyclicSpan R w) ∧
      Module.finrank ℂ (CVRectSingle.cyclicSpan R w) ≤
        Module.finrank ℂ
          (MvPolynomial (Fin (r + n + e) ⊕ Fin (r + n + e)) ℂ ⧸
            (canonicalCoefficientIdeal r n e).restrictScalars ℂ) := by
  let E := canonicalQuotientLinearEquiv r n e
  haveI := E.finiteDimensional
  have hb := cyclicSpan_bound_of_ideal R w h _ (canonicalCoefficientIdeal_le R w h)
  exact ⟨hb.1, hb.2.trans_eq E.finrank_eq.symm⟩

end
end VOA.DeligneAudit.A2.CVRectPolynomial

#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.canonical_reverse_coefficient
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.finite_coefficient_eq_mixed
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.canonical_coefficient_zero
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.canonicalCoefficientIdeal_le
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.canonicalQuotientLinearEquiv
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.cyclicSpan_bound_of_canonical
