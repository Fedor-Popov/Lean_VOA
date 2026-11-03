import VOA.DeligneAudit.D4LeviKSFlagYZCoefficients

/-! Relative X-over-YZ reduction at an exact total degree. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

theorem ksFlag_rx_mem_relation (m a b c s D : ℕ)
    (hs : m + 1 ≤ c + a + b + s) (hsD : s ≤ D) :
    (rxMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) ∈
      ksFlagRelationImage m a b c D := by
  by_cases hx : 1 ≤ a + b
  · exact ⟨rxMixedTarget a b c s,
      Submodule.subset_span (Or.inr (Or.inr
        ⟨s, D - s, 1, hx, hs, by omega, (one_mul _).symm⟩)), rfl⟩
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst a
    subst b
    have he : (rxMixedTarget 0 0 c s : MvPolynomial (PairTarget 0 0 c) ℂ) =
        (ryMixedTarget 0 0 c s : MvPolynomial (PairTarget 0 0 c) ℂ) := by
      rw [← ksTargetXYZAlphabet_coeff]
      simp only [ksTargetXAlphabet, List.ofFn_zero, List.nil_append,
        ksTargetYZAlphabet_coeff]
    rw [he]
    exact ksFlag_ry_mem_relation m 0 0 c s D (by omega) hsD

/-- All unpaired-X degrees are reduced to the `a × (m-c-b-a)` box, with
    homogeneous coefficients separately symmetric in Y and Z. -/
theorem ksFlag_x_box_step (m a b c d e : ℕ) (habc : a + b + c ≤ m)
    (U : MvPolynomial (PairTarget a b c) ℂ) (hU : U ∈ ksFlagYZCoefficient a b c e)
    (P : MvPolynomial (Fin a) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin a) ℂ) (hd : P.IsHomogeneous d) :
    U * ksTargetXMap a b c P ∈
      ksRelativeBoxSpan (m - c - b) a (e + d) (ksTargetXMap a b c)
        (ksFlagYZCoefficient a b c) ⊔ ksFlagRelationImage m a b c (e + d) := by
  apply ksRelative_box_span (m - c - b) a (e + d) (by omega)
    (ksTargetXMap a b c) (ksFlagYZCoefficient a b c)
    (fun r => (ryMixedTarget a b c r : MvPolynomial (PairTarget a b c) ℂ))
    (fun s => (rxMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ))
    (ksFlagRelationImage m a b c (e + d))
    (ksFlagYZCoefficient_mul a b c) (ksFlagYZCoefficient_hsymm a b c)
    (ksFlagX_convolution a b c) ?_ d e rfl U hU P hP hd
  intro s e' v hs he U' hU' W hW hdW
  apply ksFlagRelationImage_mul
  · exact (pairTargetSymmetric a b c).mul_mem
      (ksFlagYZCoefficient_symmetric a b c e' U' hU')
      (ksTargetXMap_symmetric a b c W hW)
  · exact ksFlag_rx_mem_relation m a b c s (e + d) (by omega) (by omega)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksFlag_rx_mem_relation
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_x_box_step
