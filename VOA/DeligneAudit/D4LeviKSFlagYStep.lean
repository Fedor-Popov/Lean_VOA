import VOA.DeligneAudit.D4LeviKSFlagConvolution

/-! Relative Y-over-Z reduction at an exact total degree. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

/-- The maximal Y generator also has the expected meaning when the Y block is empty. -/
theorem ksFlag_ry_mem_relation (m a b c s D : ℕ)
    (hs : m + 1 ≤ c + b + s) (hsD : s ≤ D) :
    (ryMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ) ∈
      ksFlagRelationImage m a b c D := by
  by_cases hb : 1 ≤ b
  · exact ⟨ryMixedTarget a b c s,
      Submodule.subset_span (Or.inr (Or.inl
        ⟨s, D - s, 1, hb, hs, by omega, (one_mul _).symm⟩)), rfl⟩
  · have hb0 : b = 0 := by omega
    subst b
    have he : (ryMixedTarget a 0 c s : MvPolynomial (PairTarget a 0 c) ℂ) =
        ksTargetZMap a 0 c (hsymm (Fin c) ℂ s) := by
      rw [← ksTargetYZAlphabet_coeff]
      simp only [ksTargetYAlphabet, List.ofFn_zero, List.nil_append,
        ksTargetZAlphabet_coeff]
    rw [he]
    by_cases hc : 1 ≤ c
    · exact ⟨rzFullHSymm a 0 c s,
        Submodule.subset_span (Or.inl
          ⟨s, D - s, 1, hc, by omega, by omega, (one_mul _).symm⟩), rfl⟩
    · have hc0 : c = 0 := by omega
      subst c
      rw [ksHsymm_empty_of_pos s (by omega), map_zero]
      exact Submodule.zero_mem _

/-- All Y degrees are reduced to the `b × (m-c-b)` box, with homogeneous
    Z coefficients. No positivity assumption on the size of the Y block is needed. -/
theorem ksFlag_y_box_step (m a b c d e : ℕ) (hbc : b + c ≤ m)
    (U : MvPolynomial (PairTarget a b c) ℂ) (hU : U ∈ ksFlagZCoefficient a b c e)
    (P : MvPolynomial (Fin b) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin b) ℂ) (hd : P.IsHomogeneous d) :
    U * ksTargetYMap a b c P ∈
      ksRelativeBoxSpan (m - c) b (e + d) (ksTargetYMap a b c)
        (ksFlagZCoefficient a b c) ⊔ ksFlagRelationImage m a b c (e + d) := by
  apply ksRelative_box_span (m - c) b (e + d) (by omega)
    (ksTargetYMap a b c) (ksFlagZCoefficient a b c)
    (fun r => ksTargetZMap a b c (hsymm (Fin c) ℂ r))
    (fun s => (ryMixedTarget a b c s : MvPolynomial (PairTarget a b c) ℂ))
    (ksFlagRelationImage m a b c (e + d))
    (fun e f U W hU hW => ksBlockCoefficient_mul c e f _ U W hU hW)
    (fun r => ksBlockCoefficient_hsymm c r _)
    (ksFlagY_convolution a b c) ?_ d e rfl U hU P hP hd
  intro s e' v hs he U' hU' W hW hdW
  apply ksFlagRelationImage_mul
  · exact (pairTargetSymmetric a b c).mul_mem
      (ksFlagZCoefficient_symmetric a b c e' U' hU')
      (ksTargetYMap_symmetric a b c W hW)
  · exact ksFlag_ry_mem_relation m a b c s (e + d) (by omega) (by omega)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksFlag_ry_mem_relation
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_y_box_step
