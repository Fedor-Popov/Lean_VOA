import VOA.DeligneAudit.D4LeviKSTargetSymmetricEmbeds

/-! Pure three-alphabet products span the PAIR target algebra. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

abbrev PairTargetFactors (a b c : ℕ) :=
  symmetricSubalgebra (Fin a) ℂ ×
    symmetricSubalgebra (Fin b) ℂ ×
      symmetricSubalgebra (Fin c) ℂ

noncomputable def pairTargetPure (a b c : ℕ)
    (F : PairTargetFactors a b c) : MvPolynomial (PairTarget a b c) ℂ :=
  rename Sum.inl F.1.val *
    rename (fun y : Fin b => (Sum.inr (Sum.inl y) : PairTarget a b c)) F.2.1.val *
    rename (fun z : Fin c => (Sum.inr (Sum.inr z) : PairTarget a b c)) F.2.2.val

private theorem pairTargetPure_mul (a b c : ℕ)
    (F G : PairTargetFactors a b c) :
    pairTargetPure a b c (F * G) = pairTargetPure a b c F * pairTargetPure a b c G := by
  simp only [pairTargetPure, Prod.fst_mul, Prod.snd_mul, Subalgebra.coe_mul, map_mul]
  ring

private theorem pairTargetPure_one (a b c : ℕ) :
    pairTargetPure a b c 1 = 1 := by
  simp [pairTargetPure]

noncomputable def pairTargetPureSpan (a b c : ℕ) :
    Submodule ℂ (MvPolynomial (PairTarget a b c) ℂ) :=
  Submodule.span ℂ (Set.range (pairTargetPure a b c))

private theorem pairTargetPureSpan_mul (a b c : ℕ)
    {P Q : MvPolynomial (PairTarget a b c) ℂ}
    (hP : P ∈ pairTargetPureSpan a b c)
    (hQ : Q ∈ pairTargetPureSpan a b c) :
    P * Q ∈ pairTargetPureSpan a b c := by
  let S := pairTargetPureSpan a b c
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨F, rfl⟩ := hP
      induction hQ using Submodule.span_induction with
      | mem Q hQ =>
          obtain ⟨G, rfl⟩ := hQ
          rw [← pairTargetPure_mul]
          exact Submodule.subset_span ⟨F * G, rfl⟩
      | zero => simp
      | add Q R _ _ hQ hR =>
          simpa only [mul_add] using S.add_mem hQ hR
      | smul t Q _ hQ =>
          simpa only [mul_smul_comm] using S.smul_mem t hQ
  | zero => simp
  | add P R _ _ hP hR =>
      simpa only [add_mul] using S.add_mem hP hR
  | smul t P _ hP =>
      simpa only [smul_mul_assoc] using S.smul_mem t hP

private theorem pairTargetPureSpan_one (a b c : ℕ) :
    (1 : MvPolynomial (PairTarget a b c) ℂ) ∈ pairTargetPureSpan a b c := by
  rw [← pairTargetPure_one a b c]
  exact Submodule.subset_span ⟨1, rfl⟩

private theorem pairTargetPureSpan_algebraMap (a b c : ℕ) (t : ℂ) :
    algebraMap ℂ (MvPolynomial (PairTarget a b c) ℂ) t ∈
      pairTargetPureSpan a b c := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (pairTargetPureSpan a b c).smul_mem t (pairTargetPureSpan_one a b c)

private theorem pairTargetPureSpan_targetPower (a b c : ℕ)
    (j : Fin 3) (r : ℕ) :
    pairTargetPower a b c j r ∈ pairTargetPureSpan a b c := by
  fin_cases j
  · let F : PairTargetFactors a b c :=
      (⟨psum (Fin a) ℂ r, psum_isSymmetric (Fin a) ℂ r⟩, 1, 1)
    have h : pairTargetPure a b c F = pairTargetPower a b c 0 r := by
      simp [F, pairTargetPure, pairTargetPower, pairTargetXPsum, psum]
    simpa only [h] using
      (Submodule.subset_span ⟨F, rfl⟩ :
        pairTargetPure a b c F ∈ pairTargetPureSpan a b c)
  · let F : PairTargetFactors a b c :=
      (1, ⟨psum (Fin b) ℂ r, psum_isSymmetric (Fin b) ℂ r⟩, 1)
    have h : pairTargetPure a b c F = pairTargetPower a b c 1 r := by
      simp [F, pairTargetPure, pairTargetPower, targetYPsum, psum]
    simpa only [h] using
      (Submodule.subset_span ⟨F, rfl⟩ :
        pairTargetPure a b c F ∈ pairTargetPureSpan a b c)
  · let F : PairTargetFactors a b c :=
      (1, 1, ⟨psum (Fin c) ℂ r, psum_isSymmetric (Fin c) ℂ r⟩)
    have h : pairTargetPure a b c F = pairTargetPower a b c 2 r := by
      simp [F, pairTargetPure, pairTargetPower, pairTargetZPsum, psum]
    simpa only [h] using
      (Submodule.subset_span ⟨F, rfl⟩ :
        pairTargetPure a b c F ∈ pairTargetPureSpan a b c)

/-- Every separately symmetric target polynomial is a linear combination
    of products with one symmetric factor in each alphabet. -/
theorem pairTargetSymmetric_le_pureSpan (a b c : ℕ) :
    (pairTargetSymmetric a b c).toSubmodule ≤ pairTargetPureSpan a b c := by
  intro P hP
  change P ∈ pairTargetSymmetric a b c at hP
  induction hP using Algebra.adjoin_induction with
  | mem P hP =>
      rcases hP with ⟨⟨j, r⟩, rfl⟩
      exact pairTargetPureSpan_targetPower a b c j r
  | algebraMap t => exact pairTargetPureSpan_algebraMap a b c t
  | add P Q _ _ hP hQ =>
      exact (pairTargetPureSpan a b c).add_mem hP hQ
  | mul P Q _ _ hP hQ =>
      exact pairTargetPureSpan_mul a b c hP hQ

/-- The target symmetric algebra is exactly the linear span of pure
    products from its three independent symmetric alphabets. -/
theorem pairTargetSymmetric_eq_pureSpan (a b c : ℕ) :
    (pairTargetSymmetric a b c).toSubmodule = pairTargetPureSpan a b c := by
  apply le_antisymm (pairTargetSymmetric_le_pureSpan a b c)
  rw [pairTargetPureSpan, Submodule.span_le]
  rintro P ⟨F, rfl⟩
  change pairTargetPure a b c F ∈ pairTargetSymmetric a b c
  exact pairTarget_separate_symmetric_mem a b c
    F.1.val F.2.1.val F.2.2.val F.1.property F.2.1.property F.2.2.property

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairTargetSymmetric_le_pureSpan
#print axioms VOA.DeligneAudit.D4Levi.pairTargetSymmetric_eq_pureSpan
