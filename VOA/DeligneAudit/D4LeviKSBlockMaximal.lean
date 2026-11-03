import VOA.DeligneAudit.D4LeviKSHsymmSeries

/-! One-alphabet boxes modulo maximal complete homogeneous relations. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

theorem ksOrbitSum_mul_symmetric (n : ℕ) (P H : MvPolynomial (Fin n) ℂ)
    (hH : H ∈ symmetricSubalgebra (Fin n) ℂ) :
    rzOrbitSum (Fin n) (P * H) = rzOrbitSum (Fin n) P * H := by
  classical
  change H.IsSymmetric at hH
  simp only [rzOrbitSum, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [hH e]

/-- Symmetric multiples of the full-alphabet relations whose generator degree
    does not exceed the degree being reduced. -/
noncomputable def ksBlockMaximalSpan (q n d : ℕ) :
    Submodule ℂ (MvPolynomial (Fin n) ℂ) :=
  Submodule.span ℂ {T | ∃ s : ℕ, q + 1 ≤ n + s ∧ s ≤ d ∧
    ∃ U : MvPolynomial (Fin n) ℂ,
      U ∈ symmetricSubalgebra (Fin n) ℂ ∧ T = U * hsymm (Fin n) ℂ s}

/-- Complement removal, as an identity of ordinary symmetric polynomials. -/
theorem ksHsymm_subset_identity (k l s : ℕ) :
    rename (Fin.castAdd l) (hsymm (Fin k) ℂ s) =
      ∑ p ∈ Finset.antidiagonal s,
        hsymm (Fin (k + l)) ℂ p.1 *
          (ksEPoly (List.ofFn fun j : Fin l =>
            (X (Fin.natAdd k j) : MvPolynomial (Fin (k + l)) ℂ))).coeff p.2 := by
  let vs := List.ofFn fun i : Fin k =>
    (X (Fin.castAdd l i) : MvPolynomial (Fin (k + l)) ℂ)
  let ws := List.ofFn fun j : Fin l =>
    (X (Fin.natAdd k j) : MvPolynomial (Fin (k + l)) ℂ)
  have hcat : vs ++ ws = List.ofFn fun i : Fin (k + l) =>
      (X i : MvPolynomial (Fin (k + l)) ℂ) := List.ofFn_add.symm
  have hc : PowerSeries.coeff s (ksHSeries vs) =
      rename (Fin.castAdd l) (hsymm (Fin k) ℂ s) :=
    ksHSeries_coeff_aeval k s (fun i => X (Fin.castAdd l i))
  rw [← hc, ksHSeries_remove_coeff vs ws s, hcat]
  simp only [ksHSeries_coeff_hsymm, ws]

/-- Every subset generator lies in the span of symmetric multiples of full
    complete homogeneous generators, with the required threshold and degree. -/
theorem ksBlockGarlandSeed_mem_maximal (q k l s d : ℕ) (β : Fin l → ℕ)
    (hqs : q + 1 ≤ k + s) (hsd : s ≤ d) :
    ksBlockGarlandSeed k l s β ∈ ksBlockMaximalSpan q (k + l) d := by
  classical
  let W := List.ofFn fun j : Fin l =>
    (X (Fin.natAdd k j) : MvPolynomial (Fin (k + l)) ℂ)
  let B : MvPolynomial (Fin (k + l)) ℂ :=
    ∏ j : Fin l, X (Fin.natAdd k j) ^ β j
  rw [ksBlockGarlandSeed, ksHsymm_subset_identity, Finset.sum_mul, ksOrbitSum_sum]
  apply Submodule.sum_mem
  intro p hp
  have hps := Finset.mem_antidiagonal.mp hp
  by_cases hj : l < p.2
  · have hz : (ksEPoly W).coeff p.2 = 0 :=
      ksEPoly_coeff_eq_zero W p.2 (by simpa [W] using hj)
    change rzOrbitSum _ ((hsymm _ _ p.1 * (ksEPoly W).coeff p.2) * B) ∈ _
    simp [hz, rzOrbitSum]
  · have hr : (hsymm (Fin (k + l)) ℂ p.1 * (ksEPoly W).coeff p.2) * B =
        ((ksEPoly W).coeff p.2 * B) * hsymm (Fin (k + l)) ℂ p.1 := by ring
    change rzOrbitSum _ ((hsymm _ _ p.1 * (ksEPoly W).coeff p.2) * B) ∈ _
    rw [hr, ksOrbitSum_mul_symmetric _ _ _ (hsymm_isSymmetric _ _ _)]
    exact Submodule.subset_span
      ⟨p.1, by omega, by omega, _, rzOrbitSum_symmetric _ _, rfl⟩

theorem ksBlockGarlandSpan_le_maximal (q n d : ℕ) :
    ksBlockGarlandSpan q n d ≤ ksBlockMaximalSpan q n d := by
  apply Submodule.span_le.mpr
  rintro T ⟨k, l, s, hn, β, hk, hqs, hd, rfl⟩
  subst n
  simp only [finCongr_refl, Equiv.coe_refl, rename_id]
  exact ksBlockGarlandSeed_mem_maximal q k l s d β hqs (by omega)

/-- The full one-alphabet box theorem with only maximal generators. This is
    the outer-alphabet-free step of the partial-flag reduction. -/
theorem ksBlockSymmetric_span_maximal (q n d : ℕ) (hn : n ≤ q)
    (P : MvPolynomial (Fin n) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin n) ℂ) (hd : P.IsHomogeneous d) :
    P ∈ Submodule.span ℂ (ksBlockBoxPolys q n d : Set _) ⊔
      ksBlockMaximalSpan q n d :=
  (sup_le_sup_left (ksBlockGarlandSpan_le_maximal q n d) _)
    (ksBlockSymmetric_span_graded q n d hn P hP hd)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksOrbitSum_mul_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksHsymm_subset_identity
#print axioms VOA.DeligneAudit.D4Levi.ksBlockGarlandSeed_mem_maximal
#print axioms VOA.DeligneAudit.D4Levi.ksBlockGarlandSpan_le_maximal
#print axioms VOA.DeligneAudit.D4Levi.ksBlockSymmetric_span_maximal
