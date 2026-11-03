import VOA.DeligneAudit.D4LeviKSBlockMaximal

/-! Maximal one-alphabet relations with homogeneous multipliers retained. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

/-- Complete homogeneous polynomials have their indicated mode degree. -/
theorem ksHsymm_homogeneous (n s : ℕ) :
    (hsymm (Fin n) ℂ s).IsHomogeneous s := by
  classical
  rw [rz_hsymm_eq_sum_vectors]
  apply IsHomogeneous.sum
  intro e he
  simpa only [e.property] using
    IsHomogeneous.prod Finset.univ (fun i => X i ^ e.1 i) e.1
      (fun i _ => isHomogeneous_X_pow i (e.1 i))

theorem ksOrbitSum_homogeneous (n d : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : P.IsHomogeneous d) : (rzOrbitSum (Fin n) P).IsHomogeneous d := by
  classical
  exact IsHomogeneous.sum _ _ _ fun e _ => hP.rename_isHomogeneous

theorem ksHomogeneousComponent_rename {σ τ : Type*} (f : σ → τ)
    (d : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent d (rename f P) = rename f (homogeneousComponent d P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial e t =>
      have hh : (monomial e t : MvPolynomial σ ℂ).IsHomogeneous e.degree := by
        exact isHomogeneous_monomial t rfl
      rw [homogeneousComponent_of_mem hh.rename_isHomogeneous,
        homogeneousComponent_of_mem hh]
      split_ifs <;> simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem ksHomogeneousComponent_symmetric (n d : ℕ)
    (P : MvPolynomial (Fin n) ℂ) (hP : P ∈ symmetricSubalgebra (Fin n) ℂ) :
    homogeneousComponent d P ∈ symmetricSubalgebra (Fin n) ℂ := by
  change P.IsSymmetric at hP
  intro e
  rw [← ksHomogeneousComponent_rename, hP e]

theorem ksHomogeneousComponent_mul_homogeneous {σ : Type*} (d s : ℕ)
    (hs : s ≤ d) (U H : MvPolynomial σ ℂ) (hH : H.IsHomogeneous s) :
    homogeneousComponent d (U * H) = homogeneousComponent (d - s) U * H := by
  induction U using MvPolynomial.induction_on' with
  | monomial e t =>
      have hh : (monomial e t : MvPolynomial σ ℂ).IsHomogeneous e.degree := by
        exact isHomogeneous_monomial t rfl
      rw [homogeneousComponent_of_mem (hh.mul hH), homogeneousComponent_of_mem hh]
      by_cases hd : d = e.degree + s
      · have he : d - s = e.degree := by omega
        simp [hd]
      · have he : d - s ≠ e.degree := by omega
        simp [hd, he]
  | add P Q hP hQ => simp only [add_mul, map_add, hP, hQ]

noncomputable def ksBlockGradedMaximalSpan (q n d : ℕ) :
    Submodule ℂ (MvPolynomial (Fin n) ℂ) :=
  Submodule.span ℂ {T | ∃ s : ℕ, q + 1 ≤ n + s ∧ s ≤ d ∧
    ∃ U : MvPolynomial (Fin n) ℂ,
      U ∈ symmetricSubalgebra (Fin n) ℂ ∧ U.IsHomogeneous (d - s) ∧
        T = U * hsymm (Fin n) ℂ s}

theorem ksBlockMaximal_component_mem (q n d : ℕ)
    (P : MvPolynomial (Fin n) ℂ) (hP : P ∈ ksBlockMaximalSpan q n d) :
    homogeneousComponent d P ∈ ksBlockGradedMaximalSpan q n d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨s, hs, hsd, U, hU, rfl⟩ := hP
      rw [ksHomogeneousComponent_mul_homogeneous d s hsd U _
        (ksHsymm_homogeneous n s)]
      exact Submodule.subset_span ⟨s, hs, hsd, _,
        ksHomogeneousComponent_symmetric n (d - s) U hU,
        homogeneousComponent_isHomogeneous _ _, rfl⟩
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
      simpa only [map_add] using Submodule.add_mem _ ihP ihQ
  | smul t P hP ihP =>
      simpa only [map_smul] using Submodule.smul_mem _ t ihP

theorem ksBlockBoxPolys_homogeneous (q n d : ℕ) (hn : n ≤ q)
    (P : MvPolynomial (Fin n) ℂ) (hP : P ∈ ksBlockBoxPolys q n d) :
    P.IsHomogeneous d := by
  obtain ⟨v, _, hv, rfl⟩ := ksBlockBoxPolys_spec q n d hn P hP
  apply ksOrbitSum_homogeneous
  rw [← hv]
  exact IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow i (v i)

/-- The box theorem with every relation multiplier homogeneous of degree `d - s`. -/
theorem ksBlockSymmetric_span_graded_maximal (q n d : ℕ) (hn : n ≤ q)
    (P : MvPolynomial (Fin n) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin n) ℂ) (hd : P.IsHomogeneous d) :
    P ∈ Submodule.span ℂ (ksBlockBoxPolys q n d : Set _) ⊔
      ksBlockGradedMaximalSpan q n d := by
  obtain ⟨B, hB, C, hC, heq⟩ := Submodule.mem_sup.mp
    (ksBlockSymmetric_span_maximal q n d hn P hP hd)
  have hcP : homogeneousComponent d P = P := by
    rw [homogeneousComponent_of_mem hd, if_pos rfl]
  rw [← hcP, ← heq, map_add]
  apply Submodule.add_mem_sup
  · clear heq
    induction hB using Submodule.span_induction with
    | mem B hB =>
        rw [homogeneousComponent_of_mem (ksBlockBoxPolys_homogeneous q n d hn B hB),
          if_pos rfl]
        exact Submodule.subset_span hB
    | zero => simp
    | add B C hB hC ihB ihC =>
        simpa only [map_add] using Submodule.add_mem _ ihB ihC
    | smul t B hB ihB =>
        simpa only [map_smul] using Submodule.smul_mem _ t ihB
  · exact ksBlockMaximal_component_mem q n d C hC

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksHsymm_homogeneous
#print axioms VOA.DeligneAudit.D4Levi.ksOrbitSum_homogeneous
#print axioms VOA.DeligneAudit.D4Levi.ksHomogeneousComponent_rename
#print axioms VOA.DeligneAudit.D4Levi.ksHomogeneousComponent_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksHomogeneousComponent_mul_homogeneous
#print axioms VOA.DeligneAudit.D4Levi.ksBlockMaximal_component_mem
#print axioms VOA.DeligneAudit.D4Levi.ksBlockBoxPolys_homogeneous
#print axioms VOA.DeligneAudit.D4Levi.ksBlockSymmetric_span_graded_maximal
