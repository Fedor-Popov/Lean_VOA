import VOA.DeligneAudit.D4LeviKSRzOrbitSpanAlgebra
import VOA.DeligneAudit.D4LeviKSOneBoxQuot
import VOA.DeligneAudit.LeviTypeA2CertGradedDefectWeight

/-! The occupation-to-symmetric-polynomial map for one block of variables. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.CLAssembly

/-- The occupation numbers of a labelled tuple of modes, including zero modes. -/
noncomputable def ksModeOccupation (n : ℕ) (v : Fin n → ℕ) : ℕ →₀ ℕ :=
  Multiset.toFinsupp (List.ofFn v : Multiset ℕ)

theorem ksModeOccupation_degree (n : ℕ) (v : Fin n → ℕ) :
    Finsupp.degree (ksModeOccupation n v) = n := by
  rw [ksModeOccupation, Finsupp.degree_apply]
  simp

/-- A canonical ordering of an occupation monomial of length `n`. -/
noncomputable def ksOccupationModes (n : ℕ) (f : ℕ →₀ ℕ)
    (h : Finsupp.degree f = n) : Fin n → ℕ :=
  fun i => (lst f).get ⟨i.1, by rw [length_lst, h]; exact i.2⟩

theorem ksOccupationModes_ofFn (n : ℕ) (f : ℕ →₀ ℕ)
    (h : Finsupp.degree f = n) :
    List.ofFn (ksOccupationModes n f h) = lst f := by
  apply List.ext_getElem
  · simp [length_lst, h]
  · intro i hi hj
    simp [ksOccupationModes]

theorem ksOccupationModes_sorted (n : ℕ) (v : Fin n → ℕ) :
    ksOccupationModes n (ksModeOccupation n v)
        (ksModeOccupation_degree n v) = v ∘ Tuple.sort v := by
  apply List.ofFn_injective
  rw [ksOccupationModes_ofFn]
  have hp : (lst (ksModeOccupation n v)).Perm (List.ofFn v) := by
    apply Multiset.coe_eq_coe.mp
    rw [lst_coe, ksModeOccupation, Multiset.toFinsupp_toMultiset]
  exact (hp.trans ((Tuple.sort v).ofFn_comp_perm v).symm).eq_of_pairwise'
    (lst_sorted _) (Tuple.monotone_sort v).sortedLE_ofFn.pairwise

theorem ksOrbitSum_rename (n : ℕ) (e : Equiv.Perm (Fin n))
    (P : MvPolynomial (Fin n) ℂ) :
    rzOrbitSum (Fin n) (rename e P) = rzOrbitSum (Fin n) P := by
  classical
  unfold rzOrbitSum
  apply Finset.sum_bij (fun f _ => f * e)
  · intro f hf; simp
  · intro f hf g hg heq
    exact mul_right_cancel heq
  · intro f hf
    exact ⟨f * e⁻¹, by simp, by group⟩
  · intro f hf
    simp [rename_rename]

theorem ksOrbitSum_modes_perm (n : ℕ) (v : Fin n → ℕ)
    (e : Equiv.Perm (Fin n)) :
    rzOrbitSum (Fin n) (∏ i, X i ^ v (e i)) =
      rzOrbitSum (Fin n) (∏ i, X i ^ v i) := by
  classical
  have hr : (∏ i, X i ^ v (e i) : MvPolynomial (Fin n) ℂ) =
      rename e.symm (∏ i, X i ^ v i) := by
    simp only [map_prod, map_pow, rename_X]
    exact Fintype.prod_equiv e (fun i => X i ^ v (e i))
      (fun j => X (e.symm j) ^ v j) (by intro i; simp)
  rw [hr, ksOrbitSum_rename]

/-- Full orbit sum on length `n` occupation monomials, zero on other lengths. -/
noncomputable def ksBlockTheta (n : ℕ) :
    R →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  modeWordEvaluation ℕ fun f =>
    if h : Finsupp.degree f = n then
      rzOrbitSum (Fin n) (∏ i, X i ^ ksOccupationModes n f h i)
    else 0

theorem ksBlockTheta_monomial (n : ℕ) (f : ℕ →₀ ℕ)
    (h : Finsupp.degree f = n) :
    ksBlockTheta n (monomial f 1) =
      rzOrbitSum (Fin n) (∏ i, X i ^ ksOccupationModes n f h i) := by
  change modeWordEvaluation ℕ _ (modeMonomial ℕ f) = _
  rw [modeWordEvaluation_monomial, dif_pos h]

/-- Evaluation is independent of the ordering chosen for the occupation monomial. -/
theorem ksBlockTheta_occupation (n : ℕ) (v : Fin n → ℕ) :
    ksBlockTheta n (monomial (ksModeOccupation n v) 1) =
      rzOrbitSum (Fin n) (∏ i, X i ^ v i) := by
  rw [ksBlockTheta_monomial n _ (ksModeOccupation_degree n v)]
  rw [ksOccupationModes_sorted]
  exact ksOrbitSum_modes_perm n v (Tuple.sort v)

theorem ksBlockTheta_symmetric (n : ℕ) (P : R) :
    ksBlockTheta n P ∈ symmetricSubalgebra (Fin n) ℂ := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial f t =>
      have ht : (monomial f t : R) = t • monomial f 1 := by
        simp only [smul_monomial, smul_eq_mul, mul_one]
      rw [ht, map_smul]
      apply Subalgebra.smul_mem
      change modeWordEvaluation ℕ _ (modeMonomial ℕ f) ∈ _
      rw [modeWordEvaluation_monomial]
      split
      · exact rzOrbitSum_symmetric _ _
      · exact zero_mem _
  | add P Q hP hQ =>
      rw [map_add]
      exact add_mem hP hQ

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksModeOccupation_degree
#print axioms VOA.DeligneAudit.D4Levi.ksOccupationModes_ofFn
#print axioms VOA.DeligneAudit.D4Levi.ksOccupationModes_sorted
#print axioms VOA.DeligneAudit.D4Levi.ksOrbitSum_rename
#print axioms VOA.DeligneAudit.D4Levi.ksOrbitSum_modes_perm
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_monomial
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_occupation
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_symmetric
