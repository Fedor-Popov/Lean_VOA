import VOA.DeligneAudit.D4LeviKSBlockTheta

/-! Homogeneous surjectivity of the one-block occupation model. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.Sl2Weyl

theorem ksListOccupation_weight (l : List ℕ) :
    Finsupp.weight om (Multiset.toFinsupp (l : Multiset ℕ)) =
      (l.length, l.sum) := by
  induction l with
  | nil => simp; rfl
  | cons r l ih =>
      rw [← Multiset.cons_coe, ← Multiset.singleton_add,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, map_add, ih]
      simp [Finsupp.weight_single, om, Nat.add_comm]

theorem ksModeOccupation_weight (n : ℕ) (v : Fin n → ℕ) :
    Finsupp.weight om (ksModeOccupation n v) = (n, ∑ i, v i) := by
  rw [ksModeOccupation, ksListOccupation_weight]
  simp [rz_sum_ofFn]

/-- Forget the labels of a monomial, retaining its multiset of modes. -/
noncomputable def ksBlockLift (n : ℕ) :
    MvPolynomial (Fin n) ℂ →ₗ[ℂ] R :=
  modeWordEvaluation (Fin n) fun f => monomial (ksModeOccupation n f) 1

theorem ksBlockLift_monomial (n : ℕ) (f : Fin n →₀ ℕ) (t : ℂ) :
    ksBlockLift n (monomial f t) = t • monomial (ksModeOccupation n f) 1 := by
  have ht : (monomial f t : MvPolynomial (Fin n) ℂ) = t • monomial f 1 := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [ht, map_smul]
  congr 1
  exact modeWordEvaluation_monomial _ _ _

theorem ksBlockTheta_lift (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    ksBlockTheta n (ksBlockLift n P) = rzOrbitSum (Fin n) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial f t =>
      rw [ksBlockLift_monomial, map_smul, ksBlockTheta_occupation]
      have ht : (monomial f t : MvPolynomial (Fin n) ℂ) =
          t • ∏ i, X i ^ f i := by
        rw [MvPolynomial.prod_X_pow]
        have he : Finsupp.indicator Finset.univ (fun i _ => f i) = f := by
          ext i
          simp [Finsupp.indicator]
        rw [he]
        simp only [smul_monomial, smul_eq_mul, mul_one]
      rw [ht, rzOrbitSum_smul]
  | add P Q hP hQ =>
      rw [map_add, map_add, hP, hQ, rzOrbitSum_add]

theorem ksBlockLift_homogeneous (n d : ℕ) (P : MvPolynomial (Fin n) ℂ)
    (hP : P.IsHomogeneous d) :
    IsWeightedHomogeneous om (ksBlockLift n P) (n, d) := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply (weightedHomogeneousSubmodule ℂ om (n, d)).sum_mem
  intro f hf
  rw [ksBlockLift_monomial]
  apply (weightedHomogeneousSubmodule ℂ om (n, d)).smul_mem
  apply isWeightedHomogeneous_monomial
  rw [ksModeOccupation_weight]
  congr 1
  have hd : Finsupp.degree f = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (MvPolynomial.mem_support_iff.mp hf)
  rw [← hd, Finsupp.degree_apply]
  exact (Finsupp.sum_fintype f (fun _ r => r) (by intro i; rfl)).symm

/-- Every homogeneous symmetric polynomial is the image of an occupation
    polynomial of exactly the required length and mode degree. -/
theorem ksBlockTheta_surjective_graded (n d : ℕ)
    (P : MvPolynomial (Fin n) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin n) ℂ) (hd : P.IsHomogeneous d) :
    ∃ Q : R, IsWeightedHomogeneous om Q (n, d) ∧ ksBlockTheta n Q = P := by
  let t : ℂ := Nat.card (Equiv.Perm (Fin n))
  have ht : t ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  refine ⟨t⁻¹ • ksBlockLift n P, ?_, ?_⟩
  · exact (weightedHomogeneousSubmodule ℂ om (n, d)).smul_mem _
      (ksBlockLift_homogeneous n d P hd)
  · rw [map_smul, ksBlockTheta_lift,
      rzOrbitSum_eq_card_smul_of_symmetric _ P hP]
    change t⁻¹ • t • P = P
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksListOccupation_weight
#print axioms VOA.DeligneAudit.D4Levi.ksModeOccupation_weight
#print axioms VOA.DeligneAudit.D4Levi.ksBlockLift_monomial
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_lift
#print axioms VOA.DeligneAudit.D4Levi.ksBlockLift_homogeneous
#print axioms VOA.DeligneAudit.D4Levi.ksBlockTheta_surjective_graded
