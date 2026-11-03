import VOA.DeligneAudit.DeligneFusionJetInterpolation
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Exact isolation of local two-jet operators

For arbitrary local endomorphisms A_i and B_i, define the shifted current
J_k as the sum of z_i^k A_i and k z_i^(k-1) B_i. The explicit Hermite value
and tangent polynomials recover each A_i and B_i from modes k<2*card(i).
No current-bracket, cyclicity or dimension assertion is assumed.
-/

namespace VOA.DeligneAudit.JetInterpolation

open Polynomial

noncomputable section

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The shifted current of an arbitrary family of local two-jet operators. -/
def jetOp (z : ι → K) (A B : ι → Module.End K V) (k : ℕ) : Module.End K V :=
  ∑ i, ((z i ^ k) • A i + ((k : K) * z i ^ (k - 1)) • B i)

/-- Evaluation of a scalar polynomial in the local two-jet operator family. -/
def jetPolynomialOp (z : ι → K) (A B : ι → Module.End K V) (P : K[X]) : Module.End K V :=
  ∑ i, (P.eval (z i) • A i + P.derivative.eval (z i) • B i)

theorem derivative_eval_eq_sum_range (P : K[X]) (D : ℕ) (hP : P.natDegree < D) (x : K) :
    P.derivative.eval x = ∑ k ∈ Finset.range D, P.coeff k * (k : K) * x ^ (k - 1) := by
  rw [Polynomial.derivative_eval]
  exact P.sum_over_range' (by intro k; simp only [zero_mul]) D hP

/-- Polynomial coefficients acting on shifted modes agree with actual local
value/derivative evaluation. -/
theorem sum_coeff_jetOp (z : ι → K) (A B : ι → Module.End K V)
    (P : K[X]) (D : ℕ) (hP : P.natDegree < D) :
    (∑ k ∈ Finset.range D, P.coeff k • jetOp z A B k) = jetPolynomialOp z A B P := by
  simp only [jetOp, jetPolynomialOp, Finset.smul_sum, smul_add, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.sum_smul,
    ← Polynomial.eval_eq_sum_range' hP (z i)]
  congr 1
  rw [derivative_eval_eq_sum_range P D hP (z i)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (mul_assoc _ _ _).symm

variable [DecidableEq ι]
variable (z : ι → K) (hz : Function.Injective z) (A B : ι → Module.End K V)

include hz

/-- The value polynomial recovers the exact local mode-zero operator. -/
theorem valueBasis_isolates (i : ι) :
    (∑ k ∈ Finset.range (2 * Fintype.card ι),
      (valueBasis z i).coeff k • jetOp z A B k) = A i := by
  rw [sum_coeff_jetOp z A B _ _ (valueBasis_natDegree_lt z hz i)]
  simp only [jetPolynomialOp, valueBasis_eval z hz, valueBasis_derivative_eval z hz,
    zero_smul, add_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The tangent polynomial recovers the exact local mode-one operator. -/
theorem tangentBasis_isolates (i : ι) :
    (∑ k ∈ Finset.range (2 * Fintype.card ι),
      (tangentBasis z i).coeff k • jetOp z A B k) = B i := by
  rw [sum_coeff_jetOp z A B _ _ (tangentBasis_natDegree_lt z hz i)]
  simp only [jetPolynomialOp, tangentBasis_eval z hz, tangentBasis_derivative_eval z hz,
    zero_smul, zero_add, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [DecidableEq ι] in
/-- Every local two-jet operator is in the actual linear span of shifted
current modes, uniformly in the number of sites and their local dimensions. -/
theorem local_mem_span_jetOp (i : ι) :
    A i ∈ Submodule.span K (Set.range (jetOp z A B)) ∧
      B i ∈ Submodule.span K (Set.range (jetOp z A B)) := by
  classical
  constructor
  · rw [← valueBasis_isolates z hz A B i]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [← tangentBasis_isolates z hz A B i]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

omit [DecidableEq ι] in
/-- Shifted currents and separate local two-jet operators have the same actual
linear span. This is independent of any Lie bracket or model identification. -/
theorem span_jetOp_eq :
    Submodule.span K (Set.range (jetOp z A B)) =
      Submodule.span K (Set.range A ∪ Set.range B) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    unfold jetOp
    apply Submodule.sum_mem
    intro i _
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))
  · apply Submodule.span_le.mpr
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (local_mem_span_jetOp z hz A B i).1
    · exact (local_mem_span_jetOp z hz A B i).2

omit [DecidableEq ι] in
/-- An actual vector subspace is invariant under shifted currents exactly when
it is invariant under both separate local modes. -/
theorem invariant_jetOp_iff (P : Submodule K V) :
    (∀ k, P ≤ P.comap (jetOp z A B k)) ↔
      (∀ i, P ≤ P.comap (A i)) ∧ (∀ i, P ≤ P.comap (B i)) := by
  classical
  constructor
  · intro h
    constructor
    · intro i v hv
      change A i v ∈ P
      rw [← valueBasis_isolates z hz A B i]
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h k hv)
    · intro i v hv
      change B i v ∈ P
      rw [← tangentBasis_isolates z hz A B i]
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h k hv)
  · rintro ⟨hA, hB⟩ k v hv
    change jetOp z A B k v ∈ P
    simp only [jetOp, LinearMap.coe_sum, Finset.sum_apply, LinearMap.add_apply,
      LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.add_mem _
      (Submodule.smul_mem _ _ (hA i hv)) (Submodule.smul_mem _ _ (hB i hv))

end
end VOA.DeligneAudit.JetInterpolation

#print axioms VOA.DeligneAudit.JetInterpolation.valueBasis_isolates
#print axioms VOA.DeligneAudit.JetInterpolation.tangentBasis_isolates
#print axioms VOA.DeligneAudit.JetInterpolation.local_mem_span_jetOp

#print axioms VOA.DeligneAudit.JetInterpolation.span_jetOp_eq
#print axioms VOA.DeligneAudit.JetInterpolation.invariant_jetOp_iff
