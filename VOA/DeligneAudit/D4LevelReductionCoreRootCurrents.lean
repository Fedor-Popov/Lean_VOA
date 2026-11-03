import VOA.DeligneAudit.D4LevelReductionCoreCellCurrents
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! Root current relations and finite-dimensional highest-weight nilpotence for the core. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A lowering operator is locally nilpotent on every Cartan eigenvector in finite dimension. -/
theorem coreLowering_locally_nilpotent [FiniteDimensional ℂ V]
    (F H : Module.End ℂ V)
    (hHF : ∀ x, H (F x) - F (H x) = (-2 : ℂ) • F x)
    (v : V) (μ : ℂ) (hv : H v = μ • v) : ∃ N : ℕ, F^[N] v = 0 := by
  by_contra hn
  have hnz : ∀ n : ℕ, F^[n] v ≠ 0 := fun n hz => hn ⟨n, hz⟩
  have hinj : Function.Injective (fun n : ℕ => μ - 2 * (n : ℂ)) := by
    intro n m he
    have hc : (n : ℂ) = (m : ℂ) := by linear_combination (-1 / 2) * he
    exact_mod_cast hc
  have hsub : Set.range (fun n : ℕ => μ - 2 * (n : ℂ)) ⊆
      Module.End.HasEigenvalue H := by
    rintro ν ⟨n, rfl⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
    exact Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (sl2_H_Fpow F H hHF v μ hv n), hnz n⟩
  exact ((Module.End.finite_hasEigenvalue H).subset hsub).not_infinite
    (Set.infinite_range_of_injective hinj)

/-- Finite-dimensional highest vectors satisfy the sharp integral lowering relation. -/
theorem coreHighest_lowering_nilpotent [FiniteDimensional ℂ V]
    {E H F : ℕ → Module.End ℂ V} (hS : CVsl2.SL2 E H F)
    (v : V) (d : ℕ) (hE : E 0 v = 0) (hH : H 0 v = (d : ℂ) • v) :
    (F 0 ^ (d + 1)) v = 0 := by
  have hEF : ∀ x, E 0 (F 0 x) - F 0 (E 0 x) = H 0 x := by
    intro x
    exact congrArg (fun T : Module.End ℂ V => T x) (hS.hEF 0 0)
  have hHF : ∀ x, H 0 (F 0 x) - F 0 (H 0 x) = (-2 : ℂ) • F 0 x := by
    intro x
    exact congrArg (fun T : Module.End ℂ V => T x) (hS.hHF 0 0)
  obtain ⟨N, hN⟩ := coreLowering_locally_nilpotent (F 0) (H 0) hHF v d hH
  simpa only [Module.End.pow_apply] using sl2_sharpen (E 0) (F 0) (H 0)
    hEF hHF v d hE hH hN

/-- The commutator formula in the endomorphism algebra of an arbitrary core current module. -/
theorem coreCurrent_commutator (Q : CurrentModule A3Sector.bracketTable V)
    (e f : Fin 15) (r s : ℕ) :
    Q.op e r * Q.op f s - Q.op f s * Q.op e r =
      ∑ k, A3Sector.bracketTable e f k • Q.op k (r + s) := by
  ext v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply]
  exact Q.comm e f r s v

private theorem coreOuter_rootTable :
    (∀ k : Fin 15, A3Sector.bracketTable 0 6 k = if k = 12 then 1 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 12 6 k = if k = 6 then -2 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 12 0 k = if k = 0 then 2 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 6 6 k = 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 0 0 k = 0) := by
  have ht :
      (∀ k : Fin 15, A3Sector.bracketInt 0 6 k = if k = 12 then 1 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 12 6 k = if k = 6 then -2 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 12 0 k = if k = 0 then 2 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 6 6 k = 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 0 0 k = 0) := by decide +kernel
  unfold A3Sector.bracketTable
  exact_mod_cast ht

/-- The first outer-root currents satisfy the rank-one current relations. -/
theorem coreOuter_currentRelations (Q : CurrentModule A3Sector.bracketTable V) :
    CVsl2.SL2 (Q.op 0) (Q.op 12) (Q.op 6) := by
  obtain ⟨hEF, hHF, hHE, hFF, hEE⟩ := coreOuter_rootTable
  refine ⟨fun r s => ?_, fun r s => ?_, fun r s => ?_,
    fun r s => ?_, fun r s => ?_⟩
  · rw [coreCurrent_commutator]
    simp [hEF]
  · rw [coreCurrent_commutator]
    simp [hHF, ite_smul]
  · rw [coreCurrent_commutator]
    simp [hHE, ite_smul]
  · rw [← sub_eq_zero, coreCurrent_commutator]
    simp [hFF]
  · rw [← sub_eq_zero, coreCurrent_commutator]
    simp [hEE]

/-- The highest-root Cartan current is the sum of the three simple Cartan currents. -/
def coreHighestCartan (Q : CurrentModule A3Sector.bracketTable V) (s : ℕ) :
    Module.End ℂ V := Q.op 12 s + Q.op 13 s + Q.op 14 s

private theorem coreHighest_rootTable :
    (∀ k : Fin 15, A3Sector.bracketTable 2 8 k =
      (if k = 12 then 1 else 0) + (if k = 13 then 1 else 0) +
        (if k = 14 then 1 else 0)) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 12 8 k + A3Sector.bracketTable 13 8 k +
      A3Sector.bracketTable 14 8 k = if k = 8 then -2 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 12 2 k + A3Sector.bracketTable 13 2 k +
      A3Sector.bracketTable 14 2 k = if k = 2 then 2 else 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 8 8 k = 0) ∧
    (∀ k : Fin 15, A3Sector.bracketTable 2 2 k = 0) := by
  have ht :
      (∀ k : Fin 15, A3Sector.bracketInt 2 8 k =
        (if k = 12 then 1 else 0) + (if k = 13 then 1 else 0) +
          (if k = 14 then 1 else 0)) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 12 8 k + A3Sector.bracketInt 13 8 k +
        A3Sector.bracketInt 14 8 k = if k = 8 then -2 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 12 2 k + A3Sector.bracketInt 13 2 k +
        A3Sector.bracketInt 14 2 k = if k = 2 then 2 else 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 8 8 k = 0) ∧
      (∀ k : Fin 15, A3Sector.bracketInt 2 2 k = 0) := by decide +kernel
  unfold A3Sector.bracketTable
  exact_mod_cast ht

/-- The highest-root currents satisfy the rank-one current relations. -/
theorem coreHighest_currentRelations (Q : CurrentModule A3Sector.bracketTable V) :
    CVsl2.SL2 (Q.op 2) (coreHighestCartan Q) (Q.op 8) := by
  obtain ⟨hEF, hHF, hHE, hFF, hEE⟩ := coreHighest_rootTable
  refine ⟨fun r s => ?_, fun r s => ?_, fun r s => ?_,
    fun r s => ?_, fun r s => ?_⟩
  · rw [coreCurrent_commutator]
    simp [hEF, add_smul, Finset.sum_add_distrib, coreHighestCartan]
  · simp only [coreHighestCartan, add_mul, mul_add, add_sub_add_comm]
    rw [coreCurrent_commutator, coreCurrent_commutator, coreCurrent_commutator,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp_rw [← add_smul, hHF]
    simp [ite_smul]
  · simp only [coreHighestCartan, add_mul, mul_add, add_sub_add_comm]
    rw [coreCurrent_commutator, coreCurrent_commutator, coreCurrent_commutator,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp_rw [← add_smul, hHE]
    simp [ite_smul]
  · rw [← sub_eq_zero, coreCurrent_commutator]
    simp [hFF]
  · rw [← sub_eq_zero, coreCurrent_commutator]
    simp [hEE]

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreLowering_locally_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighest_lowering_nilpotent
#print axioms VOA.DeligneAudit.D4LevelReduction.coreCurrent_commutator
#print axioms VOA.DeligneAudit.D4LevelReduction.coreOuter_currentRelations
#print axioms VOA.DeligneAudit.D4LevelReduction.coreHighest_currentRelations
