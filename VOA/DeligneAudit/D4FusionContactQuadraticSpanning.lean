import VOA.DeligneAudit.D4FusionContactQuadraticTable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Nine quadratic normal columns from the checked relation rows

This is linear algebra over an arbitrary characteristic-zero field. The source
relations are explicit submodule-membership premises; no source finiteness or
rank hypothesis is used. The actual D₄ source bridge supplies those relations.
-/
namespace VOA.DeligneAudit.D4FusionContact.Quadratic

open scoped BigOperators

noncomputable section

variable {V : Type*} [AddCommGroup V]

/-- Evaluation of an integer coefficient vector in an additive group. -/
def evalZ (b : Fin 36 → V) : (Fin 36 → ℤ) →ₗ[ℤ] V where
  toFun c := ∑ j, c j • b j
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem evalZ_apply (b : Fin 36 → V) (c : Fin 36 → ℤ) :
    evalZ b c = ∑ j, c j • b j := rfl

theorem evalZ_basis (b : Fin 36 → V) (j : Fin 36) : evalZ b (basis j) = b j := by
  simp [evalZ, basis]

/-- The checked coefficient identity evaluates in every additive group. -/
theorem evaluate_elimination (b : Fin 36 → V) (j : Fin 36) :
    b j = (if isNormal j then 0 else evalZ b (normalized (pivotRow j))) +
      ∑ n : Fin 9, normalCoeff j n • b (normalColumn n) := by
  have he : basis j =
      (if isNormal j then (0 : Fin 36 → ℤ) else normalized (pivotRow j)) +
        ∑ n : Fin 9, normalCoeff j n • basis (normalColumn n) := by
    funext k
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ite_apply, Pi.zero_apply] using elimination j k
  have hh := congrArg (evalZ b) he
  simpa only [evalZ_basis, map_add, map_sum, map_smul, apply_ite, map_zero] using hh

variable {K : Type*} [Field K] [CharZero K] [Module K V]

/-- Actual raw-row relations modulo P imply the nine-column spanning bound
modulo P. The nonzero integer normalization factors are proved, not assumed. -/
theorem raw_rows_mem_implies_span (P : Submodule K V) (b : Fin 36 → V)
    (h : ∀ r : Fin 27, (∑ j : Fin 36, (raw r j : K) • b j) ∈ P) (j : Fin 36) :
    b j ∈ P ⊔ Submodule.span K (Set.range fun n : Fin 9 => b (normalColumn n)) := by
  have hn : ∀ r : Fin 27, evalZ b (normalized r) ∈ P := by
    intro r
    have hr : raw r = factor r • normalized r := by
      funext k
      simpa only [Pi.smul_apply, smul_eq_mul] using raw_eq_factor r k
    have he := congrArg (evalZ b) hr
    simp only [map_smul] at he
    have hc : (factor r : K) ≠ 0 := by exact_mod_cast factor_ne_zero r
    have hs : (factor r : K) • evalZ b (normalized r) ∈ P := by
      rw [Int.cast_smul_eq_zsmul, ← he]
      simpa only [evalZ_apply, Int.cast_smul_eq_zsmul] using h r
    have hi := P.smul_mem ((factor r : K)⁻¹) hs
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi
  rw [evaluate_elimination b j]
  apply Submodule.add_mem
  · split_ifs
    · exact Submodule.zero_mem _
    · exact Submodule.mem_sup_left (hn _)
  · apply Submodule.sum_mem
    intro n _
    apply Submodule.mem_sup_right
    have hm : b (normalColumn n) ∈
        Submodule.span K (Set.range fun n : Fin 9 => b (normalColumn n)) :=
      Submodule.subset_span ⟨n, rfl⟩
    simpa only [Int.cast_smul_eq_zsmul] using
      (Submodule.span K _).smul_mem (normalCoeff j n : K) hm

end
end VOA.DeligneAudit.D4FusionContact.Quadratic

#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.evaluate_elimination
#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.raw_rows_mem_implies_span
