import VOA.Moonshine.MoonshineCNTrace
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Finite-order traces are bounded by dimension, without a choice of invariant metric. -/

namespace VOA.Moonshine.ConwayNorton

open AutMonster

/-- Every eigenvalue of a finite-order complex operator has norm one. The trace
bound follows by summing the roots of its characteristic polynomial. -/
theorem finiteOrderTrace_norm_le {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (f : Module.End ℂ M) (hf : IsOfFinOrder f) :
    ‖LinearMap.trace ℂ M f‖ ≤ Module.finrank ℂ M := by
  classical
  obtain ⟨N, hN, hfN⟩ := isOfFinOrder_iff_pow_eq_one.mp hf
  have hroot : ∀ z ∈ f.charpoly.roots, ‖z‖ ≤ (1 : ℝ) := by
    intro z hz
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly f z).mpr
      ((Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).mp hz)
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hvN := hv.pow_apply N
    rw [hfN, Module.End.one_apply] at hvN
    have hzN : z ^ N = 1 := by
      apply (smul_left_injective ℂ hv.2)
      simpa only [one_smul] using hvN.symm
    exact le_of_eq (Complex.norm_eq_one_of_pow_eq_one hzN hN.ne')
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  calc
    ‖f.charpoly.roots.sum‖ ≤ (f.charpoly.roots.map norm).sum := norm_multiset_sum_le _
    _ ≤ (f.charpoly.roots.card : ℝ) := by
      simpa using Multiset.sum_le_card_nsmul (f.charpoly.roots.map norm) (1 : ℝ)
        (by simpa only [Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
              using hroot)
    _ ≤ Module.finrank ℂ M := by
      exact_mod_cast (f.charpoly.card_roots'.trans_eq (LinearMap.charpoly_natDegree f))

/-- The trace bound applies on each finite-dimensional homogeneous piece. -/
theorem gradedAutTrace_norm_le {M : Type*} [AddCommGroup M] [Module ℂ M]
    (V : VertexOperatorAlgebra M) (g : Aut V) (hg : IsOfFinOrder g) (n : ℤ) :
    ‖gradedAutTrace V g n‖ ≤ Module.finrank ℂ (V.grading n) := by
  letI := V.finrank n
  exact finiteOrderTrace_norm_le _ ((gradedAutAction V n).isOfFinOrder hg)

/-- Every finite-order McKay–Thompson coefficient is dominated by the identity coefficient. -/
theorem mckayThompson_coeff_norm_le (g : AutVnat) (hg : IsOfFinOrder g) (n : ℕ) :
    ‖PowerSeries.coeff n (mckayThompson g)‖ ≤
      ‖PowerSeries.coeff n (mckayThompson 1)‖ := by
  rw [mckayThompson_coeff, mckayThompson_coeff, gradedAutTrace_one]
  simpa using gradedAutTrace_norm_le VnatVOA g hg ((n : ℤ) + 1)

end VOA.Moonshine.ConwayNorton
