import VOA.Modules.LogModuleC2FiniteLength

/-! # Actual C₁-cofiniteness for generalized finite-length modules

The module C₂ subspace lies in Huang's C₁ subspace by translation covariance.
Thus every finite-length or finitely generated weak module over a C₂-cofinite
VOA is C₁-cofinite with its actual action, including logarithmic modules.
-/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.ModuleC2
open VOA.Huang.FusionC2
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Huang's actual C₁ subspace, spanned by positive-weight states acting at mode -1. -/
def C1M (B : WeakModule W M) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ (d : ℤ) (a : V) (m : M),
    1 ≤ d ∧ a ∈ W.grading d ∧ x = B.act a (-1) m}

theorem C2M_le_C1M (B : WeakModule W M) : C2M B ≤ C1M B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,m,rfl⟩
  refine induction_grading (W := W)
    (motive := fun a => mode (B.YM a) (-2) m ∈ C1M B) a
    (by simp) (fun a b ha hb => ?_) (fun p a ha => ?_)
  · simp only [map_add,mode_add,LinearMap.add_apply]
    exact Submodule.add_mem _ ha hb
  · rcases lt_or_ge p 0 with hp | hp
    · rw [W.positivity p hp,Submodule.mem_bot] at ha
      rw [ha,map_zero,mode_zero,LinearMap.zero_apply]
      exact Submodule.zero_mem _
    · have hcov := act_T_covariance B a (-1) m
      simp only [WeakModule.act_def,Int.cast_neg,Int.cast_one,neg_neg,one_smul,
        show (-1 : ℤ)-1 = -2 by norm_num] at hcov
      rw [← hcov]
      exact Submodule.subset_span ⟨p+1,W.L (-1) a,m,by omega,
        VertexOperatorAlgebra.L_neg_one_raise W ha,rfl⟩

theorem C1_cofinite_of_C2 (B : WeakModule W M) (hB : ModuleC2Cofinite B) :
    FiniteDimensional ℂ (M ⧸ C1M B) := by
  haveI : FiniteDimensional ℂ (M ⧸ C2M B) := hB
  exact Module.Finite.of_surjective (Submodule.factor (C2M_le_C1M B))
    (Submodule.factor_surjective (C2M_le_C1M B))

/-- C₁-cofiniteness of every genuine finite-length weak module, with no rationality premise. -/
theorem C1_cofinite_of_finiteLength (hC2 : C2Cofinite W) (B : WeakModule W M)
    (hfl : IsFiniteLength (VOA.Classification.COne.modeAlg B) M) :
    FiniteDimensional ℂ (M ⧸ C1M B) :=
  C1_cofinite_of_C2 B (cofinite_of_finiteLength hC2 B hfl)

/-- In particular, every finitely generated logarithmic module is C₁-cofinite. -/
theorem C1_cofinite_of_finGen (hC2 : C2Cofinite W) (B : WeakModule W M) (hfg : FinGen B) :
    FiniteDimensional ℂ (M ⧸ C1M B) :=
  C1_cofinite_of_C2 B (cofinite_of_finGen hC2 B hfg)

end VOA.LogTensor.ModuleC2
