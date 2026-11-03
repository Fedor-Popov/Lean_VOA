import VOA.Modules.LogModuleC1Graded

/-! The genuine homogeneous C1 weight reduction for logarithmic modules.
Above a real cutoff, vectors are sums of positive homogeneous states acting
at mode -1 on vectors of strictly lower generalized weight. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.ModuleC2
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The actual generalized-weight alpha part of Huang's C1 subspace. -/
def c1Part (N : LogVModule W M) (α : ℂ) : Submodule ℂ M :=
  Submodule.span ℂ {x | ∃ (d : ℤ) (a : V) (m : M),
    1 ≤ d ∧ a ∈ W.grading d ∧ m ∈ N.weight (α-(d : ℂ)) ∧
      x = N.toWeakModule.act a (-1) m}

/-- Homogeneous C1 generators lie in the actual C1 subspace. -/
theorem c1Part_le_C1 (N : LogVModule W M) (α : ℂ) :
    c1Part N α ≤ C1M N.toWeakModule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d,a,m,hd,ha,hm,rfl⟩
  exact Submodule.subset_span ⟨d,a,m,hd,ha,rfl⟩

/-- Each generator has precisely the requested genuine generalized weight. -/
theorem c1Part_le_weight (N : LogVModule W M) (α : ℂ) :
    c1Part N α ≤ N.weight α := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d,a,m,hd,ha,hm,rfl⟩
  have h := N.mode_mem_weight ha hm (-1)
  convert h using 1
  congr 1
  push_cast
  ring

/-- Projecting C1 onto alpha gives its actual homogeneous generating span. -/
theorem weightProj_mem_c1Part (N : LogVModule W M) (α : ℂ) {x : M}
    (hx : x ∈ C1M N.toWeakModule) : weightProj N α x ∈ c1Part N α := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d,a,m,hd,ha,rfl⟩ := hx
    obtain ⟨s,-,hs⟩ := C2Rigid.exists_sum_cmp N.toGW m
    change weightProj N α (mode (N.YM a) (-1) m) ∈ c1Part N α
    rw [← hs,map_sum,map_sum]
    apply Submodule.sum_mem
    intro β _
    have hm := N.mode_mem_weight ha (C2Rigid.cmp_mem N.toGW β m) (-1)
    by_cases he : β+(d : ℂ)-(-1 : ℤ)-1=α
    · rw [weightProj_of_mem N (he ▸ hm)]
      have hb : β=α-(d : ℂ) := by push_cast at he; linear_combination he
      exact Submodule.subset_span ⟨d,a,C2Rigid.cmp N.toGW β m,hd,ha,
        hb ▸ C2Rigid.cmp_mem N.toGW β m,rfl⟩
    · rw [weightProj_of_mem_ne N hm he]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- The homogeneous C1 part is exactly the intersection with generalized weight. -/
theorem c1Part_eq_inf (N : LogVModule W M) (α : ℂ) :
    c1Part N α = C1M N.toWeakModule ⊓ N.weight α := by
  apply le_antisymm
  · exact le_inf (c1Part_le_C1 N α) (c1Part_le_weight N α)
  · intro x hx
    rw [← weightProj_of_mem N hx.2]
    exact weightProj_mem_c1Part N α hx.1

/-- Actual finite generation and C2-cofiniteness discharge homogeneous C1 reduction. -/
theorem c1Part_generalized_cutoff (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) :
    ∃ b : ℝ, ∀ α : ℂ, b < α.re → N.weight α ≤ c1Part N α := by
  obtain ⟨b,hb⟩ := C1_generalized_weight_cutoff hC2 N hfg
  refine ⟨b,fun α hα x hx => ?_⟩
  rw [← weightProj_of_mem N hx]
  exact weightProj_mem_c1Part N α (hb α hα hx)

end VOA.LogTensor.ModuleC2
