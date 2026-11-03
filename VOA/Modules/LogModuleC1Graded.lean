import VOA.Modules.LogModuleC1Cofinite
import VOA.Modules.LogTensorContraCoordinates
import VOA.Classification.COne.McRaeM2Perp

/-! # A genuine generalized-weight cutoff for logarithmic C₁-cofiniteness

The actual generalized-weight projections preserve C₁. Their images in the
finite-dimensional C₁ quotient are independent, so only finitely many survive.
This gives a real upper weight bound without assuming semisimple L(0) or a
single conformal-weight coset.
-/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.ModuleC2
open Module (End)
open scoped BigOperators
noncomputable section
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The actual projection onto one generalized weight space. -/
def weightProj (N : LogVModule W M) (α : ℂ) : End ℂ M where
  toFun := C2Rigid.cmp N.toGW α
  map_add' := C2Rigid.cmp_add N.toGW α
  map_smul' := C2Rigid.cmp_smul N.toGW α

theorem weightProj_of_mem (N : LogVModule W M) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : weightProj N α x = x := C2Rigid.cmp_of_mem N.toGW hx

theorem weightProj_of_mem_ne (N : LogVModule W M) {α β : ℂ} {x : M}
    (hx : x ∈ N.weight β) (hne : β ≠ α) : weightProj N α x = 0 :=
  C2Rigid.cmp_of_mem_ne N.toGW hx hne

/-- The projections of the actual generalized grading preserve Huang's C₁ subspace. -/
theorem weightProj_mem_C1 (N : LogVModule W M) (α : ℂ) {x : M}
    (hx : x ∈ C1M N.toWeakModule) : weightProj N α x ∈ C1M N.toWeakModule := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d,a,m,hd,ha,rfl⟩ := hx
    obtain ⟨s,-,hs⟩ := C2Rigid.exists_sum_cmp N.toGW m
    change weightProj N α (mode (N.YM a) (-1) m) ∈ C1M N.toWeakModule
    rw [← hs,map_sum,map_sum]
    apply Submodule.sum_mem
    intro β _
    have hm := N.mode_mem_weight ha (C2Rigid.cmp_mem N.toGW β m) (-1)
    by_cases he : β + (d : ℂ) - (-1 : ℤ) - 1 = α
    · rw [weightProj_of_mem N (he ▸ hm)]
      exact Submodule.subset_span ⟨d,a,C2Rigid.cmp N.toGW β m,hd,ha,rfl⟩
    · rw [weightProj_of_mem_ne N hm he]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- Only finitely many generalized weights survive in the genuine C₁ quotient. -/
theorem exists_finite_C1_weights (N : LogVModule W M)
    (hfd : FiniteDimensional ℂ (M ⧸ C1M N.toWeakModule)) :
    ∃ F : Finset ℂ, ∀ α ∉ F, N.weight α ≤ C1M N.toWeakModule := by
  classical
  let C := C1M N.toWeakModule
  haveI : FiniteDimensional ℂ (M ⧸ C) := hfd
  let E : ℂ → Submodule ℂ (M ⧸ C) := fun α => (N.weight α).map C.mkQ
  have hind : iSupIndep E := by
    rw [iSupIndep_def]
    intro α
    rw [Submodule.disjoint_def]
    intro q hq hq'
    obtain ⟨x,hx,rfl⟩ := Submodule.mem_map.mp hq
    have hq'' : C.mkQ x ∈ (⨆ (β : ℂ) (_ : β ≠ α), N.weight β).map C.mkQ := by
      rw [Submodule.map_iSup]
      simpa only [Submodule.map_iSup,E] using hq'
    obtain ⟨y,hy,hxy⟩ := Submodule.mem_map.mp hq''
    have hdiff : y-x ∈ C := by
      apply (Submodule.Quotient.mk_eq_zero C).mp
      rw [Submodule.Quotient.mk_sub]
      change C.mkQ y-C.mkQ x = 0
      rw [hxy,sub_self]
    have hy0 : weightProj N α y = 0 := by
      refine Submodule.iSup_induction _ hy
        (motive := fun y => weightProj N α y = 0) ?_ (map_zero _) ?_
      · intro β z hz
        refine Submodule.iSup_induction _ hz
          (motive := fun z => weightProj N α z = 0) ?_ (map_zero _) ?_
        · intro hne z hz
          exact weightProj_of_mem_ne N hz hne
        · intro z w hz hw
          beta_reduce at hz hw ⊢
          rw [map_add,hz,hw,add_zero]
      · intro z w hz hw
        beta_reduce at hz hw ⊢
        rw [map_add,hz,hw,add_zero]
    have hxC : x ∈ C := by
      have h1 := weightProj_mem_C1 N α hdiff
      rw [map_sub,hy0,zero_sub,weightProj_of_mem N hx] at h1
      simpa using C.neg_mem h1
    exact (Submodule.Quotient.mk_eq_zero C).mpr hxC
  letI := hind.fintypeNeBotOfFiniteDimensional
  let F : Finset ℂ := Finset.univ.image (fun i : {α // E α ≠ ⊥} => (i : ℂ))
  refine ⟨F,?_⟩
  intro α hα x hx
  have hE : E α = ⊥ := by
    by_contra hne
    exact hα (Finset.mem_image.mpr ⟨⟨α,hne⟩,Finset.mem_univ _,rfl⟩)
  have hq : C.mkQ x ∈ E α := Submodule.mem_map_of_mem hx
  rw [hE,Submodule.mem_bot,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero] at hq
  exact hq

/-- A real upper cutoff in every genuine finitely generated logarithmic module. -/
theorem C1_generalized_weight_cutoff (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) :
    ∃ b : ℝ, ∀ α : ℂ, b < α.re → N.weight α ≤ C1M N.toWeakModule := by
  obtain ⟨F,hF⟩ := exists_finite_C1_weights N (C1_cofinite_of_finGen hC2 N.toWeakModule hfg)
  obtain ⟨b,hb⟩ := (F.finite_toSet.image Complex.re).bddAbove
  refine ⟨b,fun α hα => hF α ?_⟩
  intro hmem
  exact (not_le_of_gt hα) (hb ⟨α,hmem,rfl⟩)

end
end VOA.LogTensor.ModuleC2
