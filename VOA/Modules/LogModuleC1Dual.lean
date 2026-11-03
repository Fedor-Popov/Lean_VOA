import VOA.Modules.LogModuleC1Parts
import VOA.Modules.LogTensorPzSimpleHomFinite
import VOA.Huang.HuangODEDual

/-! Actual generalized dual-C1 weight reduction.
The genuine contragredient's C1 cutoff gives a finite positive-mode reduction
for functionals on arbitrary generalized weight spaces. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor.ModuleC2
open VOA.C2Rigid VOA.LogTensor.Pz VOA.Classification.COne
open VOA.Huang.HuangODEDual
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Finite generation of an actual weak module gives finite length under C2. -/
theorem finiteLength_of_finGen (hC2 : C2Cofinite W) (B : WeakModule W M) (hgen : FinGen B) :
    IsFiniteLength (modeAlg B) M := by
  obtain ⟨S,hS,hgen⟩ := hgen
  let P := Submodule.span (modeAlg B) S
  have hPt : P.restrictScalars ℂ = ⊤ := hgen (P.restrictScalars ℂ)
    (fun _ hx => Submodule.subset_span hx) (fun a n x hx => (ofR B P).act_mem a n hx)
  have hP : P = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    have hx : x ∈ P.restrictScalars ℂ := hPt ▸ Submodule.mem_top
    exact hx
  have hfg : (⊤ : Submodule (modeAlg B) M).FG :=
    Submodule.fg_def.mpr ⟨S,hS,hP⟩
  exact Submodule.topEquiv.isFiniteLength
    (PlusFiniteLength.finiteLength_fg_of_c2Cofinite hC2 B ⊤ hfg)

/-- The genuine positive-mode span on a generalized weight space. -/
def dualC1Part (N : LogVModule W M) (α : ℂ) : Submodule ℂ (Module.Dual ℂ (N.weight α)) :=
  Submodule.span ℂ {φ | ∃ (d m : ℤ) (a : V) (g : M →ₗ[ℂ] ℂ),
    1 ≤ d ∧ 2*d ≤ m+1 ∧ a ∈ W.grading d ∧
      φ = (g ∘ₗ mode (N.YM a) m).domRestrict (N.weight α)}

/-- Every genuine summand of a contragredient C1 generator has the required
positive-mode shape on the original module. -/
theorem dualC1_term_mem (N : LogVModule W M) (α : ℂ) {d : ℤ} (hd : 1 ≤ d)
    {a : V} (ha : a ∈ W.grading d) (γ : ℂ) (g₀ : Module.Dual ℂ (N.weight γ))
    {j : ℕ} (hj : j ≤ d.toNat) :
    C2Rigid.restrictToWeight N.toGW α
      (LinearMap.lcomp ℂ ℂ (C2Rigid.dualTargetOp N.toGW d a (-1) γ j) g₀) ∈ dualC1Part N α := by
  obtain ⟨d,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ d by omega)
  have hd' : 1 ≤ d := by exact_mod_cast hd
  simp only [Int.toNat_natCast] at hj
  have hv := VertexOperatorAlgebra.L_one_pow_mem W ha j
  rcases lt_or_eq_of_le hj with hjd | rfl
  · refine Submodule.subset_span ⟨(d : ℤ)-j,2*(d : ℤ)-1-j,(W.L 1 ^ j) a,
      g₀ ∘ₗ internalProjTo N.isInternal γ,by omega,by omega,hv,?_⟩
    ext x
    simp only [C2Rigid.restrictToWeight,LinearMap.lcomp_apply,LinearMap.comp_apply,
      LinearMap.domRestrict_apply,Submodule.subtype_apply,C2Rigid.dualTargetOp,modeLinear,
      LinearMap.coe_mk,AddHom.coe_mk]
    have hi : 2*(d : ℤ)-(-1)-2-(j : ℤ) = 2*(d : ℤ)-1-j := by ring
    rw [hi]
    rfl
  · have h0 : (W.L 1 ^ j) a ∈ W.grading 0 := by simpa using hv
    rw [W.vacuum_grade,Submodule.mem_span_singleton] at h0
    obtain ⟨c,hc⟩ := h0
    have hz : C2Rigid.restrictToWeight N.toGW α
        (LinearMap.lcomp ℂ ℂ (C2Rigid.dualTargetOp N.toGW (j : ℤ) a (-1) γ j) g₀) = 0 := by
      ext x
      simp only [C2Rigid.restrictToWeight,LinearMap.lcomp_apply,LinearMap.comp_apply,
        LinearMap.domRestrict_apply,Submodule.subtype_apply,C2Rigid.dualTargetOp,modeLinear,
        LinearMap.coe_mk,AddHom.coe_mk,LinearMap.zero_apply]
      rw [← hc,map_smul,N.toGW.vacuum_YM,mode_smul,mode_one,if_neg (by omega)]
      simp
    rw [hz]
    exact Submodule.zero_mem _

/-- Component extraction sends the actual contragredient's homogeneous C1
part into the genuine positive-mode functional span. -/
theorem component_mem_dualC1 (N : LogVModule W M) (α : ℂ)
    {φ : C2Rigid.RestrictedDual N.toGW} (hφ : φ ∈ c1Part (contraLog N) α) :
    DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α φ ∈ dualC1Part N α := by
  let R := DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α
  change R φ ∈ dualC1Part N α
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨d,a,g',hd,ha,hg',rfl⟩ := hφ
    change g' ∈ LinearMap.range
      (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) (α-(d : ℂ))) at hg'
    obtain ⟨g₀,rfl⟩ := hg'
    change R (mode (C2Rigid.YMdual N.toGW a) (-1) _) ∈ dualC1Part N α
    rw [C2Rigid.mode_YMdual_homogeneous N.toGW ha (-1)]
    erw [C2Rigid.dualModeEndo_lof]
    have hi : C2Rigid.dualOutIdx d (-1) (α-(d : ℂ)) = α := by
      simp only [C2Rigid.dualOutIdx]; push_cast; ring
    rw [hi]
    change DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α
      (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α
        (C2Rigid.restrictToWeight N.toGW α (C2Rigid.dualCompMap N.toGW d a (-1) (α-d) g₀))) ∈ _
    rw [DirectSum.component.lof_self]
    simp only [C2Rigid.dualCompMap,LinearMap.smul_apply,LinearMap.coeFn_sum,Finset.sum_apply,
      map_smul,map_sum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    simp only [Finset.mem_range] at hj
    exact dualC1_term_mem N α hd ha _ g₀ (by omega)
  | zero => erw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => erw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => erw [map_smul]; exact Submodule.smul_mem _ c hx

/-- C2 and actual finite generation discharge the generalized dual-C1 cutoff. -/
theorem dualC1_generalized_cutoff (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) :
    ∃ b : ℝ, ∀ α : ℂ, b < α.re → ∀ f : M →ₗ[ℂ] ℂ,
      f.domRestrict (N.weight α) ∈ dualC1Part N α := by
  have hdual := finGen_contraLog_of_finiteLength N (finiteLength_of_finGen hC2 N.toWeakModule hfg)
  obtain ⟨b,hb⟩ := c1Part_generalized_cutoff hC2 (contraLog N) hdual
  refine ⟨b,fun α hα f => ?_⟩
  let φ := DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α
    (f.domRestrict (N.weight α))
  have hφ : φ ∈ (contraLog N).weight α := ⟨_,rfl⟩
  have hc := component_mem_dualC1 N α (hb α hα hφ)
  simpa only [φ,DirectSum.component.lof_self] using hc

end VOA.LogTensor.ModuleC2
