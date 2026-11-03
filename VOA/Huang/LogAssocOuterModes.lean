import VOA.Huang.LogAssocOuterEvaluation

/-! Actual outer zeroth-mode reconstruction from homogeneous outside blocks.
Its weight law and lower truncation follow from the genuine target grading;
Jacobi and the coupled derivative remain separate identities to prove. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficients
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficientCompatibility
open Module (Dual)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {R M₃ M₄ : Type u}
  [AddCommGroup R] [Module ℂ R] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄]
variable (N : LogVModule W R) (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄)
variable (A : ∀ β γ c : ℂ,Dual ℂ (N₄.weight β) →ₗ[ℂ] N₃.weight c →ₗ[ℂ] R)

/-- An outer mode has an actual vector in the stated target generalized weight. -/
noncomputable def outerModeBlock (n γ c : ℂ) :
    (contraLog N).weight γ →ₗ[ℂ] N₃.weight c →ₗ[ℂ] M₄ :=
  LinearMap.mk₂ ℂ
    (fun ξ z => (outerEvaluationBlock N N₃ N₄ (γ+c-n-1) c (A (γ+c-n-1) γ c) ξ z : M₄))
    (fun ξ η z => by
      dsimp only
      simp only [Submodule.coe_add,map_add,LinearMap.add_apply])
    (fun s ξ z => by
      dsimp only
      simp only [Submodule.coe_smul,map_smul,LinearMap.smul_apply])
    (fun ξ z z' => by
      dsimp only
      simp only [map_add,Submodule.coe_add])
    (fun s ξ z => by
      dsimp only
      simp only [map_smul,Submodule.coe_smul])

/-- Actual homogeneous pieces assemble the genuine outer zeroth-mode family. -/
noncomputable def outerModes (n : ℂ) :
    C2Rigid.RestrictedDual N.toGW →ₗ[ℂ] M₃ →ₗ[ℂ] M₄ :=
  fromBlocks (contraLog N) N₃ (outerModeBlock N N₃ N₄ A n)

theorem outerModes_homogeneous (n : ℂ) {γ c : ℂ}
    {ξ : C2Rigid.RestrictedDual N.toGW} {z : M₃}
    (hξ : ξ∈(contraLog N).weight γ) (hz : z∈N₃.weight c) :
    outerModes N N₃ N₄ A n ξ z=
      (outerEvaluationBlock N N₃ N₄ (γ+c-n-1) c (A (γ+c-n-1) γ c) ξ ⟨z,hz⟩ : M₄) := by
  rw [outerModes,fromBlocks_homogeneous (contraLog N) N₃ _ hξ hz]
  rfl

/-- This actual weight law uses the full generalized modules. -/
theorem outerModes_weight (n : ℂ) :
    HasModeWeight (contraLog N) N₃ N₄ n (outerModes N N₃ N₄ A n) := by
  intro γ c ξ z hξ hz
  rw [outerModes_homogeneous N N₃ N₄ A n hξ hz]
  exact (outerEvaluationBlock N N₃ N₄ (γ+c-n-1) c (A (γ+c-n-1) γ c) ξ ⟨z,hz⟩).2

/-- Actual homogeneous outer values are lower truncated solely by the genuine
output module lower bound, with no semisimple premise. -/
theorem outerModes_truncated_homogeneous {γ c : ℂ}
    {ξ : C2Rigid.RestrictedDual N.toGW} {z : M₃}
    (hξ : ξ∈(contraLog N).weight γ) (hz : z∈N₃.weight c) (n : ℂ) :
    ∃ K : ℤ,∀ j : ℤ,K≤j → outerModes N N₃ N₄ A (n+j) ξ z=0 := by
  obtain ⟨B,hB⟩ := N₄.boundedBelow
  let K : ℤ := ⌈(γ+c-n-1).re-B⌉
  have hK : (γ+c-n-1).re-B≤(K : ℝ) := Int.le_ceil _
  refine ⟨K+1,fun j hj => ?_⟩
  have hm := outerModes_weight N N₃ N₄ A (n+j) hξ hz
  have hbot : N₄.weight (γ+c-(n+j)-1)=⊥ := by
    by_contra h
    have hb := hB _ h
    have hj' : ((K+1 : ℤ) : ℝ)≤(j : ℝ) := by exact_mod_cast hj
    simp only [Complex.sub_re,Complex.add_re,Complex.intCast_re,Complex.one_re] at hb hK
    push_cast at hj'
    linarith
  simpa only [hbot,Submodule.mem_bot] using hm

/-- Finite genuine generalized homogeneous decompositions give lower truncation
on arbitrary outside vectors. -/
theorem outerModes_truncated (ξ : C2Rigid.RestrictedDual N.toGW) (z : M₃) (n : ℂ) :
    ∃ K : ℤ,∀ j : ℤ,K≤j → outerModes N N₃ N₄ A (n+j) ξ z=0 := by
  refine LogFin.induction_on (contraLog N)
    (C := fun ξ => ∃ K : ℤ,∀ j : ℤ,K≤j → outerModes N N₃ N₄ A (n+j) ξ z=0)
    ξ ?_ ⟨0,fun _ _ => by simp⟩ ?_
  · intro γ ξ hξ
    refine LogFin.induction_on N₃
      (C := fun z => ∃ K : ℤ,∀ j : ℤ,K≤j → outerModes N N₃ N₄ A (n+j) ξ z=0)
      z (fun c z hz => outerModes_truncated_homogeneous N N₃ N₄ A hξ hz n)
      ⟨0,fun _ _ => by simp⟩ ?_
    rintro z z' ⟨K,hK⟩ ⟨L,hL⟩
    exact ⟨max K L,fun j hj => by
      rw [map_add,hK j (le_trans (le_max_left _ _) hj),hL j (le_trans (le_max_right _ _) hj),add_zero]⟩
  · rintro ξ η ⟨K,hK⟩ ⟨L,hL⟩
    exact ⟨max K L,fun j hj => by
      rw [map_add,LinearMap.add_apply,hK j (le_trans (le_max_left _ _) hj),
        hL j (le_trans (le_max_right _ _) hj),add_zero]⟩

/-- The literal paired value of the recovered mode, including all foreign
output-weight vanishing. -/
theorem outerModes_pair (n : ℂ) {γ c β : ℂ}
    {ξ : C2Rigid.RestrictedDual N.toGW} {z : M₃}
    (hξ : ξ∈(contraLog N).weight γ) (hz : z∈N₃.weight c)
    (f : Dual ℂ M₄) (hf : SupportedAt N₄ f β) :
    f (outerModes N N₃ N₄ A n ξ z)=
      if β=γ+c-n-1 then
        C2Rigid.dualPairing N.toGW (A β γ c (f.domRestrict (N₄.weight β)) ⟨z,hz⟩) ξ else 0 := by
  rw [outerModes_homogeneous N N₃ N₄ A n hξ hz]
  split_ifs with h
  · subst β
    exact outerEvaluationBlock_supported_pair N N₃ N₄ _ c _ ξ ⟨z,hz⟩ f
  · exact hf (γ+c-n-1) (Ne.symm h) _
      (outerEvaluationBlock N N₃ N₄ (γ+c-n-1) c (A (γ+c-n-1) γ c) ξ ⟨z,hz⟩).2

end VOA.Huang.LogAssocCoefficients
