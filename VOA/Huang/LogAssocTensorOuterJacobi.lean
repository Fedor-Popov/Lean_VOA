import VOA.Huang.LogAssocTensorOuterJacobiSpan
import VOA.Modules.LogTensorArInjective

/-! Literal outer modes on the actual logarithmic tensor object, obtained
from the actual collision coefficient inclusion in its tensor dual. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorOuterModes
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocCoefficientCoproduct VOA.C2Rigid VOA.C2Rigid.LocalInjective
open VOA.Classification.COne
open Module (Dual)
open VOA.Huang.PzTensorRho VOA.Huang.PzTensorOutside
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅




/-- Supported actual homogeneous dual functionals separate all vectors. -/
theorem eq_zero_of_supported_log {v : M₄}
    (h : ∀ β : ℂ,∀ f : M₄ →ₗ[ℂ] ℂ,SupportedAt N₄ f β → f v=0) : v=0 := by
  apply Ar.eq_zero_of_pairing_log N₄
  intro r
  refine LogFin.induction_on (contraLog N₄)
    (C := fun r => C2Rigid.dualPairing N₄.toGW v r=0) r ?_ ?_ ?_
  · intro β r hr
    exact h β (C2Rigid.dualPairingFlip N₄.toGW r) (restrictedDual_supportedAt N₄ r hr)
  · exact map_zero (C2Rigid.dualPairing N₄.toGW v)
  · intro r s hr hs
    rw [map_add,hr,hs,add_zero]

set_option maxHeartbeats 2000000 in
/-- Full genuine outer zeroth-mode Jacobi on true generalized homogeneous
inputs, obtained from the actual outside coefficient Borcherds identity. -/
theorem tensorOuterModes_jacobi_homogeneous {d : ℤ} {u : V} (hu : u∈W.grading d)
    {γ c : ℂ} {ξ : C2Rigid.RestrictedDual (tensorDual hC2 N₁ N₂ hfg₁ hfg₂).toGW} {z : M₃}
    (hξ : ξ∈(tensorModule hC2 N₁ N₂ hfg₁ hfg₂).weight γ) (hz : z∈N₃.weight c)
    (ell m : ℤ) (n : ℂ) :
    (∑ᶠ i : ℤ,IsLogIntertwining.jacL N₃.toWeakModule N₄.toWeakModule
      (liftModes (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂))
      u ξ z ell m n 0 i)=
    ∑ᶠ i : ℤ,IsLogIntertwining.jacR (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule
      (liftModes (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂))
      u ξ z ell m n 0 i := by
  let N := tensorDual hC2 N₁ N₂ hfg₁ hfg₂
  let F := tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  let Y := liftModes F
  let χ := (coefficientSpanToTensorDualHom hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).toLinearMap
  have htr : ∀ ξ z n,∃ K : ℤ,∀ j : ℤ,K ≤ j → ∀ k : ℕ,Y (n+j) k ξ z=0 := by
    intro ξ z n
    obtain ⟨K,hK⟩ := tensorOuterModes_truncated hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ ξ z n
    exact ⟨K,fun j hj _ => hK j hj⟩
  have hfinL := IsLogIntertwining.jacL_support_finite (A₂ := N₃.toWeakModule)
    (A₃ := N₄.toWeakModule) htr u ξ z ell m n 0
  have hfinR := IsLogIntertwining.jacR_support_finite (A₁ := (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule)
    Y u ξ z ell m n 0
  rw [← sub_eq_zero]
  apply eq_zero_of_supported_log hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
  intro β f hf
  rw [map_sub,map_finsum f hfinL,map_finsum f hfinR]
  let Λ : coefficientSpan hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ →ₗ[ℂ] ℂ :=
    (C2Rigid.dualPairingFlip N.toGW ξ).comp χ
  let X := outsideCoeffX hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz hu
  let B := outsideCoeffY hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz hu
  let Z := outsideCoeffZ hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz hu
  let β₀ := γ+c+d-ell-m-n-2
  have hT (i : ℤ) : f (IsLogIntertwining.jacL N₃.toWeakModule N₄.toWeakModule Y u ξ z ell m n 0 i)=
      if β=β₀ then (negOnePow i*cbz ell i)*(Λ (X (ell+m-i))-negOnePow ell*Λ (B (m+i))) else 0 := by
    simp only [IsLogIntertwining.jacL,Y,liftModes,map_smul,map_sub,smul_eq_mul]
    rw [show f (mode (N₄.YM u) (ell+m-i) (F (n+i) ξ z))=
      (f ∘ₗ mode (N₄.YM u) (ell+m-i)) (F (n+i) ξ z) by rfl]
    rw [tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (n+i) hξ hz _ (supportedAt_comp_mode hf hu (ell+m-i)),
      tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (ell+n-i) hξ (N₃.mode_mem_weight hu hz (m+i)) f hf]
    have c1 : (β-d+((ell+m-i : ℤ) : ℂ)+1=γ+c-(n+i)-1) ↔ β=β₀ := by
      dsimp [β₀]
      push_cast
      constructor <;> intro h <;> linear_combination h
    have c2 : (β=γ+(c+d-((m+i : ℤ) : ℂ)-1)-(ell+n-i)-1) ↔ β=β₀ := by
      dsimp [β₀]
      push_cast
      constructor <;> intro h <;> linear_combination h
    by_cases h : β=β₀
    · rw [if_pos (c1.mpr h),if_pos (c2.mpr h),if_pos h]
      rfl
    · rw [if_neg (fun h' => h (c1.mp h')),if_neg (fun h' => h (c2.mp h')),if_neg h]
      ring
  have hR (i : ℤ) : f (IsLogIntertwining.jacR (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule
      Y u ξ z ell m n 0 i)=if β=β₀ then cbz m i*Λ (Z (ell+i)) else 0 := by
    simp only [IsLogIntertwining.jacR,Y,liftModes,map_smul,smul_eq_mul]
    rw [tensorOuterModes_pair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (m+n-i) ((tensorModule hC2 N₁ N₂ hfg₁ hfg₂).mode_mem_weight hu hξ (ell+i)) hz f hf]
    have c3 : (β=γ+d-((ell+i : ℤ) : ℂ)-1+c-(m+n-i)-1) ↔ β=β₀ := by
      dsimp [β₀]
      push_cast
      constructor <;> intro h <;> linear_combination h
    by_cases h : β=β₀
    · rw [if_pos (c3.mpr h),if_pos h]
      have hp := pair_tensor_mode_coefficient hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu (ell+i)
        ⟨coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f z c β (γ+d-((ell+i : ℤ) : ℂ)-1) 0,
          coefficient_mem_span hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
            Y₁ Y₂ f z c β (γ+d-((ell+i : ℤ) : ℂ)-1) 0 hf hz⟩ ξ
      exact congrArg (fun q : ℂ => cbz m i*q) hp
    · rw [if_neg (fun h' => h (c3.mp h')),if_neg h,mul_zero]
  rw [finsum_congr hT,finsum_congr hR]
  by_cases h : β=β₀
  · simp only [if_pos h]
    obtain ⟨⟨QX,hX⟩,⟨QY,hB⟩,⟨QZ,hZ⟩⟩ := outsideCoeff_bounds hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz hu
    have hFX : Function.HasFiniteSupport (fun i : ℤ => (negOnePow i*cbz ell i) • X (ell+m-i)) :=
      hfs_of _ 0 (max 0 (ell+m-QX)) (fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_apply_neg _ hi,mul_zero,zero_smul]
        · rw [show X (ell+m-i)=0 from hX _ (by omega),smul_zero])
    have hFB : Function.HasFiniteSupport (fun i : ℤ => (negOnePow i*cbz ell i) • B (m+i)) :=
      hfs_of _ 0 (max 0 (QY-m)) (fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_apply_neg _ hi,mul_zero,zero_smul]
        · rw [show B (m+i)=0 from hB _ (by omega),smul_zero])
    have hFZ : Function.HasFiniteSupport (fun i : ℤ => cbz m i • Z (ell+i)) :=
      hfs_of _ 0 (max 0 (QZ-ell)) (fun i hi => by
        rcases hi with hi | hi
        · rw [cbz_apply_neg _ hi,zero_smul]
        · rw [show Z (ell+i)=0 from hZ _ (by omega),smul_zero])
    have hSX : Function.HasFiniteSupport (fun i : ℤ => (negOnePow i*cbz ell i)*Λ (X (ell+m-i))) := by
      refine hFX.subset ?_
      intro i hi
      rw [Function.mem_support] at hi ⊢
      intro hz
      apply hi
      have he := congrArg Λ hz
      simpa only [map_smul,smul_eq_mul,map_zero] using he
    have hSB : Function.HasFiniteSupport (fun i : ℤ => (negOnePow i*cbz ell i)*(negOnePow ell*Λ (B (m+i)))) := by
      refine hFB.subset ?_
      intro i hi
      rw [Function.mem_support] at hi ⊢
      intro hz
      apply hi
      have he := congrArg Λ hz
      rw [map_smul,map_zero,smul_eq_mul] at he
      rw [mul_left_comm,he,mul_zero]
    have he := congrArg Λ (outsideCoeff_borcherds hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ 0 hf hz hu ell m)
    change Λ ((∑ᶠ i : ℤ,(negOnePow i*cbz ell i) • X (ell+m-i))
      -negOnePow ell • (∑ᶠ i : ℤ,(negOnePow i*cbz ell i) • B (m+i))
      -(∑ᶠ i : ℤ,cbz m i • Z (ell+i)))=Λ 0 at he
    rw [map_sub,map_sub,map_smul,map_finsum Λ hFX,map_finsum Λ hFB,map_finsum Λ hFZ,map_zero] at he
    simp only [map_smul,smul_eq_mul] at he
    rw [finsum_congr (fun i => mul_sub (negOnePow i*cbz ell i) _ _),finsum_sub_distrib hSX hSB]
    have eB : (∑ᶠ i : ℤ,(negOnePow i*cbz ell i)*(negOnePow ell*Λ (B (m+i))))=
        negOnePow ell*(∑ᶠ i : ℤ,(negOnePow i*cbz ell i)*Λ (B (m+i))) := by
      rw [mul_finsum]
      apply finsum_congr
      intro i
      ring
    rw [eB]
    exact he
  · simp only [if_neg h,finsum_zero,sub_self]

/-- Every literal tensor outer zeroth mode has genuine full Jacobi. -/
theorem tensorOuterModes_isJacobi :
    IsJacobiFamily (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule N₃.toWeakModule N₄.toWeakModule
      (tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂) where
  truncation := tensorOuterModes_truncated hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  jacobi := modeJacobi_of_homogeneous (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃ N₄.toWeakModule
    (tensorOuterModes_truncated hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
    (fun d u hu γ c ξ z hξ hz ell m n => tensorOuterModes_jacobi_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu hξ hz ell m n)

/-- The actual logarithmic outer intertwiner reconstructed from the literal
full-product collision coefficients, with full Jacobi and coupled derivative. -/
noncomputable def tensorOuterIntertwiner :
    LogIntertwiningOperator (tensorModule hC2 N₁ N₂ hfg₁ hfg₂).toWeakModule
      N₃.toWeakModule N₄.toWeakModule :=
  ⟨tensorOuterLogModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂,
    isLogIntertwining_logLift_of_jacobi_weight (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃ N₄
      (tensorOuterModes_isJacobi hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
      (tensorOuterModes_weight hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)⟩

@[simp] theorem tensorOuterIntertwiner_zero (n : ℂ) :
    (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂).1 n 0=
      tensorOuterModes hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n :=
  tensorOuterLogModes_zero hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ n

end VOA.Huang.LogAssocTensorOuterModes
