import VOA.Huang.LogAssocSpectrum
import VOA.Huang.LogAssocProductLinearity
import VOA.Modules.LogTensorPzAction

/-! Actual bilinear expansion coefficient maps of genuine logarithmic products.
Unique convergent log coefficients are extracted from the entire actual
intermediate spectrum, with all Jordan and logarithmic degrees retained. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficients
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules (logCoeff_congr)
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

private theorem spectrum_add_left (f : M₄ →ₗ[ℂ] ℂ)
    (x x' : M₁) (y : M₂) (z : M₃) (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f (x+x') y z a b c β t=
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β t+
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x' y z a b c β t := by
  unfold logProductSpectrumFun
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun mu _ =>
    fullCoset_add_left hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x x' y z _ _ ht

private theorem spectrum_add_right (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y y' : M₂) (z : M₃) (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x (y+y') z a b c β t=
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β t+
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y' z a b c β t := by
  unfold logProductSpectrumFun
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun mu _ =>
    fullCoset_add_right hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y y' z _ _ ht

private theorem spectrum_smul_left (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (s a b c β t : ℂ) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f (s•x) y z a b c β t=
      s*logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β t := by
  unfold logProductSpectrumFun
  simp only [fullCoset_smul_left,Finset.mul_sum]

private theorem spectrum_smul_right (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (s a b c β t : ℂ) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x (s•y) z a b c β t=
      s*logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β t := by
  unfold logProductSpectrumFun
  simp only [fullCoset_smul_right,Finset.mul_sum]

/-- A coefficient block is extracted from the genuine full log product. -/
noncomputable def coefficientBlock (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (a b : ℂ) : N₁.weight a →ₗ[ℂ] N₂.weight b →ₗ[ℂ] ℂ := by
  let F : M₁ → M₂ → ℂ → ℂ := fun x y =>
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β
  have hF (x : M₁) (y : M₂) : HasLogExp overlapDomain (F x y) :=
    log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z a b c β
  refine LinearMap.mk₂ ℂ (fun x y => logCoeff overlapDomain (F x y) (γ-a-b) k) ?_ ?_ ?_ ?_
  · intro x x' y
    have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      (fun t ht => spectrum_add_left hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ f x x' y z a b c β ht) (hF (x+x') y) (γ-a-b) k
    dsimp only
    simp only [Submodule.coe_add,Submodule.coe_smul,F]
    rw [he]
    simpa only [F,Pi.add_apply] using logCoeff_add isOpen_overlapDomain overlapDomain_subset
      overlapDomain_nonempty (hF x y) (hF x' y) (γ-a-b) k
  · intro s x y
    have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      (fun t _ => spectrum_smul_left hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ f x y z s a b c β t) (hF (s•x) y) (γ-a-b) k
    dsimp only
    simp only [Submodule.coe_add,Submodule.coe_smul,F]
    rw [he,logCoeff_smul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty s (hF x y)]
    rfl
  · intro x y y'
    have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      (fun t ht => spectrum_add_right hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ f x y y' z a b c β ht) (hF x (y+y')) (γ-a-b) k
    dsimp only
    simp only [Submodule.coe_add,Submodule.coe_smul,F]
    rw [he]
    simpa only [F,Pi.add_apply] using logCoeff_add isOpen_overlapDomain overlapDomain_subset
      overlapDomain_nonempty (hF x y) (hF x y') (γ-a-b) k
  · intro s x y
    have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      (fun t _ => spectrum_smul_right hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ f x y z s a b c β t) (hF x (s•y)) (γ-a-b) k
    dsimp only
    simp only [Submodule.coe_add,Submodule.coe_smul,F]
    rw [he,logCoeff_smul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty s (hF x y)]
    rfl

/-- The actual bilinear coefficient functional on the two genuine inside modules. -/
noncomputable def coefficient (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ) :
    BilinearDual (M₁ := M₁) (M₂ := M₂) :=
  fromBlocks N₁ N₂ (coefficientBlock hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k)

/-- The coefficient is literally the unique collision coefficient of the full
actual product, on each true generalized homogeneous input pair. -/
theorem coefficient_homogeneous (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y=
      logCoeff overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β)
        (γ-a-b) k := by
  rw [coefficient,fromBlocks_homogeneous N₁ N₂ _ hx hy]
  rfl

end VOA.Huang.LogAssocCoefficients
