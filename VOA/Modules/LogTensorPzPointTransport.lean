import VOA.Modules.LogTensorPzPointEvaluation
import VOA.Modules.LogTensorPzNilCovariance

/-! Actual logarithmic point evaluation is the genuine L(0) transport
of evaluateOne, including all Jordan parts. The identity is proved from
finite generalized weight blocks and the actual nilExp/logShift covariance. -/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.Pz
open VOA.LogTensor.Contra
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- The actual L(0) exponential acts on every component of the genuine completion. -/
noncomputable def completionL0exp (N : LogVModule W M₃) (ell : ℂ) :
    Completion N →ₗ[ℂ] Completion N where
  toFun q c := ⟨L0exp N ell (q c),L0exp_mem_weight N ell (q c).2⟩
  map_add' q r := by funext c; apply Subtype.ext; simp
  map_smul' s q := by funext c; apply Subtype.ext; simp

@[simp] theorem completionL0exp_apply (N : LogVModule W M₃) (ell : ℂ)
    (q : Completion N) (c : ℂ) :
    (completionL0exp N ell q c : M₃)=L0exp N ell (q c) := rfl

/-- Literal L(0)-transport of evaluateOne on the three genuine generalized modules. -/
noncomputable def transportedEvaluateOne (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell : ℂ) : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] Completion N₃ :=
  LinearMap.mk₂ ℂ (fun x y => completionL0exp N₃ ell
    (evaluateOne N₁ N₂ N₃ Y (L0exp N₁ (-ell) x) (L0exp N₂ (-ell) y)))
    (fun x x' y => by simp)
    (fun s x y => by simp)
    (fun x y y' => by simp)
    (fun s x y => by simp)

/-- Genuine chosen-branch evaluation equals actual L(0) transport, with no
ordinary-module, diagonalizability, finite-generation, or C2 premise. -/
theorem evaluatePoint_L0exp (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell : ℂ) : evaluatePoint N₁ N₂ N₃ Y ell=transportedEvaluateOne N₁ N₂ N₃ Y ell := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  funext c
  apply Subtype.ext
  have hx' := L0exp_mem_weight N₁ (-ell) hx
  have hy' := L0exp_mem_weight N₂ (-ell) hy
  dsimp only [transportedEvaluateOne,LinearMap.mk₂_apply]
  rw [completionL0exp_apply,evaluateOne_homogeneous N₁ N₂ N₃ Y hx' hy' c]
  have hmode : Y.1 (a+b-c-1) 0 (L0exp N₁ (-ell) x) (L0exp N₂ (-ell) y)∈N₃.weight c := by
    have hh := Y.2.mem_weight hx' hy' (a+b-c-1) 0
    convert hh using 1 <;> ring
  rw [L0exp_apply_of_mem N₃ ell hmode,L0exp_apply_of_mem N₁ (-ell) hx,
    L0exp_apply_of_mem N₂ (-ell) hy]
  simp only [map_smul,LinearMap.smul_apply,smul_smul]
  rw [nilExp_logShift N₁ N₂ N₃ Y ell (a+b-c-1) x y,
    evaluatePoint_logShift N₁ N₂ N₃ Y ell hx hy c]
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  congr 1
  ring

end VOA.LogTensor.Pz
