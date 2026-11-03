import VOA.Modules.LogTensorPzPointTransport
import VOA.Modules.LogTensorBalancing

/-! Chosen-branch logarithmic point evaluations transform under the actual
L(0) exponentials, including every nilpotent Jordan contribution. -/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.Pz
open VOA.LogTensor.Contra
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- The genuine conformal exponentials compose with their actual parameters. -/
theorem L0exp_apply_add (N : LogVModule W M₁) (s ell : ℂ) (x : M₁) :
    L0exp N s (L0exp N ell x)=L0exp N (s+ell) x :=
  DFunLike.congr_fun (L0exp_add N s ell) x

/-- Actual opposite conformal parameters cancel, without semisimplicity. -/
theorem L0exp_neg_cancel (N : LogVModule W M₁) (s : ℂ) (x : M₁) :
    L0exp N (-s) (L0exp N s x)=x := by
  rw [L0exp_apply_add,neg_add_cancel,L0exp_zero_apply]

/-- The genuine completion carries the same conformal parameter addition. -/
theorem completionL0exp_add (N : LogVModule W M₃) (s ell : ℂ) (q : Completion N) :
    completionL0exp N s (completionL0exp N ell q)=completionL0exp N (s+ell) q := by
  funext c
  apply Subtype.ext
  exact L0exp_apply_add N s ell (q c)

/-- An arbitrary chosen-branch point is the actual conformal transport of
another chosen-branch point; every logarithmic coefficient is retained. -/
theorem evaluatePoint_shift_transport (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell s : ℂ) (x : M₁) (y : M₂) :
    evaluatePoint N₁ N₂ N₃ Y (ell+s) x y=
      completionL0exp N₃ s (evaluatePoint N₁ N₂ N₃ Y ell (L0exp N₁ (-s) x) (L0exp N₂ (-s) y)) := by
  rw [evaluatePoint_L0exp N₁ N₂ N₃ Y (ell+s),evaluatePoint_L0exp N₁ N₂ N₃ Y ell]
  funext c
  apply Subtype.ext
  change L0exp N₃ (ell+s)
      (evaluateOne N₁ N₂ N₃ Y (L0exp N₁ (-(ell+s)) x) (L0exp N₂ (-(ell+s)) y) c)=
    L0exp N₃ s (L0exp N₃ ell
      (evaluateOne N₁ N₂ N₃ Y (L0exp N₁ (-ell) (L0exp N₁ (-s) x))
        (L0exp N₂ (-ell) (L0exp N₂ (-s) y)) c))
  rw [L0exp_apply_add N₁ (-ell) (-s),L0exp_apply_add N₂ (-ell) (-s),L0exp_apply_add N₃ s ell]
  rw [show -ell+-s=-(ell+s) by ring,add_comm s ell]

/-- The genuine completed evaluation restricts to its literal homogeneous block. -/
theorem evaluatePoint_eq_block (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (c : ℂ) :
    evaluatePoint N₁ N₂ N₃ Y ell x y c=pointEvaluationBlock N₁ N₂ N₃ Y ell a b c ⟨x,hx⟩ ⟨y,hy⟩ := by
  rw [evaluatePoint,fromBlocks_homogeneous N₁ N₂ _ hx hy]
  rfl

/-- The literal finite generalized-weight point blocks obey actual conformal scaling. -/
theorem pointEvaluationBlock_shift_transport (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell s a b c : ℂ) (x : N₁.weight a) (y : N₂.weight b) :
    (pointEvaluationBlock N₁ N₂ N₃ Y (ell+s) a b c x y : M₃)=
      L0exp N₃ s (pointEvaluationBlock N₁ N₂ N₃ Y ell a b c
        ⟨L0exp N₁ (-s) x,L0exp_mem_weight N₁ (-s) x.2⟩
        ⟨L0exp N₂ (-s) y,L0exp_mem_weight N₂ (-s) y.2⟩) := by
  have hh := congrArg (fun q : Completion N₃ => (q c : M₃))
    (evaluatePoint_shift_transport N₁ N₂ N₃ Y ell s x y)
  dsimp only at hh
  rw [completionL0exp_apply,evaluatePoint_eq_block N₁ N₂ N₃ Y (ell+s) x.2 y.2 c,
    evaluatePoint_eq_block N₁ N₂ N₃ Y ell (L0exp_mem_weight N₁ (-s) x.2)
      (L0exp_mem_weight N₂ (-s) y.2) c] at hh
  exact hh

end VOA.LogTensor.Pz
