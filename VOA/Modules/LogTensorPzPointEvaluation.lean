import VOA.Modules.LogTensorPzEvaluation
import VOA.Modules.LogTensorContraL0Exp
import VOA.Modules.LogTensorSkewEquiv

/-! Actual logarithmic evaluation at a chosen branch ell, at z=exp(ell).
Each component is the genuine finite sum of logarithmic modes with its
complex exponential factor. Generalized homogeneous blocks assemble to
the true completed module; no ordinary or semisimple hypothesis occurs. -/
set_option maxSynthPendingDepth 3
namespace VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- Every actual logarithmic coefficient on one triple of weight spaces. -/
noncomputable def logarithmicBlock (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (a b c : ℂ) (k : ℕ) : N₁.weight a →ₗ[ℂ] N₂.weight b →ₗ[ℂ] N₃.weight c :=
  LinearMap.mk₂ ℂ (fun x y => ⟨Y.1 (a+b-c-1) k x y,by
    have hh := Y.2.mem_weight x.2 y.2 (a+b-c-1) k
    convert hh using 1 <;> ring⟩)
    (fun x x' y => by apply Subtype.ext; dsimp only; simp)
    (fun s x y => by apply Subtype.ext; dsimp only; simp)
    (fun x y y' => by apply Subtype.ext; dsimp only; simp)
    (fun s x y => by apply Subtype.ext; dsimp only; simp)

/-- A concrete bound from the genuine three generalized weight spaces.
The added one also gives a uniform nonempty range at ell=0. -/
noncomputable def pointLogCutoff (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) (a b c : ℂ) : ℕ :=
  Module.finrank ℂ (N₁.weight a)+Module.finrank ℂ (N₂.weight b)+
    Module.finrank ℂ (N₃.weight c)+1

theorem pointLogCutoff_vanish (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (a b c : ℂ) {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    {k : ℕ} (hk : pointLogCutoff N₁ N₂ N₃ a b c≤k) : Y.1 (a+b-c-1) k x y=0 := by
  apply Y.2.log_degree_le hx hy
  have he : a+b-(a+b-c-1)-1=c := by ring
  rw [he]
  dsimp only [pointLogCutoff] at hk
  omega

/-- The actual finite logarithmic evaluation on one weight triple. -/
noncomputable def pointEvaluationBlock (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell a b c : ℂ) : N₁.weight a →ₗ[ℂ] N₂.weight b →ₗ[ℂ] N₃.weight c :=
  Complex.exp (ell*(c-a-b)) •
    ∑ k∈Finset.range (pointLogCutoff N₁ N₂ N₃ a b c),
      ell^k • logarithmicBlock N₁ N₂ N₃ Y a b c k

/-- Actual evaluation into the genuine generalized weight completion at exp(ell). -/
noncomputable def evaluatePoint (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell : ℂ) : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] Completion N₃ :=
  fromBlocks N₁ N₂ fun a b => LinearMap.mk₂ ℂ
    (fun x y c => pointEvaluationBlock N₁ N₂ N₃ Y ell a b c x y)
    (fun x x' y => by funext c; simp)
    (fun s x y => by funext c; simp)
    (fun x y y' => by funext c; simp)
    (fun s x y => by funext c; simp)

/-- The chosen branch and every actual logarithmic coefficient appear literally. -/
theorem evaluatePoint_homogeneous (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell : ℂ) {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    (c : ℂ) :
    (evaluatePoint N₁ N₂ N₃ Y ell x y c : M₃)=Complex.exp (ell*(c-a-b)) •
      ∑ k∈Finset.range (pointLogCutoff N₁ N₂ N₃ a b c),ell^k • Y.1 (a+b-c-1) k x y := by
  rw [evaluatePoint,fromBlocks_homogeneous N₁ N₂ _ hx hy]
  simp only [LinearMap.mk₂_apply,pointEvaluationBlock,LinearMap.smul_apply,
    LinearMap.sum_apply,Submodule.coe_smul,Submodule.coe_sum]
  rfl

/-- At branch zero, the actual point evaluation agrees with evaluateOne. -/
theorem evaluatePoint_zero (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) :
    evaluatePoint N₁ N₂ N₃ Y 0=evaluateOne N₁ N₂ N₃ Y := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  funext c
  apply Subtype.ext
  rw [evaluatePoint_homogeneous N₁ N₂ N₃ Y 0 hx hy,
    evaluateOne_homogeneous N₁ N₂ N₃ Y hx hy c]
  simp only [zero_mul,Complex.exp_zero,one_smul]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    rw [zero_pow hk0,zero_smul]
  · intro hh
    exfalso
    apply hh
    simp only [Finset.mem_range,pointLogCutoff]
    omega

/-- Evaluating the actual logarithmic polynomial is the zero coefficient
of the genuine finite log shift, with its complex exponential retained. -/
theorem evaluatePoint_logShift (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell : ℂ) {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    (c : ℂ) :
    (evaluatePoint N₁ N₂ N₃ Y ell x y c : M₃)=Complex.exp (ell*(c-a-b)) •
      logShift ell Y.1 (a+b-c-1) 0 x y := by
  rw [evaluatePoint_homogeneous N₁ N₂ N₃ Y ell hx hy c,
    logShift_eq_sum Y.2.logFin (pointLogCutoff N₁ N₂ N₃ a b c)
      (fun k hk => pointLogCutoff_vanish N₁ N₂ N₃ Y a b c hx hy hk)]
  simp only [shc,Nat.choose_zero_right,Nat.sub_zero,Nat.cast_one,one_mul]

/-- Actual completed evaluation at every chosen branch is faithful. The
higher log coefficients are recovered from genuine shifted L(0) brackets. -/
theorem evaluatePoint_injective (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) (ell : ℂ) :
    Function.Injective (fun Y => evaluatePoint N₁ N₂ N₃ Y ell) := by
  intro Y Z h
  let Y' : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule :=
    ⟨logShift ell Y.1,Y.2.isLogIntertwining_logShift ell⟩
  let Z' : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule :=
    ⟨logShift ell Z.1,Z.2.isLogIntertwining_logShift ell⟩
  have hzero : logZero N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Y'=
      logZero N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule Z' := by
    funext n
    ext x y
    refine LogFin.induction_on N₁ (C := fun x => Y'.1 n 0 x y=Z'.1 n 0 x y) x ?_ (by simp) ?_
    · intro a x hx
      refine LogFin.induction_on N₂ (C := fun y => Y'.1 n 0 x y=Z'.1 n 0 x y) y ?_ (by simp) ?_
      · intro b y hy
        have hp := congrArg (fun F => (F x y (a+b-n-1) : M₃)) h
        dsimp only at hp
        rw [evaluatePoint_logShift N₁ N₂ N₃ Y ell hx hy,
          evaluatePoint_logShift N₁ N₂ N₃ Z ell hx hy] at hp
        have he : a+b-(a+b-n-1)-1=n := by ring
        rw [he] at hp
        have hpc := congrArg (fun v : M₃ => (Complex.exp (ell*((a+b-n-1)-a-b)))⁻¹ • v) hp
        simpa only [smul_smul,inv_mul_cancel₀ (Complex.exp_ne_zero _),one_smul] using hpc
      · intro y z hy hz
        simp only [map_add,hy,hz]
    · intro x z hx hz
      simp only [map_add,LinearMap.add_apply,hx,hz]
  have hs : Y'=Z' := logZero_injective hzero
  have he := congrArg (fun F : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule
    N₃.toWeakModule => logShift (-ell) F.1) hs
  simp only [Y',Z',logShift_logShift Y.2.logFin,logShift_logShift Z.2.logFin,
    neg_add_cancel,logShift_zero Y.2.logFin,logShift_zero Z.2.logFin] at he
  exact Subtype.ext he

/-- Any genuine logarithmic cutoff gives exactly the same actual evaluation,
so a global Jordan bound can replace the separate weight-space cutoffs. -/
theorem pointEvaluationBlock_fixed_cutoff (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell a b c : ℂ) (x : N₁.weight a) (y : N₂.weight b) (K : ℕ)
    (hK : ∀ k,K≤k → Y.1 (a+b-c-1) k x y=0) :
    (pointEvaluationBlock N₁ N₂ N₃ Y ell a b c x y : M₃)=
      Complex.exp (ell*(c-a-b)) • ∑ k∈Finset.range K,ell^k • Y.1 (a+b-c-1) k x y := by
  have hh := evaluatePoint_logShift N₁ N₂ N₃ Y ell x.2 y.2 c
  rw [evaluatePoint,fromBlocks_homogeneous N₁ N₂ _ x.2 y.2] at hh
  simp only [LinearMap.mk₂_apply] at hh
  rw [hh,logShift_eq_sum Y.2.logFin K hK]
  simp only [shc,Nat.choose_zero_right,Nat.sub_zero,Nat.cast_one,one_mul]

end VOA.LogTensor.Pz
