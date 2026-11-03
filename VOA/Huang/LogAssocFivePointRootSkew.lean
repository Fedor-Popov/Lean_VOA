import VOA.Modules.LogTensorSkewEquiv
import VOA.Huang.LogAssocCoefficientCompatibility

/-! Genuine all-log root reflection has a finite uniform outside profile.
Every original logarithmic degree is retained. The reflected coefficient at
mode p+j lies in the actual output weight beta-j, so the proved lower bound
truncates the profile uniformly in both internal weights. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocFivePoint
open VOA VOA.LogTensor VOA.LogSkew
open Module (End)
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- Per-log reflection is itself a genuine logarithmic intertwiner,
including its coupled derivative. It differs from Omega only by log shift. -/
noncomputable def rootSkewIntertwiner
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) :
    LogIntertwiningOperator N₂.toWeakModule N₁.toWeakModule N₃.toWeakModule :=
  ⟨skewK N₃.toWeakModule (omegaPhase 0) Y.1,
    Y.2.isLogIntertwining_skewK (omegaPhase_succ 0) (omegaPhase_ne_zero 0)⟩

/-- Every original logarithmic coefficient is recovered by reciprocal reflection. -/
theorem rootSkew_inverse_modes
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule) :
    skewK N₃.toWeakModule (fun n => (omegaPhase 0 n)⁻¹)
      (rootSkewIntertwiner N₁ N₂ N₃ Y).1=Y.1 :=
  Y.2.skewK_skewK (omegaPhase_succ 0)
    (fun n => inv_mul_cancel₀ (omegaPhase_ne_zero 0 n))

/-- The actual generalized output spectrum uniformly truncates root
reflection, for every input weight and every logarithmic degree. -/
theorem exists_rootSkew_uniform_range
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (β : ℂ) : ∃ J : ℕ,∀ (a b : ℂ) (x : M₁) (y : M₂),
      x∈N₁.weight a → y∈N₂.weight b → ∀ (j k : ℕ),J≤j →
      (rootSkewIntertwiner N₁ N₂ N₃ Y).1 (a+b-β-1+j) k y x=0 := by
  obtain ⟨B,hB⟩ := N₃.boundedBelow
  refine ⟨Nat.ceil (β.re-B)+1,fun a b x y hx hy j k hj => ?_⟩
  have hmem := (rootSkewIntertwiner N₁ N₂ N₃ Y).2.mem_weight hy hx (a+b-β-1+j) k
  have he : b+a-(a+b-β-1+(j : ℂ))-1=β-j := by ring
  rw [he] at hmem
  by_contra hne
  have hbot : N₃.weight (β-j)≠⊥ := fun hb => hne (by
    rw [hb] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem)
  have hbound := hB (β-j) hbot
  have hj' : (Nat.ceil (β.re-B) : ℝ)+1≤j := by exact_mod_cast hj
  have hceil : β.re-B≤Nat.ceil (β.re-B) := Nat.le_ceil _
  simp only [Complex.sub_re,Complex.natCast_re] at hbound
  linarith

/-- Exact all-log root coefficient reflection with a genuine finite profile. -/
theorem rootSkew_expand
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (p : ℂ) (k : ℕ) (x : M₁) (y : M₂) (J : ℕ)
    (hJ : ∀ j : ℕ,J≤j → (rootSkewIntertwiner N₁ N₂ N₃ Y).1 (p+j) k y x=0) :
    Y.1 p k x y=(omegaPhase 0 p)⁻¹ • ∑ j∈Finset.range J,
      sc j • (Lm1 N₃.toWeakModule ^ j) ((rootSkewIntertwiner N₁ N₂ N₃ Y).1 (p+j) k y x) := by
  have hi := congrArg (fun Z : LogModes M₁ M₂ M₃ => Z p k x y)
    (rootSkew_inverse_modes N₁ N₂ N₃ Y)
  exact hi.symm.trans ((rootSkewIntertwiner N₁ N₂ N₃ Y).2.skewK_eq_sum
    (fun n => (omegaPhase 0 n)⁻¹) p k x y J hJ)

/-- Scalar all-log root reflection retains the literal outside translation
profiles and phase coefficients, with no ordinary-module premise. -/
theorem rootSkew_expand_apply
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (f : M₃ →ₗ[ℂ] ℂ) (p : ℂ) (k : ℕ) (x : M₁) (y : M₂) (J : ℕ)
    (hJ : ∀ j : ℕ,J≤j → (rootSkewIntertwiner N₁ N₂ N₃ Y).1 (p+j) k y x=0) :
    f (Y.1 p k x y)=∑ j∈Finset.range J,(omegaPhase 0 p)⁻¹*sc j*
      (f ∘ₗ (Lm1 N₃.toWeakModule ^ j)) ((rootSkewIntertwiner N₁ N₂ N₃ Y).1 (p+j) k y x) := by
  rw [rootSkew_expand N₁ N₂ N₃ Y p k x y J hJ,map_smul,map_sum,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul,smul_eq_mul,LinearMap.comp_apply]
  ring

/-- The exact root phase on natural weight shifts retains its constant norm. -/
theorem rootSkew_phase_add_nat (p : ℂ) (m : ℕ) :
    omegaPhase 0 (p+m)=(-1 : ℂ)^m*omegaPhase 0 p := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : p+((m+1 : ℕ) : ℂ)=(p+(m : ℂ))+1 := by push_cast; ring
    rw [he,omegaPhase_succ 0,ih,pow_succ]
    ring

/-- The reciprocal root phase has a uniform norm on every genuine natural row. -/
theorem rootSkew_phase_norm_add_nat (p : ℂ) (m : ℕ) :
    ‖(omegaPhase 0 (p+m))⁻¹‖=‖(omegaPhase 0 p)⁻¹‖ := by
  rw [rootSkew_phase_add_nat,norm_inv,norm_mul,norm_pow]
  norm_num

/-- Actual generalized output weights give one exact finite scalar profile
for every live pair of input weights and every original logarithmic degree. -/
theorem exists_rootSkew_scalar_profiles
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (β : ℂ) : ∃ J : ℕ,∀ (a b : ℂ) (x : M₁) (y : M₂),
      x∈N₁.weight a → y∈N₂.weight b → ∀ (f : M₃ →ₗ[ℂ] ℂ) (k : ℕ),
      f (Y.1 (a+b-β-1) k x y)=
        ∑ j∈Finset.range J,(omegaPhase 0 (a+b-β-1))⁻¹*sc j*
          (f ∘ₗ (Lm1 N₃.toWeakModule ^ j))
            ((rootSkewIntertwiner N₁ N₂ N₃ Y).1 (a+b-β-1+j) k y x) := by
  obtain ⟨J,hJ⟩ := exists_rootSkew_uniform_range N₁ N₂ N₃ Y β
  refine ⟨J,fun a b x y hx hy f k => ?_⟩
  exact rootSkew_expand_apply N₁ N₂ N₃ Y f (a+b-β-1) k x y J
    (fun j hj => hJ a b x y hx hy j k hj)

end VOA.Huang.LogAssocFivePoint
