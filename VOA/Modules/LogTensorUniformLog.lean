import VOA.Modules.LogTensorUniformNil
import VOA.Modules.LogTensorGraded

/-! A single logarithmic degree bound for all genuine intertwining operators
between three finitely generated generalized modules. The bound works at every
mode and on every vector, not merely on a fixed triple of weight spaces. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.LogTensor
open Module (End)
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)

/-- Actual global Jordan bounds give a uniform bound on all logarithmic modes. -/
theorem uniform_log_degree_of_jordan {p q r : ℕ}
    (hp : N₁.L0nil ^ p = 0) (hq : N₂.L0nil ^ q = 0) (hr : N₃.L0nil ^ r = 0)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (n : ℂ) (k : ℕ) (hk : p+q+r ≤ k+2) : Y.1 n k = 0 := by
  ext x y
  have hx : x ∈ ⨆ α, N₁.weight α := by
    rw [N₁.isInternal.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction N₁.weight
    (motive := fun x => Y.1 n k x y = 0) hx ?_ ?_ ?_
  · intro a x hx
    have hy : y ∈ ⨆ β, N₂.weight β := by
      rw [N₂.isInternal.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction N₂.weight
      (motive := fun y => Y.1 n k x y = 0) hy ?_ ?_ ?_
    · intro b y hy
      apply Y.2.log_degree_bound (α₁ := a) (α₂ := b) (p := p) (q := q) (r := r)
      · intro z hz
        have hz' : z ∈ N₃.weight (a+b-n-1) := by
          exact N₃.maxGenEigenspace_le_weight _ hz
        change ((N₃.L0op-(a+b-n-1) • 1)^r) z = 0
        rw [← N₃.L0nil_pow_apply_of_mem r hz',hr,LinearMap.zero_apply]
      · change ((N₁.L0op-a • 1)^p) x = 0
        rw [← N₁.L0nil_pow_apply_of_mem p hx,hp,LinearMap.zero_apply]
      · change ((N₂.L0op-b • 1)^q) y = 0
        rw [← N₂.L0nil_pow_apply_of_mem q hy,hq,LinearMap.zero_apply]
      · exact hk
    · simp only [map_zero]
    · intro y z hy hz
      rw [map_add,hy,hz,add_zero]
  · simp only [map_zero,LinearMap.zero_apply]
  · intro x z hx hz
    rw [map_add,LinearMap.add_apply,hx,hz,add_zero]

/-- One finite logarithmic cutoff works for every genuine operator among three
finitely generated modules, uniformly across all their generalized weights. -/
theorem uniform_log_degree_of_finGen (h₁ : FinGen N₁.toWeakModule)
    (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule) :
    ∃ K : ℕ, ∀ Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule,
      ∀ n : ℂ, ∀ k : ℕ, K ≤ k → Y.1 n k = 0 := by
  obtain ⟨p,hp⟩ := Contra.L0nil_isNilpotent_of_finGen N₁ h₁
  obtain ⟨q,hq⟩ := Contra.L0nil_isNilpotent_of_finGen N₂ h₂
  obtain ⟨r,hr⟩ := Contra.L0nil_isNilpotent_of_finGen N₃ h₃
  exact ⟨p+q+r,fun Y n k hk => uniform_log_degree_of_jordan N₁ N₂ N₃ hp hq hr Y n k (by omega)⟩

end VOA.LogTensor
