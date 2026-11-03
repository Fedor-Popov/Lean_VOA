import VOA.Huang.LogHuangODEProductDerivative
import VOA.Huang.LogHuangODEProductDual

/-! One genuinely finite regular coefficient module contains all logarithmic
product coefficients, at every tuple level and every logarithmic degree.
The finite logarithmic cutoffs come from the actual global Jordan bounds. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEProduct
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
  {A₁ : GWModule W M₁} {A₂ : GWModule W M₂} {A₃ : GWModule W M₃}
  {A₄ : GWModule W M₄} {A₅ : GWModule W M₅}
  {Y₁ : LogModes M₁ M₅ M₄} {Y₂ : LogModes M₂ M₃ M₅}

theorem QT_zero_log_left (c ν : ℂ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (k l n₄ s : ℕ)
    (hz : ∀ n, Y₁ n k = 0) :
    QT (fun n => Y₁ n k) (fun n => Y₂ n l) c ν f x y z n₄ s = 0 := by
  ext n
  simp only [QT,coeff_prodQ,hz,LinearMap.zero_apply,map_zero]

theorem QT_zero_log_right (c ν : ℂ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (k l n₄ s : ℕ)
    (hz : ∀ n, Y₂ n l = 0) :
    QT (fun n => Y₁ n k) (fun n => Y₂ n l) c ν f x y z n₄ s = 0 := by
  ext n
  simp only [QT,coeff_prodQ,hz,LinearMap.zero_apply,map_zero]

/-- All true logarithmic coefficients share one finite regular coefficient module. -/
theorem exists_joint_fg {h₁ h₂ h₃ h₄ ν : ℂ} {B₁ B₂ B₃ B₄ K₁ K₂ : ℕ}
    (hJ₁ : ∀ k, IsGradedJacobiFamily A₁ A₅ A₄ (fun n => Y₁ n k))
    (hJ₂ : ∀ l, IsGradedJacobiFamily A₂ A₃ A₅ (fun n => Y₂ n l))
    (hl₁ : CosetBase A₁ h₁) (hl₂ : CosetBase A₂ h₂)
    (hl₃ : CosetBase A₃ h₃) (hl₄ : CosetBase A₄ h₄)
    (hUB : ∀ l, UnifBase A₂ A₃ (fun n => Y₂ n l) h₂ h₃ ν)
    (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hD₄ : DualC1Graded A₄ h₄ B₄)
    (hK₁ : ∀ n k, K₁ ≤ k → Y₁ n k = 0)
    (hK₂ : ∀ n l, K₂ ≤ l → Y₂ n l = 0) :
    ∃ NN : Submodule (ratRing 1) (PowerSeries ℂ), NN.FG ∧
      ∀ (k l N₁ N₂ N₃ N₄ : ℕ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃),
        x∈A₁.weight (h₁+N₁) → y∈A₂.weight (h₂+N₂) → z∈A₃.weight (h₃+N₃) →
        QT (fun n => Y₁ n k) (fun n => Y₂ n l) (h₁+h₂+h₃-h₄-2) ν f x y z N₄
          (N₁+N₂+N₃+N₄) ∈ NN := by
  classical
  let I := (Fin K₁ × Fin K₂) ×
    (Fin (B₁+1) × Fin (B₂+1) × Fin (B₃+1) × Fin (B₄+1))
  choose T hTfin hT using fun q : I =>
    exists_finite_span (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄) (ν := ν)
      (hJ₁ q.1.1) (hJ₂ q.1.2) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  let NN : Submodule (ratRing 1) (PowerSeries ℂ) := Submodule.span (ratRing 1) (⋃ q, T q)
  refine ⟨NN,Submodule.fg_span (Set.finite_iUnion hTfin),?_⟩
  intro k l N₁ N₂ N₃ N₄ f x y z hx hy hz
  by_cases hk : K₁ ≤ k
  · rw [QT_zero_log_left _ _ _ _ _ _ _ _ _ _ (fun n => hK₁ n k hk)]
    exact NN.zero_mem
  by_cases hl : K₂ ≤ l
  · rw [QT_zero_log_right _ _ _ _ _ _ _ _ _ _ (fun n => hK₂ n l hl)]
    exact NN.zero_mem
  have hbase : ∀ (n₁ n₂ n₃ n₄ : ℕ), n₁ ≤ B₁ → n₂ ≤ B₂ → n₃ ≤ B₃ → n₄ ≤ B₄ →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃), x∈A₁.weight (h₁+n₁) →
        y∈A₂.weight (h₂+n₂) → z∈A₃.weight (h₃+n₃) →
        QT (fun n => Y₁ n k) (fun n => Y₂ n l) (h₁+h₂+h₃-h₄-2) ν f x y z n₄
          (n₁+n₂+n₃+n₄) ∈ NN := by
    intro n₁ n₂ n₃ n₄ b₁ b₂ b₃ b₄ f x y z hx hy hz
    let q : I := ((⟨k,by omega⟩,⟨l,by omega⟩),
      (⟨n₁,by omega⟩,⟨n₂,by omega⟩,⟨n₃,by omega⟩,⟨n₄,by omega⟩))
    have hq := hT q f x y z hx hy hz
    have hle : Submodule.span ℂ (T q) ≤ NN.restrictScalars ℂ :=
      (Submodule.span_mono (Set.subset_iUnion T q)).trans
        (Submodule.span_le_restrictScalars ℂ (ratRing 1) _)
    exact hle hq
  exact qt_mem (hJ₁ k) (hJ₂ l) hl₁ hl₂ hl₃ hl₄ (hUB l) hC₁ hC₂ hC₃ hD₄
    NN hbase _ N₁ N₂ N₃ N₄ rfl f x y z hx hy hz

end VOA.Huang.LogHuangODEProduct
