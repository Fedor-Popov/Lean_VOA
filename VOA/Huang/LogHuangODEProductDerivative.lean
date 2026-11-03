import VOA.Huang.LogHuangODEProductSpan
import VOA.Modules.LogTensorUniformLog

/-! The actual logarithmic L(-1) derivative and a uniform coset base.
The degree-(l+1) correction is part of the exact series identity. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEProduct
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE
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

theorem exists_unifBase_family (Y₂ : ℕ → IntertwiningModes M₂ M₃ M₅)
    (hY₂ : ∀ k, IsGradedJacobiFamily A₂ A₃ A₅ (Y₂ k)) (h₂ h₃ ν₀ : ℂ) (s : ℕ) :
    ∃ K : ℕ, ∀ k, UnifBase A₂ A₃ (Y₂ k) h₂ h₃ (ν₀ - s + K) := by
  obtain ⟨B, hB⟩ := A₅.boundedBelow
  refine ⟨Nat.ceil ((h₂ + h₃ - ν₀).re + s - B) + 1, ?_⟩
  intro k N₂ N₃ w₂ w₃ hw₂ hw₃ j
  set K : ℕ := Nat.ceil ((h₂ + h₃ - ν₀).re + s - B) + 1 with hK
  have hv := (hY₂ k).mem_weight hw₂ hw₃
    (ν₀ - s + K + N₂ + N₃ + ((j : ℂ) + 1))
  by_cases hβ : A₅.weight (h₂ + N₂ + (h₃ + N₃) - (ν₀ - s + K + N₂ + N₃ + ((j : ℂ) + 1)) - 1) = ⊥
  · rw [hβ] at hv; exact (Submodule.mem_bot ℂ).mp hv
  · exfalso
    have h1 := hB _ hβ
    have h2 : (h₂ + N₂ + (h₃ + N₃) - (ν₀ - s + K + N₂ + N₃ + ((j : ℂ) + 1)) - 1).re
        = (h₂ + h₃ - ν₀).re + s - K - j - 2 := by
      simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
      ring
    have h3 : (h₂ + h₃ - ν₀).re + s - B ≤ (Nat.ceil ((h₂ + h₃ - ν₀).re + s - B) : ℝ) :=
      Nat.le_ceil _
    have h4 : ((K : ℕ) : ℝ) = (Nat.ceil ((h₂ + h₃ - ν₀).re + s - B) : ℝ) + 1 := by
      rw [hK]; push_cast; ring
    have h5 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [h2] at h1
    linarith

theorem Lm1_mem_weight {h : ℂ} {n : ℕ} {x : M₂}
    (hx : x ∈ A₂.weight (h+n)) :
    Lm1 A₂.toWeakModule x ∈ A₂.weight (h+((n+1 : ℕ) : ℂ)) := by
  have hm := C2Rigid.mode_mem_weight A₂ W.conformalVector_mem_grading_two hx (0 : ℤ)
  convert hm using 1
  congr 1
  push_cast
  ring

theorem Lm1_iterate_mem_weight {h : ℂ} {n : ℕ} {x : M₂}
    (hx : x ∈ A₂.weight (h+n)) (j : ℕ) :
    (⇑(Lm1 A₂.toWeakModule))^[j] x ∈ A₂.weight (h+((n+j : ℕ) : ℂ)) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact Lm1_mem_weight ih

/-- The genuine coupled derivative on a normalized product coefficient. -/
theorem QT_LogLm1 {Y₁ : LogModes M₁ M₅ M₄} {Y₂ : LogModes M₂ M₃ M₅}
    (hY₂ : IsLogIntertwining A₂.toWeakModule A₃.toWeakModule A₅.toWeakModule Y₂)
    (c ν : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (k l N₄ s : ℕ) :
    QT (fun n => Y₁ n k) (fun n => Y₂ n l) c ν f x (Lm1 A₂.toWeakModule y) z N₄ (s+1)
      = thetaShift (-(ν+s+1)) (QT (fun n => Y₁ n k) (fun n => Y₂ n l) c ν f x y z N₄ s)
        + ((l : ℂ)+1) • QT (fun n => Y₁ n k) (fun n => Y₂ n (l+1)) c ν f x y z N₄ s := by
  ext n
  rw [map_add,map_smul,coeff_thetaShift,QT,QT,QT,coeff_prodQ,coeff_prodQ,coeff_prodQ,
    hY₂.L_neg_one]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,smul_eq_mul]
  have he : ν+((s+1 : ℕ) : ℂ)-n-1=ν+s-n := by push_cast; ring
  rw [he]
  push_cast
  ring

end VOA.Huang.LogHuangODEProduct
