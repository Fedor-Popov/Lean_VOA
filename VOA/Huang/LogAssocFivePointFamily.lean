import VOA.Huang.LogAssocFivePointC1Induction
import VOA.Huang.LogAssocFivePointCoupledAlgebra

/-! One finite regular bidisc module contains every genuine logarithmic
five-point coefficient. Uniform true weight bounds control both intermediate
levels; finite log bounds and the five-slot C1 descent give finite generation. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries
open VOA.Huang.LogHuangODEProduct VOA.Huang.FivePointSep
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : GWModule W M₀} {A₁ : GWModule W M₁} {A₂ : GWModule W M₂}
  {A₃ : GWModule W M₃} {A₄ : GWModule W M₄} {A₅ : GWModule W M₅} {A₆ : GWModule W M₆}
variable {Y₁ : LogModes M₁ M₆ M₀} {Y₂ : LogModes M₂ M₅ M₆} {Y₃ : LogModes M₃ M₄ M₅}

/-- The literal normalized all-log three-operator series. -/
def logNormalizedSeries (Y₁ : LogModes M₁ M₆ M₀) (Y₂ : LogModes M₂ M₅ M₆)
    (Y₃ : LogModes M₃ M₄ M₅) (c ν μ : ℂ) (f : M₀  →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄) (N₀ s k l j : ℕ) : PS2 :=
  normalizedSeries (fun n => Y₁ n k) (fun n => Y₂ n l) (fun n => Y₃ n j)
    c ν μ f x y z w N₀ s

/-- Both intermediate lower bounds are uniform over every log coefficient. -/
theorem exists_uniformTwoBase_family
    (hJ₂ : ∀ l, IsGradedJacobiFamily A₂ A₅ A₆ (fun n => Y₂ n l))
    (hJ₃ : ∀ j, IsGradedJacobiFamily A₃ A₄ A₅ (fun n => Y₃ n j))
    (h₂ h₃ h₄ ν₀ μ₀ : ℂ) :
    ∃ K L : ℕ, ∀ l j, UniformTwoBase A₂ A₃ A₄
      (fun n => Y₂ n l) (fun n => Y₃ n j) h₂ h₃ h₄ (ν₀+K) (μ₀+L) := by
  obtain ⟨B₅,hB₅⟩ := A₅.boundedBelow
  obtain ⟨B₆,hB₆⟩ := A₆.boundedBelow
  obtain ⟨K,hK⟩ := exists_nat_gt ((h₂+h₃+h₄-ν₀-2).re-B₆)
  obtain ⟨L,hL⟩ := exists_nat_gt ((h₃+h₄-μ₀-1).re-B₅)
  refine ⟨K,L,?_⟩
  intro l j N₂ N₃ N₄ s hs y z w hy hz hw m n hmn
  have hs' : (N₂ : ℝ)+N₃+N₄ ≤ s := by exact_mod_cast hs
  have hv₅ := (hJ₃ j).mem_weight hz hw (μ₀+L+s-n)
  have hv₆ := (hJ₂ l).mem_weight hy hv₅ (ν₀+K-(μ₀+L)-m+n)
  rcases hmn with hm | hn
  · by_contra he
    have hb := hB₆ _ (fun hb => he (by rw [hb,Submodule.mem_bot] at hv₆; exact hv₆))
    have hm' : (m : ℝ)<0 := by exact_mod_cast hm
    simp only [Complex.add_re,Complex.sub_re,Complex.natCast_re,
      Complex.intCast_re,Complex.one_re] at hb hK
    norm_num at hK
    linarith
  · have hz0 : Y₃ (μ₀+L+s-n) j z w=0 := by
      by_contra he
      have hb := hB₅ _ (fun hb => he (by rw [hb,Submodule.mem_bot] at hv₅; exact hv₅))
      have hn' : (n : ℝ)<0 := by exact_mod_cast hn
      have hN₂ : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
      simp only [Complex.add_re,Complex.sub_re,Complex.natCast_re,
        Complex.intCast_re,Complex.one_re] at hb hL
      linarith
    rw [hz0,map_zero]

/-- A vanishing log component kills its literal normalized series. -/
theorem logNormalizedSeries_zero_log (c ν μ : ℂ) (f : M₀  →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (w : M₄) (N₀ s k l j : ℕ)
    (hz : (∀ n,Y₁ n k=0)  ∨  (∀ n,Y₂ n l=0)  ∨  (∀ n,Y₃ n j=0)) :
    logNormalizedSeries Y₁ Y₂ Y₃ c ν μ f x y z w N₀ s k l j=0 := by
  rcases hz with hz | hz | hz
  all_goals
    ext m n
    simp [logNormalizedSeries,normalizedSeries,normalizedCoeff,productCoeff,hz]

/-- All original logarithmic degrees share one genuinely finite regular
coefficient module, at arbitrary external vector levels. -/
theorem exists_joint_fg {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ} {B₀ B₁ B₂ B₃ B₄ K L J : ℕ}
    (hJ₁ : ∀ k, IsGradedJacobiFamily A₁ A₆ A₀ (fun n => Y₁ n k))
    (hJ₂ : ∀ l, IsGradedJacobiFamily A₂ A₅ A₆ (fun n => Y₂ n l))
    (hJ₃ : ∀ j, IsGradedJacobiFamily A₃ A₄ A₅ (fun n => Y₃ n j))
    (hl₀ : CosetBase A₀ h₀) (hl₁ : CosetBase A₁ h₁)
    (hl₂ : CosetBase A₂ h₂) (hl₃ : CosetBase A₃ h₃) (hl₄ : CosetBase A₄ h₄)
    (hB : ∀ l j, UniformTwoBase A₂ A₃ A₄
      (fun n => Y₂ n l) (fun n => Y₃ n j) h₂ h₃ h₄ ν μ)
    (hD₀ : DualC1Graded A₀ h₀ B₀) (hC₁ : C1Graded A₁ h₁ B₁)
    (hC₂ : C1Graded A₂ h₂ B₂) (hC₃ : C1Graded A₃ h₃ B₃) (hC₄ : C1Graded A₄ h₄ B₄)
    (hK : ∀ n k,K ≤ k  →  Y₁ n k=0) (hL : ∀ n l,L ≤ l  →  Y₂ n l=0)
    (hJ : ∀ n j,J ≤ j  →  Y₃ n j=0) :
    ∃ NN : Submodule sepRing PS2, NN.FG  ∧ 
      ∀ (k l j N₀ N₁ N₂ N₃ N₄ : ℕ) (f : M₀  →ₗ[ℂ] ℂ) x y z w,
        x ∈ A₁.weight (h₁+N₁)  →  y ∈ A₂.weight (h₂+N₂)  → 
        z ∈ A₃.weight (h₃+N₃)  →  w ∈ A₄.weight (h₄+N₄)  → 
        logNormalizedSeries Y₁ Y₂ Y₃ (h₁+h₂+h₃+h₄-h₀-3) ν μ
          f x y z w N₀ (N₀+N₁+N₂+N₃+N₄) k l j  ∈  NN := by
  classical
  let I := Fin K × Fin L × Fin J
  choose T hTfin hT using fun p : I => exists_finite_span_normalized_box
    (hJ₁ p.1) (hJ₂ p.2.1) (hJ₃ p.2.2) h₀ h₁ h₂ h₃ h₄ ν μ B₀ B₁ B₂ B₃ B₄
  let NN : Submodule sepRing PS2 := Submodule.span sepRing (⋃ p,T p)
  refine ⟨NN,Submodule.fg_span (Set.finite_iUnion hTfin),?_⟩
  intro k l j N₀ N₁ N₂ N₃ N₄ f x y z w hx hy hz hw
  by_cases hk : K ≤ k
  · rw [logNormalizedSeries_zero_log _ _ _ _ _ _ _ _ _ _ _ _ _ (Or.inl (fun n => hK n k hk))]
    exact NN.zero_mem
  by_cases hl : L ≤ l
  · rw [logNormalizedSeries_zero_log _ _ _ _ _ _ _ _ _ _ _ _ _ (Or.inr (Or.inl (fun n => hL n l hl)))]
    exact NN.zero_mem
  by_cases hj : J ≤ j
  · rw [logNormalizedSeries_zero_log _ _ _ _ _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (fun n => hJ n j hj)))]
    exact NN.zero_mem
  let p : I := (⟨k,by omega⟩,⟨l,by omega⟩,⟨j,by omega⟩)
  have hle : Submodule.span ℂ (T p) ≤ NN.restrictScalars ℂ :=
    (Submodule.span_mono (Set.subset_iUnion T p)).trans
      (Submodule.span_le_restrictScalars ℂ sepRing _)
  apply normalizedSeries_mem (hJ₁ k) (hJ₂ l) (hJ₃ j) hl₀ hl₁ hl₂ hl₃ hl₄
    (hB l j) hD₀ hC₁ hC₂ hC₃ hC₄ NN
  · intro n₀ n₁ n₂ n₃ n₄ b₀ b₁ b₂ b₃ b₄ f x y z w hx hy hz hw
    exact hle (hT p n₀ n₁ n₂ n₃ n₄ b₀ b₁ b₂ b₃ b₄ f x y z w hx hy hz hw)
  · rfl
  · exact hx
  · exact hy
  · exact hz
  · exact hw

/-- The actual innermost logarithmic derivative is the inner Euler operator
plus the true successor logarithmic coefficient. -/
theorem logNormalizedSeries_Lm1_third
    {N₃ : LogVModule W M₃} {N₄ : LogVModule W M₄} {N₅ : LogVModule W M₅}
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    (Y₁ : LogModes M₁ M₆ M₀) (Y₂ : LogModes M₂ M₅ M₆)
    (c ν μ : ℂ) (f : M₀  →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (w : M₄)
    (N₀ s k l j : ℕ) :
    logNormalizedSeries Y₁ Y₂ Y₃.1 c ν μ f x y (Lm1 N₃.toWeakModule z) w N₀ (s+1) k l j =
      thetaY (-(μ+(s : ℂ)+1)) (logNormalizedSeries Y₁ Y₂ Y₃.1 c ν μ f x y z w N₀ s k l j)+
        ((j : ℂ)+1) • logNormalizedSeries Y₁ Y₂ Y₃.1 c ν μ f x y z w N₀ s k l (j+1) := by
  refine PS2.ext fun m n => ?_
  simp only [c2_add,c2_smul,c2_thetaY,logNormalizedSeries,c2_normalizedSeries,
    normalizedCoeff,productCoeff]
  rw [Y₃.2.L_neg_one,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply,
    map_add,map_smul,map_smul,map_add,map_smul,map_smul,map_add,map_smul,map_smul]
  have he : μ+((s+1 : ℕ) : ℂ)-(n : ℂ)-1=μ+(s : ℂ)-n := by push_cast; ring
  rw [he]
  push_cast
  simp only [smul_eq_mul]
  ring

end VOA.Huang.LogAssocFivePointGraded
