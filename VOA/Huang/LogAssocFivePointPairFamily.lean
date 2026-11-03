import VOA.Huang.LogAssocFivePointPairInduction
import VOA.Huang.LogAssocFivePointFamily

/-! One finite regular coefficient module contains the true full logarithmic
two-cluster family. Generalized weight lower bounds give the common rectangle;
the actual five-slot C1 descent includes every original logarithmic degree. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries
open VOA.Huang.LogHuangODEProduct VOA.Huang.FivePointSep
open scoped BigOperators
universe u
variable {V M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]
variable {A₀ : GWModule W M₀} {A₁ : GWModule W M₁} {A₂ : GWModule W M₂}
  {A₃ : GWModule W M₃} {A₄ : GWModule W M₄} {AU : GWModule W MU} {AV : GWModule W MV}
variable {P : LogModes MU MV M₀} {ZT : LogModes M₂ M₁ MV} {XY : LogModes M₃ M₄ MU}

/-- The literal normalized two-cluster coefficient, with three true log degrees. -/
def logPairNormalizedSeries (P : LogModes MU MV M₀) (ZT : LogModes M₂ M₁ MV)
    (XY : LogModes M₃ M₄ MU) (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ)
    (t : M₁) (z : M₂) (x : M₃) (y : M₄) (N₀ s k l j : ℕ) : PS2 :=
  normalizedSeries pairY₁ (pairY₂ (fun n => P n k) (fun n => ZT n l)) (fun n => XY n j)
    c ν μ f t z x y N₀ s

/-- Genuine lower bounds give a common rectangle for all log triples. -/
theorem exists_pairBase_family
    (hZT : ∀ l, IsGradedJacobiFamily A₂ A₁ AV (fun n => ZT n l))
    (hXY : ∀ j, IsGradedJacobiFamily A₃ A₄ AU (fun n => XY n j))
    (h₁ h₂ h₃ h₄ ν₀ μ₀ : ℂ) :
    ∃ K L : ℕ, ∀ k l j, PairBase A₁ A₂ A₃ A₄
      (fun n => P n k) (fun n => ZT n l) (fun n => XY n j)
      h₁ h₂ h₃ h₄ (ν₀+K) (μ₀+L) := by
  obtain ⟨BU,hBU⟩ := AU.boundedBelow
  obtain ⟨BV,hBV⟩ := AV.boundedBelow
  obtain ⟨L,hL⟩ := exists_nat_gt ((h₃+h₄-μ₀-1).re-BU)
  obtain ⟨K,hK⟩ := exists_nat_gt ((h₁+h₂+h₃+h₄-ν₀-2).re-BU-BV)
  refine ⟨K,L,?_⟩
  intro k l j N₁ N₂ N₃ N₄ s hs t z x y ht hz hx hy m n hmn p
  have hs' : (N₁ : ℝ)+N₂+N₃+N₄ ≤ s := by exact_mod_cast hs
  have hU := (hXY j).mem_weight hx hy (μ₀+L+s-n)
  have hV := (hZT l).mem_weight hz ht (ν₀+K-(μ₀+L)-m+n)
  by_cases hUz : XY (μ₀+L+s-n) j x y=0
  · rw [hUz,map_zero,LinearMap.zero_apply]
  by_cases hVz : ZT (ν₀+K-(μ₀+L)-m+n) l z t=0
  · rw [hVz,map_zero]
  exfalso
  have hbU := hBU _ (fun hb => hUz (by rw [hb,Submodule.mem_bot] at hU; exact hU))
  have hbV := hBV _ (fun hb => hVz (by rw [hb,Submodule.mem_bot] at hV; exact hV))
  simp only [Complex.add_re,Complex.sub_re,Complex.natCast_re,Complex.intCast_re,
    Complex.one_re] at hbU hbV hK hL
  norm_num at hK
  have hN : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg _
  rcases hmn with hm | hn
  · have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    linarith
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
    linarith

/-- Any vanished actual log component kills the normalized pair series. -/
theorem logPairNormalizedSeries_zero_log (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ)
    (t : M₁) (z : M₂) (x : M₃) (y : M₄) (N₀ s k l j : ℕ)
    (hz : (∀ n,P n k=0) ∨ (∀ n,ZT n l=0) ∨ (∀ n,XY n j=0)) :
    logPairNormalizedSeries P ZT XY c ν μ f t z x y N₀ s k l j=0 := by
  rcases hz with hz | hz | hz
  all_goals
    ext m n
    simp only [logPairNormalizedSeries,coeff_normalizedSeries,map_zero,normalizedCoeff,productCoeff]
    change f (P (c-ν-2*(N₀ : ℂ)+m) k (XY (μ+s-n) j x y)
      (ZT (ν-μ-m+n) l z t))=0
    simp [hz]

/-- Every actual log triple lies in one finite regular two-cluster module. -/
theorem exists_joint_fg_pair {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ} {B₀ B₁ B₂ B₃ B₄ K L J : ℕ}
    (hP : ∀ k, IsGradedJacobiFamily AU AV A₀ (fun n => P n k))
    (hZT : ∀ l, IsGradedJacobiFamily A₂ A₁ AV (fun n => ZT n l))
    (hXY : ∀ j, IsGradedJacobiFamily A₃ A₄ AU (fun n => XY n j))
    (hl₀ : CosetBase A₀ h₀) (hl₁ : CosetBase A₁ h₁)
    (hl₂ : CosetBase A₂ h₂) (hl₃ : CosetBase A₃ h₃) (hl₄ : CosetBase A₄ h₄)
    (hB : ∀ k l j, PairBase A₁ A₂ A₃ A₄
      (fun n => P n k) (fun n => ZT n l) (fun n => XY n j) h₁ h₂ h₃ h₄ ν μ)
    (hD₀ : DualC1Graded A₀ h₀ B₀) (hC₁ : C1Graded A₁ h₁ B₁)
    (hC₂ : C1Graded A₂ h₂ B₂) (hC₃ : C1Graded A₃ h₃ B₃) (hC₄ : C1Graded A₄ h₄ B₄)
    (hK : ∀ n k,K ≤ k → P n k=0) (hL : ∀ n l,L ≤ l → ZT n l=0)
    (hJ : ∀ n j,J ≤ j → XY n j=0) :
    ∃ NN : Submodule pairRing PS2, NN.FG ∧
      ∀ (k l j N₀ N₁ N₂ N₃ N₄ : ℕ) (f : M₀ →ₗ[ℂ] ℂ) t z x y,
        t ∈ A₁.weight (h₁+N₁) → z ∈ A₂.weight (h₂+N₂) →
        x ∈ A₃.weight (h₃+N₃) → y ∈ A₄.weight (h₄+N₄) →
        logPairNormalizedSeries P ZT XY (h₁+h₂+h₃+h₄-h₀-3) ν μ
          f t z x y N₀ (N₀+N₁+N₂+N₃+N₄) k l j ∈ NN := by
  classical
  let I := Fin K × Fin L × Fin J
  choose T hTfin hT using fun p : I => exists_finite_span_pair_box
    (hP p.1) (hZT p.2.1) (hXY p.2.2) h₀ h₁ h₂ h₃ h₄ ν μ B₀ B₁ B₂ B₃ B₄
  let NN : Submodule pairRing PS2 := Submodule.span pairRing (⋃ p,T p)
  refine ⟨NN,Submodule.fg_span (Set.finite_iUnion hTfin),?_⟩
  intro k l j N₀ N₁ N₂ N₃ N₄ f t z x y ht hz hx hy
  by_cases hk : K ≤ k
  · rw [logPairNormalizedSeries_zero_log _ _ _ _ _ _ _ _ _ _ _ _ _ (Or.inl (fun n => hK n k hk))]
    exact NN.zero_mem
  by_cases hl : L ≤ l
  · rw [logPairNormalizedSeries_zero_log _ _ _ _ _ _ _ _ _ _ _ _ _ (Or.inr (Or.inl (fun n => hL n l hl)))]
    exact NN.zero_mem
  by_cases hj : J ≤ j
  · rw [logPairNormalizedSeries_zero_log _ _ _ _ _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (fun n => hJ n j hj)))]
    exact NN.zero_mem
  let p : I := (⟨k,by omega⟩,⟨l,by omega⟩,⟨j,by omega⟩)
  have hle : Submodule.span ℂ (T p) ≤ NN.restrictScalars ℂ :=
    (Submodule.span_mono (Set.subset_iUnion T p)).trans
      (Submodule.span_le_restrictScalars ℂ pairRing _)
  apply pairSeries_mem (hP k) (hZT l) (hXY j) hl₀ hl₁ hl₂ hl₃ hl₄
    (hB k l j) hD₀ hC₁ hC₂ hC₃ hC₄ NN
  · intro n₀ n₁ n₂ n₃ n₄ b₀ b₁ b₂ b₃ b₄ f t z x y ht hz hx hy
    exact hle (hT p n₀ n₁ n₂ n₃ n₄ b₀ b₁ b₂ b₃ b₄ f t z x y ht hz hx hy)
  · rfl
  · exact ht
  · exact hz
  · exact hx
  · exact hy

/-- The true inner derivative retains the successor logarithmic coefficient. -/
theorem logPairNormalizedSeries_Lm1_inner
    {NX : LogVModule W M₃} {NY : LogVModule W M₄} {NU : LogVModule W MU}
    (XY : LogIntertwiningOperator NX.toWeakModule NY.toWeakModule NU.toWeakModule)
    (P : LogModes MU MV M₀) (ZT : LogModes M₂ M₁ MV)
    (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (t : M₁) (z : M₂) (x : M₃) (y : M₄)
    (N₀ s k l j : ℕ) :
    logPairNormalizedSeries P ZT XY.1 c ν μ f t z (Lm1 NX.toWeakModule x) y N₀ (s+1) k l j =
      thetaY (-(μ+(s : ℂ)+1)) (logPairNormalizedSeries P ZT XY.1 c ν μ f t z x y N₀ s k l j)+
        ((j : ℂ)+1) • logPairNormalizedSeries P ZT XY.1 c ν μ f t z x y N₀ s k l (j+1) :=
  logNormalizedSeries_Lm1_third XY (fun n _ => pairY₁ n)
    (fun n _ => pairY₂ (fun p => P p k) (fun p => ZT p l) n)
    c ν μ f t z x y N₀ s k l j

end VOA.Huang.LogAssocFivePointGraded
