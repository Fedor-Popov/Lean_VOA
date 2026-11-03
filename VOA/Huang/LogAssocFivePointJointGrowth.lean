import VOA.Huang.LogAssocFivePointInnerRegular
import VOA.Huang.LogAssocFivePointProduct

/-! Joint geometric bounds for literal three-operator logarithmic products.
Both internal levels and all original logarithmic degrees are retained. C2
and finite generation supply every C1, Jordan, and convergence premise; no
ordinary-module or semisimplicity assumption is present. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries
open VOA.Huang.LogHuangODEProduct VOA.Huang.FivePointSep
open scoped BigOperators
universe u
variable {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (N₆ : LogVModule W M₆)

/-- True all-log joint geometric growth under actual C2 and finite generation. -/
theorem productCoeff_joint_geometric (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₅.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) (k l j : ℕ)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 1 < ρ₁) (hρ₂ : 1 < ρ₂) :
    ∃ G : ℝ, ∀ m n : ℕ,
      ‖LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
        (a+m) (b-m+n) (c-n) k l j‖ ≤ G*ρ₁^m*ρ₂^n := by
  let a₀ := a₁+a₂+a₃+a₄-a-b-c-3
  obtain ⟨h₀,n₀,he₀,hl₀⟩ := exists_cosetBase N₀.toGW a₀
  obtain ⟨h₁,n₁,he₁,hl₁⟩ := exists_cosetBase N₁.toGW a₁
  obtain ⟨h₂,n₂,he₂,hl₂⟩ := exists_cosetBase N₂.toGW a₂
  obtain ⟨h₃,n₃,he₃,hl₃⟩ := exists_cosetBase N₃.toGW a₃
  obtain ⟨h₄,n₄,he₄,hl₄⟩ := exists_cosetBase N₄.toGW a₄
  have hx' : x ∈ N₁.weight (h₁+n₁) := he₁ ▸ hx
  have hy' : y ∈ N₂.weight (h₂+n₂) := he₂ ▸ hy
  have hz' : z ∈ N₃.weight (h₃+n₃) := he₃ ▸ hz
  have hw' : w ∈ N₄.weight (h₄+n₄) := he₄ ▸ hw
  let C := h₁+h₂+h₃+h₄-h₀-3
  let s := n₀+n₁+n₂+n₃+n₄
  let ν₀ := C-2*(n₀ : ℂ)-a
  let μ₀ := ν₀-b
  obtain ⟨K,L,hB⟩ := exists_uniformTwoBase_family
    (fun q => logCoefficient_isGradedJacobi Y₂.2 q)
    (fun q => logCoefficient_isGradedJacobi Y₃.2 q) h₂ h₃ h₄ ν₀ μ₀
  let Q := logNormalizedSeries Y₁.1 Y₂.1 Y₃.1 C (ν₀+K) (μ₀+L) f x y z w n₀ s k l j
  have hcoef : ∀ m n : ℕ, c2 Q m n =
      LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
        (a-K+m) (b+K-m+(((n : ℤ)-L : ℤ) : ℂ))
        (c-(((n : ℤ)-L : ℤ) : ℂ)) k l j := by
    intro m n
    dsimp only [Q,logNormalizedSeries]
    rw [c2_normalizedSeries]
    unfold normalizedCoeff
    change productCoeff (fun q => Y₁.1 q k) (fun q => Y₂.1 q l) (fun q => Y₃.1 q j)
      f x y z w _ _ _ = productCoeff (fun q => Y₁.1 q k)
        (fun q => Y₂.1 q l) (fun q => Y₃.1 q j) f x y z w _ _ _
    congr 1
    · dsimp only [ν₀]; ring
    · dsimp only [μ₀]; push_cast; ring
    · dsimp only [μ₀,ν₀,s,C,a₀] at *
      push_cast
      linear_combination he₀-he₁-he₂-he₃-he₄
  obtain ⟨sd,g,hs1,hgb,heq⟩ := innerRegular_logNormalizedSeries N₀ N₁ N₂ N₃ N₄ N₅ N₆
    hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ Y₂ Y₃ hl₀ hl₁ hl₂ hl₃ hl₄ hB
    f hx' hy' hz' hw' k l j 0
  obtain ⟨R,hR1,hRρ₁,hRρ₂⟩ :
      ∃ R : ℝ,1<R ∧ R<ρ₁ ∧ R<ρ₂ := by
    refine ⟨min ((1+ρ₁)/2) ((1+ρ₂)/2),
      lt_min (by linarith) (by linarith),
      lt_of_le_of_lt (min_le_left _ _) (by linarith),
      lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  obtain ⟨G,hG⟩ := hgb R hR1
  have hg' : ∀ q < sd, ∀ m n, ‖g q m n‖ ≤ max G 0*R^m*R^n := by
    intro q hq m n
    refine le_trans (hG q hq m n) ?_
    have hR : 0 ≤ R^m*R^n := by positivity
    rw [mul_assoc,mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hR
  have hrows : ∀ n, ∃ G' : ℝ, ∀ m, ‖c2 Q m n‖ ≤ G'*ρ₁^m := by
    intro n
    obtain ⟨G',hG'0,hG'⟩ := LogAssocFivePoint.product_row_geometric
      N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ Y₂ Y₃ hC2 hfg₀ hfg₁ hfg₂ hfg₅ hfg₆
      hx hy hz hw f a b c k l j K ((n : ℤ)-L) hρ₁
    exact ⟨G',fun m => by rw [hcoef]; exact hG' m⟩
  have heq' : VOA.Huang.UniformConv.DiagonalFuchsian (fun _ n => (0 : ℂ)+n) sd g (c2 Q) := heq
  obtain ⟨G₀,hG₀⟩ := geometric_of_rowFuchsian hs1 (by linarith) (by linarith)
    hRρ₁ hRρ₂ hg' heq' hrows
  refine ⟨G₀*ρ₁^K*ρ₂^L,fun m n => ?_⟩
  have he : LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j = c2 Q (m+K) (n+L) := by
    rw [hcoef]
    congr 1
    · push_cast; ring
    · push_cast; ring
    · push_cast; ring
  rw [he]
  calc
    ‖c2 Q (m+K) (n+L)‖ ≤ G₀*ρ₁^(m+K)*ρ₂^(n+L) := hG₀ _ _
    _ = G₀*ρ₁^K*ρ₂^L*ρ₁^m*ρ₂^n := by rw [pow_add,pow_add]; ring

end VOA.Huang.LogAssocFivePointGraded
