import VOA.Huang.LogAssocFivePointPairInnerRegular
import VOA.Huang.LogAssocFivePointPairRows
import VOA.Huang.LogAssocFivePointMidJointGrowth

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
variable {V M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]
variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (NU : LogVModule W MU) (NV : LogVModule W MV)

/-- True all-log joint geometric growth under actual C2 and finite generation. -/
theorem pairCoeff_joint_geometric (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfgU : FinGen NU.toWeakModule)
    (hfgV : FinGen NV.toWeakModule)
    (P : LogIntertwiningOperator NU.toWeakModule NV.toWeakModule N₀.toWeakModule)
    (ZT : LogIntertwiningOperator N₂.toWeakModule N₁.toWeakModule NV.toWeakModule)
    (XY : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule NU.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) (k l j : ℕ)
    {ρ₁ ρ₂ : ℝ} (hρ₂ : 1 < ρ₂) (hρ : 1+1/ρ₂ < ρ₁) :
    ∃ G : ℝ, ∀ m n : ℕ,
      ‖pairCoeff P.1 ZT.1 XY.1 f x y z w
        (a+m) (b-m+n) (c-n) k l j‖ ≤ G*ρ₁^m*ρ₂^n := by
  have hρ₁ : 1<ρ₁ := by
    have hρ₂0 : 0<ρ₂ := by linarith
    have hpos : 0≤1/ρ₂ := by positivity
    linarith
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
  obtain ⟨K,L,hB⟩ := exists_pairBase_family (P := P.1)
    (fun q => logCoefficient_isGradedJacobi ZT.2 q)
    (fun q => logCoefficient_isGradedJacobi XY.2 q) h₁ h₂ h₃ h₄ ν₀ μ₀
  let Q := logPairNormalizedSeries P.1 ZT.1 XY.1 C (ν₀+K) (μ₀+L) f x y z w n₀ s k l j
  have hcoef : ∀ m n : ℕ, c2 Q m n =
      pairCoeff P.1 ZT.1 XY.1 f x y z w
        (a-K+m) (b+K-m+(((n : ℤ)-L : ℤ) : ℂ))
        (c-(((n : ℤ)-L : ℤ) : ℂ)) k l j := by
    intro m n
    dsimp only [Q,logPairNormalizedSeries]
    rw [c2_normalizedSeries]
    unfold normalizedCoeff
    change pairCoeff P.1 ZT.1 XY.1 f x y z w _ _ _ k l j =
      pairCoeff P.1 ZT.1 XY.1 f x y z w _ _ _ k l j
    congr 1
    · dsimp only [ν₀]; ring
    · dsimp only [μ₀]; push_cast; ring
    · dsimp only [μ₀,ν₀,s,C,a₀] at *
      push_cast
      linear_combination he₀-he₁-he₂-he₃-he₄
  obtain ⟨sd,g,hs1,hgb,heq⟩ := innerRegularPair_logNormalizedSeries N₀ N₁ N₂ N₃ N₄ NU NV
    hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfgU hfgV P ZT XY hl₀ hl₁ hl₂ hl₃ hl₄ hB
    f hx' hy' hz' hw' k l j 0
  obtain ⟨R₁,R₂,hRAdm,hRρ₁,hRρ₂⟩ := exists_midAdm_below hρ₂ hρ
  obtain ⟨G,hG⟩ := hgb R₁ R₂ hRAdm
  have hg' : ∀ q < sd, ∀ m n, ‖g q m n‖ ≤ max G 0*R₁^m*R₂^n := by
    intro q hq m n
    refine le_trans (hG q hq m n) ?_
    have hR : 0 ≤ R₁^m*R₂^n := by
      have h1 := hRAdm.one_lt₁
      have h2 := hRAdm.1
      positivity
    rw [mul_assoc,mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hR
  have hrows : ∀ n, ∃ G' : ℝ, ∀ m, ‖c2 Q m n‖ ≤ G'*ρ₁^m := by
    intro n
    obtain ⟨G',hG'0,hG'⟩ := pair_row_geometric
      N₀ N₁ N₂ N₃ N₄ NU NV P ZT XY hC2 hfg₀ hfg₁ hfg₂ hfgU hfgV
      hx hy hz hw f a b c k l j K ((n : ℤ)-L) hρ₁
    exact ⟨G',fun m => by rw [hcoef]; exact hG' m⟩
  have heq' : VOA.Huang.UniformConv.DiagonalFuchsian (fun _ n => (0 : ℂ)+n) sd g (c2 Q) := heq
  obtain ⟨G₀,hG₀⟩ := geometric_of_rowFuchsian hs1
    (le_trans (by norm_num) (le_of_lt hRAdm.one_lt₁))
    (le_trans (by norm_num) (le_of_lt hRAdm.1)) hRρ₁ hRρ₂ hg' heq' hrows
  refine ⟨G₀*ρ₁^K*ρ₂^L,fun m n => ?_⟩
  have he : pairCoeff P.1 ZT.1 XY.1 f x y z w
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
