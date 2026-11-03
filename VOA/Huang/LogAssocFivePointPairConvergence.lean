import VOA.Huang.LogAssocFivePointPairJointGrowth
import VOA.Huang.LogAssocFivePointMidConvergence
import VOA.Huang.HuangODEThreeGrowth

/-! Absolute double convergence and genuine Fubini for every original log
coefficient and the full finite logarithmic polynomial. -/
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

variable (hC2 : C2Cofinite W)
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
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ)
include hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfgU hfgV hx hy hz hw

/-- Every genuine log triple converges absolutely over both internal levels. -/
theorem summable_pair_double (k l j : ℕ) {t u : ℂ} (ht : ‖t‖+‖t‖*‖u‖ < 1) (hu : ‖u‖ < 1) :
    Summable (fun q : ℕ × ℕ =>
      ‖pairCoeff P.1 ZT.1 XY.1 f x y z w
        (a+q.1) (b-q.1+q.2) (c-q.2) k l j*t^q.1*u^q.2‖) := by
  let C : ℕ → ℕ → ℂ := fun m n =>
    pairCoeff P.1 ZT.1 XY.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j
  obtain ⟨R₁,R₂,hAdm,hR₁,hR₂⟩ := exists_mid_rates (norm_nonneg t) (norm_nonneg u) hu ht
  obtain ⟨G,hG⟩ := pairCoeff_joint_geometric N₀ N₁ N₂ N₃ N₄ NU NV
    hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfgU hfgV P ZT XY hx hy hz hw f a b c k l j hAdm.1 hAdm.2
  have hG0 : 0≤G := le_trans (norm_nonneg _) (by simpa only [pow_zero,mul_one] using hG 0 0)
  have hR₁0 : 0≤R₁ := le_of_lt (lt_trans zero_lt_one hAdm.one_lt₁)
  have hR₂0 : 0≤R₂ := le_of_lt (lt_trans zero_lt_one hAdm.1)
  have hs := ((summable_geometric_of_lt_one
      (mul_nonneg (le_of_lt (lt_trans zero_lt_one hAdm.one_lt₁)) (norm_nonneg t)) hR₁).mul_of_nonneg
      (summable_geometric_of_lt_one
        (mul_nonneg (le_of_lt (lt_trans zero_lt_one hAdm.1)) (norm_nonneg u)) hR₂)
      (fun _ => by positivity) (fun _ => by positivity)).mul_left G
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro q
  simp only [norm_mul,norm_pow]
  calc
    _ ≤ (G*R₁^q.1*R₂^q.2)*‖t‖^q.1*‖u‖^q.2 := by
      gcongr
      exact hG q.1 q.2
    _ = G*((R₁*‖t‖)^q.1*(R₂*‖u‖)^q.2) := by rw [mul_pow,mul_pow]; ring

/-- The two actual internal coefficient sums can be interchanged. -/
theorem pair_double_tsum_comm (k l j : ℕ) {t u : ℂ} (ht : ‖t‖+‖t‖*‖u‖ < 1) (hu : ‖u‖ < 1) :
    (∑' m : ℕ, ∑' n : ℕ, pairCoeff P.1 ZT.1 XY.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j*t^m*u^n) =
    ∑' n : ℕ, ∑' m : ℕ, pairCoeff P.1 ZT.1 XY.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j*t^m*u^n := by
  have hs := summable_pair_double N₀ N₁ N₂ N₃ N₄ NU NV hC2
    hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfgU hfgV P ZT XY hx hy hz hw f a b c k l j ht hu
  exact hs.of_norm.tsum_comm.symm

omit hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfgU hfgV hx hy hz hw in
/-- The literal full logarithmic polynomial, without selecting its log-free part. -/
def fullLogPairCoefficient (e₁ e₂ e₃ : ℂ) (m n : ℕ) : ℂ :=
  ∑ᶠ p : ℕ × ℕ × ℕ,
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*
      pairCoeff P.1 ZT.1 XY.1 f x y z w
        (a+m) (b-m+n) (c-n) p.1 p.2.1 p.2.2

/-- The complete actual logarithmic polynomial also has absolute joint
convergence, since genuine global Jordan bounds supply a finite log box. -/
theorem summable_fullLog_pair_double (e₁ e₂ e₃ : ℂ) {t u : ℂ}
    (ht : ‖t‖+‖t‖*‖u‖ < 1) (hu : ‖u‖ < 1) :
    Summable (fun q : ℕ × ℕ =>
      ‖fullLogPairCoefficient N₀ N₁ N₂ N₃ N₄ NU NV P ZT XY
        (x := x) (y := y) (z := z) (w := w) f a b c e₁ e₂ e₃ q.1 q.2*t^q.1*u^q.2‖) := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen NU NV N₀ hfgU hfgV hfg₀
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₂ N₁ NV hfg₂ hfg₁ hfgV
  obtain ⟨J,hJ⟩ := uniform_log_degree_of_finGen N₃ N₄ NU hfg₃ hfg₄ hfgU
  have hcut (p q r : ℂ) (k l j : ℕ) (h : K≤k ∨ L≤l ∨ J≤j) :
      pairCoeff P.1 ZT.1 XY.1 f x y z w p q r k l j=0 := by
    rcases h with hk | hl | hj
    · simp only [pairCoeff,hK P p k hk,LinearMap.zero_apply,map_zero]
    · simp only [pairCoeff,hL ZT q l hl,
        LinearMap.zero_apply,map_zero]
    · simp only [pairCoeff,hJ XY r j hj,
        LinearMap.zero_apply,map_zero]
  let S : Finset (ℕ × ℕ × ℕ) := (Finset.range K) ×ˢ (Finset.range L) ×ˢ (Finset.range J)
  let C : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℂ := fun m n p =>
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*
      pairCoeff P.1 ZT.1 XY.1 f x y z w
        (a+m) (b-m+n) (c-n) p.1 p.2.1 p.2.2
  have hzero (m n : ℕ) (p : ℕ × ℕ × ℕ) (hp : p ∉ S) : C m n p=0 := by
    have houtside : K ≤ p.1 ∨ L ≤ p.2.1 ∨ J ≤ p.2.2 := by
      simp only [S,Finset.mem_product,Finset.mem_range] at hp
      omega
    dsimp only [C]
    rw [hcut _ _ _ _ _ _ houtside,mul_zero]
  have he (m n : ℕ) : fullLogPairCoefficient N₀ N₁ N₂ N₃ N₄ NU NV
      P ZT XY (x := x) (y := y) (z := z) (w := w) f a b c e₁ e₂ e₃ m n = ∑ p ∈ S,C m n p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    by_contra hn
    exact hp (hzero m n p hn)
  have hs (p : ℕ × ℕ × ℕ) :
      Summable (fun q : ℕ × ℕ => ‖C q.1 q.2 p*t^q.1*u^q.2‖) := by
    have hh := (summable_pair_double N₀ N₁ N₂ N₃ N₄ NU NV hC2
      hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfgU hfgV P ZT XY hx hy hz hw f a b c
        p.1 p.2.1 p.2.2 ht hu).mul_left ‖e₁^p.1*e₂^p.2.1*e₃^p.2.2‖
    refine hh.congr fun q => ?_
    simp only [C,norm_mul,mul_assoc]
  have hsum := summable_sum (fun p (hp : p ∈ S) => hs p)
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ hsum
  intro q
  rw [he]
  simp only [Finset.sum_mul]
  exact norm_sum_le _ _

end VOA.Huang.LogAssocFivePointGraded
