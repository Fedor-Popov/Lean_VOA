import VOA.Huang.LogAssocFivePointMidJointGrowth
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
variable {V M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable (N₀ : LogVModule W M₀) (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (N₃ : LogVModule W M₃) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅) (N₆ : LogVModule W M₆)

/-- Geometric rates strictly inside the actual middle collision chart. -/
theorem exists_mid_rates {t u : ℝ} (ht0 : 0≤t) (hu0 : 0≤u) (hu1 : u<1)
    (hchart : t+t*u<1) :
    ∃ R₁ R₂ : ℝ, MidAdm R₁ R₂ ∧ R₁*t<1 ∧ R₂*u<1 := by
  by_cases ht : t=0
  · obtain ⟨v,hv,hv1⟩ := exists_between hu1
    have hv0 : 0<v := lt_of_le_of_lt hu0 hv
    refine ⟨2+v,v⁻¹,⟨(one_lt_inv₀ hv0).mpr hv1,?_⟩,by simp [ht],?_⟩
    · rw [one_div,inv_inv]
      linarith
    · rw [inv_mul_eq_div,div_lt_one hv0]
      exact hv
  · have htpos : 0<t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have htv : u<t⁻¹-1 := by
      rw [inv_eq_one_div]
      apply (lt_sub_iff_add_lt).mpr
      apply (lt_div_iff₀ htpos).mpr
      nlinarith
    obtain ⟨v,hv,hvmax⟩ := exists_between (lt_min hu1 htv)
    have hv0 : 0<v := lt_of_le_of_lt hu0 hv
    have hv1 : v<1 := lt_of_lt_of_le hvmax (min_le_left _ _)
    have hvt : 1+v<t⁻¹ := by
      have := lt_of_lt_of_le hvmax (min_le_right _ _)
      linarith
    obtain ⟨R₁,hRlow,hRhigh⟩ := exists_between hvt
    refine ⟨R₁,v⁻¹,⟨(one_lt_inv₀ hv0).mpr hv1,?_⟩,?_,?_⟩
    · rw [one_div,inv_inv]
      exact hRlow
    · rw [inv_eq_one_div] at hRhigh
      exact (lt_div_iff₀ htpos).mp hRhigh
    · rw [inv_mul_eq_div,div_lt_one hv0]
      exact hv

variable (hC2 : C2Cofinite W)
    (hfg₀ : FinGen N₀.toWeakModule) (hfg₁ : FinGen N₁.toWeakModule)
    (hfg₂ : FinGen N₂.toWeakModule) (hfg₃ : FinGen N₃.toWeakModule)
    (hfg₄ : FinGen N₄.toWeakModule) (hfg₅ : FinGen N₅.toWeakModule)
    (hfg₆ : FinGen N₆.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₆.toWeakModule N₀.toWeakModule)
    (YB : LogIntertwiningOperator N₅.toWeakModule N₂.toWeakModule N₆.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₃.toWeakModule N₄.toWeakModule N₅.toWeakModule)
    {a₁ a₂ a₃ a₄ : ℂ} {x : M₁} {y : M₂} {z : M₃} {w : M₄}
    (hx : x ∈ N₁.weight a₁) (hy : y ∈ N₂.weight a₂)
    (hz : z ∈ N₃.weight a₃) (hw : w ∈ N₄.weight a₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ)
include hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ hx hy hz hw

/-- Every genuine log triple converges absolutely over both internal levels. -/
theorem summable_mid_double (k l j : ℕ) {t u : ℂ} (ht : ‖t‖+‖t‖*‖u‖ < 1) (hu : ‖u‖ < 1) :
    Summable (fun q : ℕ × ℕ =>
      ‖LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
        (a+q.1) (b-q.1+q.2) (c-q.2) k l j*t^q.1*u^q.2‖) := by
  let C : ℕ → ℕ → ℂ := fun m n =>
    LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j
  obtain ⟨R₁,R₂,hAdm,hR₁,hR₂⟩ := exists_mid_rates (norm_nonneg t) (norm_nonneg u) hu ht
  obtain ⟨G,hG⟩ := midCoeff_joint_geometric N₀ N₁ N₂ N₃ N₄ N₅ N₆
    hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ YB Y₃ hx hy hz hw f a b c k l j hAdm.1 hAdm.2
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
theorem mid_double_tsum_comm (k l j : ℕ) {t u : ℂ} (ht : ‖t‖+‖t‖*‖u‖ < 1) (hu : ‖u‖ < 1) :
    (∑' m : ℕ, ∑' n : ℕ, LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j*t^m*u^n) =
    ∑' n : ℕ, ∑' m : ℕ, LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j*t^m*u^n := by
  have hs := summable_mid_double N₀ N₁ N₂ N₃ N₄ N₅ N₆ hC2
    hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ YB Y₃ hx hy hz hw f a b c k l j ht hu
  exact hs.of_norm.tsum_comm.symm

omit hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ hx hy hz hw in
/-- The literal full logarithmic polynomial, without selecting its log-free part. -/
def fullLogMidProductCoefficient (e₁ e₂ e₃ : ℂ) (m n : ℕ) : ℂ :=
  ∑ᶠ p : ℕ × ℕ × ℕ,
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*
      LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
        (a+m) (b-m+n) (c-n) p.1 p.2.1 p.2.2

/-- The complete actual logarithmic polynomial also has absolute joint
convergence, since genuine global Jordan bounds supply a finite log box. -/
theorem summable_fullLog_mid_double (e₁ e₂ e₃ : ℂ) {t u : ℂ}
    (ht : ‖t‖+‖t‖*‖u‖ < 1) (hu : ‖u‖ < 1) :
    Summable (fun q : ℕ × ℕ =>
      ‖fullLogMidProductCoefficient N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ YB Y₃
        (x := x) (y := y) (z := z) (w := w) f a b c e₁ e₂ e₃ q.1 q.2*t^q.1*u^q.2‖) := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₆ N₀ hfg₁ hfg₆ hfg₀
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₅ N₂ N₆ hfg₅ hfg₂ hfg₆
  obtain ⟨J,hJ⟩ := uniform_log_degree_of_finGen N₃ N₄ N₅ hfg₃ hfg₄ hfg₅
  have hcut (p q r : ℂ) (k l j : ℕ) (h : K≤k ∨ L≤l ∨ J≤j) :
      LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w p q r k l j=0 := by
    rcases h with hk | hl | hj
    · simp only [LogAssocFivePoint.productCoeff,hK Y₁ p k hk,LinearMap.zero_apply,map_zero]
    · simp only [LogAssocFivePoint.productCoeff,flipLogModes,hL YB q l hl,
        LinearMap.flip_apply,LinearMap.zero_apply,map_zero]
    · simp only [LogAssocFivePoint.productCoeff,flipLogModes,hJ Y₃ r j hj,
        LinearMap.flip_apply,LinearMap.zero_apply,map_zero]
  let S : Finset (ℕ × ℕ × ℕ) := (Finset.range K) ×ˢ (Finset.range L) ×ˢ (Finset.range J)
  let C : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℂ := fun m n p =>
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*
      LogAssocFivePoint.productCoeff Y₁.1 (flipLogModes YB.1) Y₃.1 f x y z w
        (a+m) (b-m+n) (c-n) p.1 p.2.1 p.2.2
  have hzero (m n : ℕ) (p : ℕ × ℕ × ℕ) (hp : p ∉ S) : C m n p=0 := by
    have houtside : K ≤ p.1 ∨ L ≤ p.2.1 ∨ J ≤ p.2.2 := by
      simp only [S,Finset.mem_product,Finset.mem_range] at hp
      omega
    dsimp only [C]
    rw [hcut _ _ _ _ _ _ houtside,mul_zero]
  have he (m n : ℕ) : fullLogMidProductCoefficient N₀ N₁ N₂ N₃ N₄ N₅ N₆
      Y₁ YB Y₃ (x := x) (y := y) (z := z) (w := w) f a b c e₁ e₂ e₃ m n = ∑ p ∈ S,C m n p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    by_contra hn
    exact hp (hzero m n p hn)
  have hs (p : ℕ × ℕ × ℕ) :
      Summable (fun q : ℕ × ℕ => ‖C q.1 q.2 p*t^q.1*u^q.2‖) := by
    have hh := (summable_mid_double N₀ N₁ N₂ N₃ N₄ N₅ N₆ hC2
      hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ YB Y₃ hx hy hz hw f a b c
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
