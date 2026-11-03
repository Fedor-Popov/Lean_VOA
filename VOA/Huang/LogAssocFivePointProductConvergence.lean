import VOA.Huang.LogAssocFivePointJointGrowth
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

variable (hC2 : C2Cofinite W)
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
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ)
include hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ hx hy hz hw

/-- Every genuine log triple converges absolutely over both internal levels. -/
theorem summable_product_double (k l j : ℕ) {t u : ℂ} (ht : ‖t‖ < 1) (hu : ‖u‖ < 1) :
    Summable (fun q : ℕ × ℕ =>
      ‖LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
        (a+q.1) (b-q.1+q.2) (c-q.2) k l j*t^q.1*u^q.2‖) := by
  let C : ℕ → ℕ → ℂ := fun m n =>
    LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j
  have hC : VOA.Huang.HuangODEThree.JointSubexponential C := by
    intro R hR
    obtain ⟨G,hG⟩ := productCoeff_joint_geometric N₀ N₁ N₂ N₃ N₄ N₅ N₆
      hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ Y₂ Y₃ hx hy hz hw f a b c k l j hR hR
    exact ⟨G,fun m n => by rw [pow_add]; simpa only [C,mul_assoc] using hG m n⟩
  exact VOA.Huang.HuangODEThree.summable_of_jointSubexponential hC ht hu

/-- The two actual internal coefficient sums can be interchanged. -/
theorem product_double_tsum_comm (k l j : ℕ) {t u : ℂ} (ht : ‖t‖ < 1) (hu : ‖u‖ < 1) :
    (∑' m : ℕ, ∑' n : ℕ, LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j*t^m*u^n) =
    ∑' n : ℕ, ∑' m : ℕ, LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
      (a+m) (b-m+n) (c-n) k l j*t^m*u^n := by
  have hs := summable_product_double N₀ N₁ N₂ N₃ N₄ N₅ N₆ hC2
    hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ Y₂ Y₃ hx hy hz hw f a b c k l j ht hu
  exact hs.of_norm.tsum_comm.symm

omit hC2 hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ hx hy hz hw in
/-- The literal full logarithmic polynomial, without selecting its log-free part. -/
def fullLogProductCoefficient (e₁ e₂ e₃ : ℂ) (m n : ℕ) : ℂ :=
  ∑ᶠ p : ℕ × ℕ × ℕ,
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*
      LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
        (a+m) (b-m+n) (c-n) p.1 p.2.1 p.2.2

/-- The complete actual logarithmic polynomial also has absolute joint
convergence, since genuine global Jordan bounds supply a finite log box. -/
theorem summable_fullLog_product_double (e₁ e₂ e₃ : ℂ) {t u : ℂ}
    (ht : ‖t‖ < 1) (hu : ‖u‖ < 1) :
    Summable (fun q : ℕ × ℕ =>
      ‖fullLogProductCoefficient N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ Y₂ Y₃
        (x := x) (y := y) (z := z) (w := w) f a b c e₁ e₂ e₃ q.1 q.2*t^q.1*u^q.2‖) := by
  classical
  obtain ⟨K,L,J,hcut⟩ := LogAssocFivePoint.exists_uniform_log_cutoffs
    N₀ N₁ N₂ N₃ N₄ N₅ N₆ Y₁ Y₂ Y₃ hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆
  let S : Finset (ℕ × ℕ × ℕ) := (Finset.range K) ×ˢ (Finset.range L) ×ˢ (Finset.range J)
  let C : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℂ := fun m n p =>
    (e₁^p.1*e₂^p.2.1*e₃^p.2.2)*
      LogAssocFivePoint.productCoeff Y₁.1 Y₂.1 Y₃.1 f x y z w
        (a+m) (b-m+n) (c-n) p.1 p.2.1 p.2.2
  have hzero (m n : ℕ) (p : ℕ × ℕ × ℕ) (hp : p ∉ S) : C m n p=0 := by
    have houtside : K ≤ p.1 ∨ L ≤ p.2.1 ∨ J ≤ p.2.2 := by
      simp only [S,Finset.mem_product,Finset.mem_range] at hp
      omega
    dsimp only [C]
    rw [hcut f x y z w _ _ _ _ _ _ houtside,mul_zero]
  have he (m n : ℕ) : fullLogProductCoefficient N₀ N₁ N₂ N₃ N₄ N₅ N₆
      Y₁ Y₂ Y₃ (x := x) (y := y) (z := z) (w := w) f a b c e₁ e₂ e₃ m n = ∑ p ∈ S,C m n p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    by_contra hn
    exact hp (hzero m n p hn)
  have hs (p : ℕ × ℕ × ℕ) :
      Summable (fun q : ℕ × ℕ => ‖C q.1 q.2 p*t^q.1*u^q.2‖) := by
    have hh := (summable_product_double N₀ N₁ N₂ N₃ N₄ N₅ N₆ hC2
      hfg₀ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ hfg₆ Y₁ Y₂ Y₃ hx hy hz hw f a b c
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
