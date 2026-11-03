import VOA.Huang.LogAssocCoefficients

/-! The genuine coupled outer logarithmic derivative of a collision product.
Each degree k retains the actual degree-(k+1) correction until the entire
finite logarithmic sum is differentiated. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor PowerSeries VOA.Huang.AssocExpansion
open VOA.Huang.HuangODEIterPoint VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.MatrixCoeff VOA.Huang.Convergence
open scoped BigOperators Topology
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable {A₁ : WeakModule W M₁} {A₅ : WeakModule W M₅} {A₄ : WeakModule W M₄}
variable (Y₁ : LogIntertwiningOperator A₁ A₅ A₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
  (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (S ν : ℂ)

/-- The exact outer derivative has its full logarithmic successor term. -/
theorem prodCoeff_LogLm1_left (n₁ n₂ : ℂ) (k : ℕ) :
    prodCoeff (fun n => Y₁.1 n k) Y₂ f (Lm1 A₁ x) y z n₁ n₂ =
      -n₁ * prodCoeff (fun n => Y₁.1 n k) Y₂ f x y z (n₁-1) n₂ +
      ((k:ℂ)+1) * prodCoeff (fun n => Y₁.1 n (k+1)) Y₂ f x y z (n₁-1) n₂ := by
  simp only [prodCoeff,Y₁.2.L_neg_one,LinearMap.add_apply,LinearMap.smul_apply,
    map_add,map_smul,smul_eq_mul]

/-- The exact power-series identity underlying the coupled logarithmic derivative. -/
theorem prodSeries_LogLm1_left (k : ℕ) :
    prodSeries (fun n => Y₁.1 n k) Y₂ f (Lm1 A₁ x) y z (S+1) ν =
      -(VOA.theta (prodSeries (fun n => Y₁.1 n k) Y₂ f x y z S ν) +
        PowerSeries.C (S-ν+1) * prodSeries (fun n => Y₁.1 n k) Y₂ f x y z S ν) +
      ((k:ℂ)+1) • prodSeries (fun n => Y₁.1 n (k+1)) Y₂ f x y z S ν := by
  ext q
  rw [map_add,map_neg,map_add,VOA.theta_coeff,coeff_C_mul,map_smul]
  simp only [coeff_prodSeries]
  rw [prodCoeff_LogLm1_left]
  rw [show S+1-ν+q-1=S-ν+q by ring]
  simp only [smul_eq_mul]
  ring

/-- Genuine coupled outer derivative preserves subexponential convergence. -/
theorem prodSeries_LogLm1_left_mem (k : ℕ)
    (hG : prodSeries (fun n => Y₁.1 n k) Y₂ f x y z S ν ∈ SubexpPS)
    (hGnext : prodSeries (fun n => Y₁.1 n (k+1)) Y₂ f x y z S ν ∈ SubexpPS) :
    prodSeries (fun n => Y₁.1 n k) Y₂ f (Lm1 A₁ x) y z (S+1) ν ∈ SubexpPS := by
  rw [prodSeries_LogLm1_left]
  exact SubexpPS.add_mem (SubexpPS.neg_mem (SubexpPS.add_mem
    (theta_mem_subexpPS hG) (SubexpPS.mul_mem (C_mem_subexp _) hG)))
    (SubexpPS.smul_mem hGnext _)

/-- At each actual log degree, differentiation retains the successor correction. -/
theorem hasDerivAt_prodFun_log (k : ℕ)
    (hG : prodSeries (fun n => Y₁.1 n k) Y₂ f x y z S ν ∈ SubexpPS)
    (hGnext : prodSeries (fun n => Y₁.1 n (k+1)) Y₂ f x y z S ν ∈ SubexpPS)
    {t : ℂ} (ht : t∈overlapDomain) :
    HasDerivAt (prodFun (fun n => Y₁.1 n k) Y₂ f x y z S ν)
      (Complex.exp t * (prodFun (fun n => Y₁.1 n k) Y₂ f (Lm1 A₁ x) y z (S+1) ν t -
        ((k:ℂ)+1) * xt t * prodFun (fun n => Y₁.1 n (k+1)) Y₂ f x y z S ν t)) t := by
  let G := prodSeries (fun n => Y₁.1 n k) Y₂ f x y z S ν
  let κ := S-ν+1
  have hEv : ∀ q∈overlapDomain, prodFun (fun n => Y₁.1 n k) Y₂ f x y z S ν q=Ev κ 0 G q := by
    intro q hq
    simpa only [κ,G,Nat.cast_zero,sub_zero,pow_zero,one_mul] using
      prodFun_eq_Ev (fun n => Y₁.1 n k) Y₂ f x y z S ν 0 0 hG hq
  have hev : prodFun (fun n => Y₁.1 n k) Y₂ f x y z S ν =ᶠ[𝓝 t] Ev κ 0 G :=
    Filter.eventually_of_mem (isOpen_overlapDomain.mem_nhds ht) hEv
  refine (hasDerivAt_Ev κ 0 hG ht).congr_of_eventuallyEq hev |>.congr_deriv ?_
  have hL := prodFun_eq_Ev (fun n => Y₁.1 n k) Y₂ f (Lm1 A₁ x) y z (S+1) ν 0 0
    (prodSeries_LogLm1_left_mem Y₁ Y₂ f x y z S ν k hG hGnext) ht
  have hnext := prodFun_eq_Ev (fun n => Y₁.1 n (k+1)) Y₂ f x y z S ν 0 0 hGnext ht
  simp only [pow_zero,one_mul,Nat.cast_zero,sub_zero] at hL hnext
  rw [hL,hnext,prodSeries_LogLm1_left]
  have hz := one_add_exp_ne_zero ht
  have hy := norm_xt_lt_one ht
  have hθ := theta_mem_subexpPS hG
  have hκG := SubexpPS.mul_mem (C_mem_subexp κ) hG
  have h1x : 1-xt t=Complex.exp t*xt t := by
    simp only [xt]; field_simp; ring
  have hcp : (1+Complex.exp t)^(-(S+1-ν+1)) = (1+Complex.exp t)^(-κ)*xt t := by
    rw [show -(S+1-ν+1)=-κ-1 by dsimp [κ]; ring,
      Complex.cpow_sub _ _ hz,Complex.cpow_one,xt,div_eq_mul_inv]
  simp only [Ev,zero_mul,neg_zero,Complex.exp_zero,one_mul]
  rw [psEval_DOp κ 0 hG hy,psEval_add (SubexpPS.neg_mem (SubexpPS.add_mem hθ hκG))
    (SubexpPS.smul_mem hGnext _) hy,psEval_neg,psEval_add hθ hκG hy,
    psEval_C_mul,psEval_smul,hcp,h1x]
  simp only [zero_mul,sub_zero,κ,G,smul_eq_mul]
  ring

end VOA.Huang.LogAssocCoefficientL0
