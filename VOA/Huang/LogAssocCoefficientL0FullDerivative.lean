import VOA.Huang.LogAssocCoefficientL0Derivative

/-! Differentiating the entire actual finite logarithmic product.
The coupled successor term cancels exactly with the derivative of the
outer logarithm after the finite sum is assembled. -/
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

/-- The exact finite successor cancellation, including the true terminal bound. -/
theorem finite_log_successor_cancel (L : ℂ) (F : ℕ → ℂ) (K : ℕ) (hK : F K=0) :
    (∑ k∈Finset.range K,(k:ℂ)*L^(k-1)*F k) =
      ∑ k∈Finset.range K,((k:ℂ)+1)*L^k*F (k+1) := by
  have hs := Finset.sum_range_succ' (fun k : ℕ => (k:ℂ)*L^(k-1)*F k) K
  rw [Finset.sum_range_succ] at hs
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Nat.cast_zero,zero_mul,hK,mul_zero,add_zero] at hs
  exact hs

/-- The genuine finite all-log product on a one-sided actual mode coset. -/
noncomputable def fullNatProduct
    (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (S ν : ℂ) (K : ℕ) (t : ℂ) : ℂ :=
  ∑ k∈Finset.range K,Complex.log (1+Complex.exp t)^k *
    prodFun (fun n => Y₁ n k) Y₂ f x y z S ν t

variable {A₁ : WeakModule W M₁} {A₅ : WeakModule W M₅} {A₄ : WeakModule W M₄}
variable (Y₁ : LogIntertwiningOperator A₁ A₅ A₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
  (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (S ν : ℂ)

/-- The actual finite all-log product satisfies the genuine source derivative.
No individual logarithmic coefficient is assigned an ordinary derivative law. -/
theorem hasDerivAt_fullNatProduct (K : ℕ) (hK : ∀ n,Y₁.1 n K=0)
    (hG : ∀ k,prodSeries (fun n => Y₁.1 n k) Y₂ f x y z S ν ∈ SubexpPS)
    {t : ℂ} (ht : t∈overlapDomain) :
    HasDerivAt (fullNatProduct Y₁.1 Y₂ f x y z S ν K)
      (Complex.exp t * fullNatProduct Y₁.1 Y₂ f (Lm1 A₁ x) y z (S+1) ν K t) t := by
  let L : ℂ := Complex.log (1+Complex.exp t)
  let F : ℕ → ℂ := fun k => prodFun (fun n => Y₁.1 n k) Y₂ f x y z S ν t
  let G : ℕ → ℂ := fun k => prodFun (fun n => Y₁.1 n k) Y₂ f (Lm1 A₁ x) y z (S+1) ν t
  have hd : HasDerivAt (fun t => 1+Complex.exp t) (Complex.exp t) t :=
    (Complex.hasDerivAt_exp t).const_add 1
  have hlog := hd.clog (one_add_exp_mem_slitPlane ht)
  have hterm (k : ℕ) : HasDerivAt
      (fun q => Complex.log (1+Complex.exp q)^k * prodFun (fun n => Y₁.1 n k) Y₂ f x y z S ν q)
      ((k:ℂ)*L^(k-1)*(Complex.exp t/(1+Complex.exp t))*F k +
        L^k*(Complex.exp t*(G k-((k:ℂ)+1)*xt t*F (k+1)))) t := by
    exact (hlog.pow k).mul (hasDerivAt_prodFun_log Y₁ Y₂ f x y z S ν k (hG k) (hG (k+1)) ht)
  have H := HasDerivAt.fun_sum (u := Finset.range K) (fun k _ => hterm k)
  refine H.congr_deriv ?_
  have hz := one_add_exp_ne_zero ht
  have hFK : F K=0 := by
    simp only [F,prodFun,VOA.Huang.AssocTarget.prodValue,prodCoeff,hK,LinearMap.zero_apply,map_zero,
      zero_mul,tsum_zero]
  have hc := finite_log_successor_cancel L F K hFK
  change (∑ k∈Finset.range K,((k:ℂ)*L^(k-1)*(Complex.exp t/(1+Complex.exp t))*F k +
    L^k*(Complex.exp t*(G k-((k:ℂ)+1)*xt t*F (k+1))))) =
      Complex.exp t * ∑ k∈Finset.range K,L^k*G k
  have he : (∑ k∈Finset.range K,((k:ℂ)*L^(k-1)*(Complex.exp t/(1+Complex.exp t))*F k +
    L^k*(Complex.exp t*(G k-((k:ℂ)+1)*xt t*F (k+1))))) =
    Complex.exp t*(∑ k∈Finset.range K,L^k*G k) +
      (Complex.exp t/(1+Complex.exp t)) *
        ((∑ k∈Finset.range K,(k:ℂ)*L^(k-1)*F k)-
          ∑ k∈Finset.range K,((k:ℂ)+1)*L^k*F (k+1)) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [xt]
    ring
  rw [he,hc,sub_self,mul_zero,add_zero]

end VOA.Huang.LogAssocCoefficientL0
