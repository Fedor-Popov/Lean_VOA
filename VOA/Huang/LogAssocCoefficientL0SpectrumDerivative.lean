import VOA.Huang.LogAssocCoefficientL0FullDerivative

/-! The genuine source derivative of the complete intermediate spectrum.
Every logarithmic degree and actual integer mode coset is retained. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor PowerSeries VOA.Huang.AssocExpansion
open VOA.Huang.HuangODEIterPoint VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.MatrixCoeff VOA.Huang.Convergence
open VOA.Huang.LogAssocExpansion VOA.Huang.LogHuangODEProduct VOA.Huang.LogHuangODEIterPoint
open scoped BigOperators Topology
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
  (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- All genuine degreewise product series converge subexponentially. -/
theorem prodSeries_log_mem (S ν : ℂ) (k l : ℕ) :
    prodSeries (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) f x y z S ν ∈ SubexpPS := by
  apply subexp_of_summable_unitDisc
  intro t ht
  have hs := summable_log_product hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f x y z (S-ν) ν k l ht
  simpa only [coeff_prodSeries,prodCoeff] using hs

/-- Differentiation of the literal complete integer coset is the source L(-1) insertion. -/
theorem hasDerivAt_fullCoset (a b : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    HasDerivAt (logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b)
      (Complex.exp t * logProductFullCosetFun Y₁.1 Y₂.1 f (Lm1 N₁.toWeakModule x) y z (a+1) b t) t := by
  classical
  obtain ⟨R,hR⟩ := Y₂.2.truncation y z b
  let D := R.toNat
  have hb : IsBase (fun n => Y₂.1 n 0) y z (b+D) := by
    intro j
    have hj := hR ((D+j+1 : ℕ) : ℤ) (by dsimp [D]; omega) 0
    have he : b+D+((j:ℂ)+1)=b+(((D+j+1 : ℕ) : ℤ) : ℂ) := by push_cast; ring
    change Y₂.1 (b+D+((j:ℂ)+1)) 0 y z=0
    rw [he]
    exact hj
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hzero : ∀ n k,K≤k → Y₁.1 n k=0 := fun n k hk => hK Y₁ n k hk
  have he (w : M₁) (A q : ℂ) :
      logProductFullCosetFun Y₁.1 Y₂.1 f w y z A b q=
        fullNatProduct Y₁.1 (fun n => Y₂.1 n 0) f w y z (A+b) (b+D) K q := by
    rw [fullCoset_eq_sum_log Y₂.1 hzero]
    unfold fullNatProduct
    apply Finset.sum_congr rfl
    intro k hk
    unfold logProductIntegerCosetFun
    congr 1
    have hh := prodFunZ_shift (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0) f w y z (A+b) b (D:ℤ) q
    simp only [Int.cast_natCast] at hh
    rw [← hh,prodFunZ_eq_prodFun f w hb]
  have hnat := hasDerivAt_fullNatProduct Y₁ (fun n => Y₂.1 n 0) f x y z (a+b) (b+D) K
    (fun n => hzero n K le_rfl)
    (fun k => prodSeries_log_mem hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z (a+b) (b+D) k 0) ht
  have hf : logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b=
      fullNatProduct Y₁.1 (fun n => Y₂.1 n 0) f x y z (a+b) (b+D) K := funext (he x a)
  rw [hf]
  convert hnat using 1
  rw [he,show a+1+b=(a+b)+1 by ring]

/-- The finite sum of every actual intermediate spectral coset has the genuine derivative. -/
theorem hasDerivAt_spectrum (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    HasDerivAt (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β)
      (Complex.exp t * logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f
        (Lm1 N₁.toWeakModule x) y z (a+1) b c β t) t := by
  classical
  have H := HasDerivAt.fun_sum (u := spectrumCosets hC2 N₅ hfg₅) (fun mu _ =>
    hasDerivAt_fullCoset hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z
      (a+spectrumCosetRep hC2 N₅ hfg₅ mu-β-1) (b+c-spectrumCosetRep hC2 N₅ hfg₅ mu-1) ht)
  refine H.congr_deriv ?_
  unfold logProductSpectrumFun
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu hmu
  congr 2
  ring

/-- The genuine entire spectrum source insertion equals exp(-t) times its derivative. -/
theorem spectrum_Lm1_eq (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f (Lm1 N₁.toWeakModule x) y z (a+1) b c β t=
      Complex.exp (-1*t) * _root_.deriv
        (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β) t := by
  rw [(hasDerivAt_spectrum hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f x y z a b c β ht).deriv,← mul_assoc,← Complex.exp_add,
    show -1*t+t=0 by ring,Complex.exp_zero,one_mul]

end VOA.Huang.LogAssocCoefficientL0
