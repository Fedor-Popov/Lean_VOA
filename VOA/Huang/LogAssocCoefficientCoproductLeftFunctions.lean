import VOA.Huang.LogAssocCoefficientCoproductFunctions
import VOA.Huang.PzTensorCompatProof

/-! The genuine all-logarithmic right associator on the complete intermediate
spectrum. Integer-row invariance is proved directly from the actual sums. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientCoproduct
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.AssocCommutator
open VOA.Huang.LogAssocJacobi VOA.Huang.LogAssocAssociator
open VOA.Huang.LogHuangODEModes
open scoped BigOperators
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
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅


theorem fullCoset_assoc_left (u : V) (ell : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) {NA NY NZ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (N₄.YM u) (ell-i)=0)
    (hY : ∀ i : ℕ, NY ≤ i → mode (N₂.YM u) i y=0)
    (hZ : ∀ i : ℕ, NZ ≤ i → mode (N₃.YM u) i z=0)
    (a b : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductFullCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) ell x) y z a b t =
      ∑ i∈Finset.range NA,negOnePow i*cbz ell i*(1+Complex.exp t)^(i : ℤ)*
        logProductFullCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) (ell-i)) x y z (a+i) b t
      - negOnePow ell*∑ i∈Finset.range NZ,negOnePow i*cbz ell i*(1+Complex.exp t)^(ell-i)*
        logProductFullCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z) (a+(ell-i : ℤ)) b t
      - negOnePow ell*∑ j∈Finset.range NY,negOnePow j*cbz ell j*Complex.exp (((ell-j : ℤ) : ℂ)*t)*
        logProductFullCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) j y) z (a+ell) (b-j) t := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hz : 1<‖1+Complex.exp t‖ := one_lt_norm ht
  have hconv (g : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (S ν : ℂ) (k : ℕ) :
      Summable (prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0)
        g w₁ w₂ w₃ S ν (1+Complex.exp t) 1) :=
    summable_log_product_integerCoset hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ g w₁ w₂ w₃ S ν k 0 one_ne_zero (by simpa only [norm_one] using hz)
  have hk (k : ℕ) :
      logProductIntegerCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) ell x) y z a b k 0 t =
        ∑ i∈Finset.range NA,negOnePow i*cbz ell i*(1+Complex.exp t)^(i : ℤ)*
          logProductIntegerCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) (ell-i)) x y z (a+i) b k 0 t
        - negOnePow ell*∑ i∈Finset.range NZ,negOnePow i*cbz ell i*(1+Complex.exp t)^(ell-i)*
          logProductIntegerCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z) (a+(ell-i : ℤ)) b k 0 t
        - negOnePow ell*∑ j∈Finset.range NY,negOnePow j*cbz ell j*Complex.exp (((ell-j : ℤ) : ℂ)*t)*
          logProductIntegerCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) j y) z (a+ell) (b-j) k 0 t := by
    dsimp only [logProductIntegerCosetFun,prodFunZ]
    rw [prodValueZ_assoc_left (logCoefficient_isJacobi Y₁.2 k)
      (logCoefficient_isJacobi Y₂.2 0) u ell f x y z hA hY hZ (a+b) b _ hz
      (fun i => hconv _ _ _ _ _ _ k) (fun i => hconv _ _ _ _ _ _ k)
      (fun i => hconv _ _ _ _ _ _ k)]
    simp only [Int.cast_natCast,mul_sub,Finset.mul_sum]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [show a+b+(i : ℂ)=a+i+b by ring]
        ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [show a+b+((ell-i : ℤ) : ℂ)=a+(ell-i : ℤ)+b by ring]
        ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show a+b+((ell-j : ℤ) : ℂ)=a+ell+(b-j) by push_cast; ring,
        add_sub_cancel_left,← Complex.exp_int_mul]
      ring
  simp only [fullCoset_eq_sum_log Y₂.1 (fun n k hk => hK Y₁ n k hk)]
  rw [Finset.sum_congr rfl (fun k _ => hk k),Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := Finset.range K)]

/-- The true full-spectrum left associator, retaining every logarithmic
coefficient and normalizing only by integer row invariance. -/
theorem spectrum_assoc_left (u : V) (d ell : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) {NA NY NZ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (N₄.YM u) (ell-i)=0)
    (hY : ∀ i : ℕ, NY ≤ i → mode (N₂.YM u) i y=0)
    (hZ : ∀ i : ℕ, NZ ≤ i → mode (N₃.YM u) i z=0)
    (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f (mode (N₁.YM u) ell x) y z
        (a+d-ell-1) b c β t =
      ∑ i∈Finset.range NA,negOnePow i*cbz ell i*
        (FrobeniusLog.psEval (binPS (i : ℤ)) (Complex.exp t)*
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
          (f ∘ₗ mode (N₄.YM u) (ell-i)) x y z a b c (β-d+(ell-i : ℤ)+1) t)
      - negOnePow ell*∑ i∈Finset.range NZ,negOnePow i*cbz ell i*
        (FrobeniusLog.psEval (binPS (ell-i)) (Complex.exp t)*
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z)
          a b (c+d-i-1) β t)
      - negOnePow ell*∑ j∈Finset.range NY,negOnePow j*cbz ell j*Complex.exp (((ell-j : ℤ) : ℂ)*t)*
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x (mode (N₂.YM u) j y) z
          a (b+d-j-1) c β t := by
  classical
  have ep (q : ℤ) : (1+Complex.exp t)^q=FrobeniusLog.psEval (binPS q) (Complex.exp t) :=
    (psEval_binPS q (norm_exp_lt_one ht)).symm
  have hmu (h : ℂ) :
      logProductFullCosetFun Y₁.1 Y₂.1 f (mode (N₁.YM u) ell x) y z
          ((a+d-ell-1)+h-β-1) (b+c-h-1) t =
        ∑ i∈Finset.range NA,negOnePow i*cbz ell i*
          (FrobeniusLog.psEval (binPS (i : ℤ)) (Complex.exp t)*
          logProductFullCosetFun Y₁.1 Y₂.1 (f ∘ₗ mode (N₄.YM u) (ell-i)) x y z
            (a+h-(β-d+(ell-i : ℤ)+1)-1) (b+c-h-1) t)
        - negOnePow ell*∑ i∈Finset.range NZ,negOnePow i*cbz ell i*
          (FrobeniusLog.psEval (binPS (ell-i)) (Complex.exp t)*
          logProductFullCosetFun Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z)
            (a+h-β-1) (b+(c+d-i-1)-h-1) t)
        - negOnePow ell*∑ j∈Finset.range NY,negOnePow j*cbz ell j*Complex.exp (((ell-j : ℤ) : ℂ)*t)*
          logProductFullCosetFun Y₁.1 Y₂.1 f x (mode (N₂.YM u) j y) z
            (a+h-β-1) ((b+d-j-1)+c-h-1) t := by
    rw [fullCoset_assoc_left hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ u ell f x y z hA hY hZ _ _ ht]
    simp only [ep]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
        congr 2
        push_cast
        ring
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc]
        congr 1
        congr 1
        have e := fullCoset_shift Y₁.1 Y₂.1 f x y (mode (N₃.YM u) i z)
          (((a+d-ell-1)+h-β-1)+(ell-i : ℤ)) (b+c-h-1) (d-i-1) t
        have e1 : ((a+d-ell-1)+h-β-1)+((ell-i : ℤ) : ℂ)-((d-i-1 : ℤ) : ℂ)=a+h-β-1 := by
          push_cast; ring
        have e2 : b+c-h-1+((d-i-1 : ℤ) : ℂ)=b+(c+d-i-1)-h-1 := by
          push_cast; ring
        rw [e1,e2] at e
        exact e.symm
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      have e := fullCoset_shift Y₁.1 Y₂.1 f x (mode (N₂.YM u) j y) z
        (((a+d-ell-1)+h-β-1)+ell) ((b+c-h-1)-j) (d-1) t
      have e1 : ((a+d-ell-1)+h-β-1)+(ell : ℂ)-((d-1 : ℤ) : ℂ)=a+h-β-1 := by
        push_cast; ring
      have e2 : b+c-h-1-(j : ℂ)+((d-1 : ℤ) : ℂ)=(b+d-j-1)+c-h-1 := by
        push_cast; ring
      rw [e1,e2] at e
      exact e.symm
  unfold logProductSpectrumFun
  rw [Finset.sum_congr rfl (fun mu _ => hmu (spectrumCosetRep hC2 N₅ hfg₅ mu)),
    Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := spectrumCosets hC2 N₅ hfg₅)]

end VOA.Huang.LogAssocCoefficientCoproduct
