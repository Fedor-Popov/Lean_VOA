import VOA.Huang.LogAssocCoefficientCoproduct
import VOA.Huang.LogAssocCoefficientCoproductLeftFunctions

/-! The left associator on literal all-logarithmic collision coefficients.
The binomial factors act by their proved finite Cauchy coefficient sums. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientCoproduct
open VOA VOA.LogTensor VOA.LogTensor.Pz PowerSeries
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.LogAssocCoefficients
open VOA.Huang.PzTensorRho VOA.Huang.AssocAssociator VOA.Huang.FrobeniusLog
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


/-- The true left associator on the actual bilinear coefficient functions,
including every original logarithmic degree. -/
theorem coefficient_assoc_left_homogeneous {d : ℤ} {u : V} (hu : u∈W.grading d)
    (ell : ℤ) (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    {NA NY NZ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (N₄.YM u) (ell-i)=0)
    (hY : ∀ i : ℕ, NY ≤ i → mode (N₂.YM u) i y=0)
    (hZ : ∀ i : ℕ, NZ ≤ i → mode (N₃.YM u) i z=0) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k
        (mode (N₁.YM u) ell x) y =
      ∑ i∈Finset.range NA,negOnePow i*cbz ell i*
        ∑ᶠ s : ℕ,coeff s (binPS (i : ℤ))*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          (f ∘ₗ mode (N₄.YM u) (ell-i)) z c (β-d+(ell-i : ℤ)+1) (γ-d+ell+1-s) k x y
      - negOnePow ell*∑ i∈Finset.range NZ,negOnePow i*cbz ell i*
        ∑ᶠ s : ℕ,coeff s (binPS (ell-i))*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f (mode (N₃.YM u) i z) (c+d-i-1) β (γ-d+ell+1-s) k x y
      - negOnePow ell*∑ j∈Finset.range NY,negOnePow j*cbz ell j*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k
          x (mode (N₂.YM u) j y) := by
  let μ := γ-(a+d-ell-1)-b
  let FA : ℕ → ℂ → ℂ := fun i => logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
    (f ∘ₗ mode (N₄.YM u) (ell-i)) x y z a b c (β-d+(ell-i : ℤ)+1)
  let FB : ℕ → ℂ → ℂ := fun i => logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
    f x y (mode (N₃.YM u) i z) a b (c+d-i-1) β
  let FC : ℕ → ℂ → ℂ := fun j => logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
    f x (mode (N₂.YM u) j y) z a (b+d-j-1) c β
  have hE (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β : ℂ) :=
    log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z a b c β
  have eA (i : ℕ) : HasLogExp overlapDomain (FA i) := hE _ _ _ _ _ _ _ _
  have eB (i : ℕ) : HasLogExp overlapDomain (FB i) := hE _ _ _ _ _ _ _ _
  have eC (j : ℕ) : HasLogExp overlapDomain (FC j) := hE _ _ _ _ _ _ _ _
  have he := logCoeff_assoc_identity (NA := NA) (NB := NZ) (NC := NY)
    (fun i => negOnePow i*cbz ell i) (fun i => negOnePow i*cbz ell i)
    (fun j => negOnePow ell*(negOnePow j*cbz ell j))
    (negOnePow ell) (fun j => ((ell-j : ℤ) : ℂ))
    (hE f (mode (N₁.YM u) ell x) y z (a+d-ell-1) b c β)
    (fun i => hasLogExp_psEval_mul overlapDomain_subset (eA i) (binPS_mem _))
    (fun i => hasLogExp_psEval_mul overlapDomain_subset (eB i) (binPS_mem _)) eC
    (fun t ht => by
      rw [spectrum_assoc_left hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ u d ell f x y z hA hY hZ a b c β ht]
      simp only [FA,FB,FC,Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring) μ k
  have eAc (i : ℕ) := logCoeff_psEval_mul isOpen_overlapDomain overlapDomain_subset
    overlapDomain_nonempty (eA i) (binPS_mem (i : ℤ)) μ k
  have eBc (i : ℕ) := logCoeff_psEval_mul isOpen_overlapDomain overlapDomain_subset
    overlapDomain_nonempty (eB i) (binPS_mem (ell-i)) μ k
  simp only [eAc,eBc] at he
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    f z c β γ k (N₁.mode_mem_weight hu hx ell) hy]
  change logCoeff overlapDomain _ μ k=_
  rw [he]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      refine finsum_congr fun s => ?_
      rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ _ _ _ _ _ _ hx hy]
      congr 2
      dsimp [μ]
      ring
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      refine finsum_congr fun s => ?_
      rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ _ _ _ _ _ _ hx hy]
      congr 2
      dsimp [μ]
      ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ _ _ _ _ _ _ hx (N₂.mode_mem_weight hu hy (j : ℤ))]
    simp only [Int.cast_natCast]
    have eμ : μ-((ell-j : ℤ) : ℂ)=γ-a-(b+d-j-1) := by
      dsimp [μ]
      push_cast
      ring
    rw [eμ]
    dsimp [FC]
    ring

end VOA.Huang.LogAssocCoefficientCoproduct
