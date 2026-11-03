import VOA.Huang.LogAssocOutsideJacobiFunctions

/-! Literal coefficient extraction of the actual all-log outside commutator.
The binomial convolution retains the full generalized spectrum and every
collision logarithmic degree. No ordinary or rationality premise is used. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocOutsideJacobi
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.LogAssocCoefficients
open VOA.Huang.FrobeniusLog (psEval)
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

/-- The actual spectrum commutator gives the honest finite binomial convolution
of the unique collision coefficients. -/
theorem logCoeff_spectrum_commutator (u : V) (d m : ℤ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) {R : ℤ}
    (hX : ∀ i : ℤ, R ≤ i → mode (N₁.YM u) i x=0)
    (hY : ∀ i : ℤ, R ≤ i → mode (N₂.YM u) i y=0)
    (a b c β μ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
        (f ∘ₗ mode (N₄.YM u) m) x y z a b c (β-d+m+1)) μ k =
      logCoeff overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
        f x y (mode (N₃.YM u) m z) a b (c+d-m-1) β) μ k +
      ∑ i∈Finset.Ico 0 R,cbz m i*∑ᶠ j : ℕ,PowerSeries.coeff j (binPS (m-i))*
        logCoeff overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
          f (mode (N₁.YM u) i x) y z (a+d-i-1) b c β) (μ-j) k +
      ∑ i∈Finset.Ico 0 R,cbz m i*
        logCoeff overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
          f x (mode (N₂.YM u) i y) z a (b+d-i-1) c β) μ k := by
  classical
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  let F₃ := logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
    f x y (mode (N₃.YM u) m z) a b (c+d-m-1) β
  let F₁ : ℤ → ℂ → ℂ := fun i => logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
    f (mode (N₁.YM u) i x) y z (a+d-i-1) b c β
  let F₂ : ℤ → ℂ → ℂ := fun i => logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
    f x (mode (N₂.YM u) i y) z a (b+d-i-1) c β
  have hE (g : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (A B C D : ℂ) :=
    log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ g w₁ w₂ w₃ A B C D
  have e₃ : HasLogExp overlapDomain F₃ := hE _ _ _ _ _ _ _ _
  have e₁ (i : ℤ) : HasLogExp overlapDomain (F₁ i) := hE _ _ _ _ _ _ _ _
  have e₂ (i : ℤ) : HasLogExp overlapDomain (F₂ i) := hE _ _ _ _ _ _ _ _
  have e₁' (i : ℤ) : HasLogExp overlapDomain
      (fun t => cbz m i*(psEval (binPS (m-i)) (Complex.exp t)*F₁ i t)) :=
    hasLogExp_smul _ (hasLogExp_psEval_mul hs (e₁ i) (binPS_mem _))
  have e₂' (i : ℤ) : HasLogExp overlapDomain (fun t => cbz m i*F₂ i t) :=
    hasLogExp_smul _ (e₂ i)
  have eS₁ := hasLogExp_sum (Finset.Ico 0 R) (fun i _ => e₁' i)
  have eS₂ := hasLogExp_sum (Finset.Ico 0 R) (fun i _ => e₂' i)
  have hsum : ∀ t∈overlapDomain,
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
        (f ∘ₗ mode (N₄.YM u) m) x y z a b c (β-d+m+1) t =
      ((F₃+fun t => ∑ i∈Finset.Ico 0 R,
        cbz m i*(psEval (binPS (m-i)) (Complex.exp t)*F₁ i t))+
        fun t => ∑ i∈Finset.Ico 0 R,cbz m i*F₂ i t) t := by
    intro t ht
    rw [spectrum_commutator hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ u d m f x y z hX hY a b c β ht]
    change _ = F₃ t+(∑ i∈Finset.Ico 0 R,
      cbz m i*(psEval (binPS (m-i)) (Complex.exp t)*F₁ i t))+
      ∑ i∈Finset.Ico 0 R,cbz m i*F₂ i t
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [psEval_binPS _ (norm_exp_lt_one ht),Complex.cpow_intCast]
    dsimp only [F₁]
    ring
  have eA := hasLogExp_add e₃ eS₁
  rw [logCoeff_congr hU hs hne hsum
    (hasLogExp_congr (fun t ht => (hsum t ht).symm) (hasLogExp_add eA eS₂)),
    logCoeff_add hU hs hne eA eS₂,logCoeff_add hU hs hne e₃ eS₁,
    logCoeff_sum hU hs hne _ (fun i _ => e₁' i),
    logCoeff_sum hU hs hne _ (fun i _ => e₂' i)]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logCoeff_smul hU hs hne _ (hasLogExp_psEval_mul hs (e₁ i) (binPS_mem _)),
      logCoeff_psEval_mul hU hs hne (e₁ i) (binPS_mem _)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [logCoeff_smul hU hs hne _ (e₂ i)]

/-- The literal bilinear outside commutator on genuine generalized inputs,
with the exact weight shifts in its Cauchy convolution. -/
theorem coefficient_commutator_homogeneous {d : ℤ} {u : V} (hu : u∈W.grading d)
    (m : ℤ) (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    {R : ℤ} (hX : ∀ i : ℤ,R ≤ i → mode (N₁.YM u) i x=0)
    (hY : ∀ i : ℤ,R ≤ i → mode (N₂.YM u) i y=0) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      (f ∘ₗ mode (N₄.YM u) m) z c (β-d+m+1) γ k x y =
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f (mode (N₃.YM u) m z) (c+d-m-1) β γ k x y +
      ∑ i∈Finset.Ico 0 R,cbz m i*∑ᶠ j : ℕ,PowerSeries.coeff j (binPS (m-i))*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f z c β (γ+d-i-1-j) k (mode (N₁.YM u) i x) y +
      ∑ i∈Finset.Ico 0 R,cbz m i*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f z c β (γ+d-i-1) k x (mode (N₂.YM u) i y) := by
  classical
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ _ _ _ _ _ _ hx hy,
    coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ _ _ _ _ _ _ hx hy,
    logCoeff_spectrum_commutator hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ u d m f x y z hX hY a b c β (γ-a-b) k]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    apply finsum_congr
    intro j
    rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ _ _ _ _ _ _ (N₁.mode_mem_weight hu hx i) hy]
    congr 2
    push_cast
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ _ _ _ _ _ _ hx (N₂.mode_mem_weight hu hy i)]
    congr 2
    push_cast
    ring

end VOA.Huang.LogAssocOutsideJacobi
