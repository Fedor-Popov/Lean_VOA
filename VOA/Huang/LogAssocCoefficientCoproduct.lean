import VOA.Huang.LogAssocCoefficientCoproductFunctions

/-! Unique genuine collision coefficients obey the all-logarithmic P(1)
coproduct identity. The cancellation keeps precisely the same log index. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientCoproduct
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.LogAssocCoefficients
open VOA.Huang.PzTensorRho VOA.Huang.AssocAssociator
open scoped BigOperators
universe u

/-- Extraction of the unique logarithmic coefficient of a finite associator
identity, preserving the log index and translating only the exponent. -/
theorem logCoeff_assoc_identity {NA NB NC : ℕ} {F : ℂ → ℂ}
    {FA FB FC : ℕ → ℂ → ℂ} (sA sB sC : ℕ → ℂ) (s : ℂ) (δ : ℕ → ℂ)
    (eF : HasLogExp overlapDomain F)
    (eA : ∀ i, HasLogExp overlapDomain (FA i))
    (eB : ∀ i, HasLogExp overlapDomain (FB i))
    (eC : ∀ i, HasLogExp overlapDomain (FC i))
    (h : ∀ t∈overlapDomain,F t=(∑ i∈Finset.range NA,sA i*FA i t)
      -s*(∑ i∈Finset.range NB,sB i*FB i t)
      -(∑ i∈Finset.range NC,sC i*Complex.exp (δ i*t)*FC i t)) (μ : ℂ) (k : ℕ) :
    logCoeff overlapDomain F μ k=
      (∑ i∈Finset.range NA,sA i*logCoeff overlapDomain (FA i) μ k)
      -s*(∑ i∈Finset.range NB,sB i*logCoeff overlapDomain (FB i) μ k)
      -(∑ i∈Finset.range NC,sC i*logCoeff overlapDomain (FC i) (μ-δ i) k) := by
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  have eA' : ∀ i,HasLogExp overlapDomain (fun t => sA i*FA i t) :=
    fun i => hasLogExp_smul _ (eA i)
  have eB' : ∀ i,HasLogExp overlapDomain (fun t => sB i*FB i t) :=
    fun i => hasLogExp_smul _ (eB i)
  have eC' : ∀ i,HasLogExp overlapDomain (fun t => sC i*(Complex.exp (δ i*t)*FC i t)) :=
    fun i => hasLogExp_smul _ (hasLogExp_exp_mul (eC i) _)
  have eSA := hasLogExp_sum (Finset.range NA) (fun i _ => eA' i)
  have eSB := hasLogExp_smul s (hasLogExp_sum (Finset.range NB) (fun i _ => eB' i))
  have eSC := hasLogExp_sum (Finset.range NC) (fun i _ => eC' i)
  have hsum : ∀ t∈overlapDomain,F t=
      (((fun t => ∑ i∈Finset.range NA,sA i*FA i t)
        +fun t => -(s*∑ i∈Finset.range NB,sB i*FB i t))
        +fun t => -(∑ i∈Finset.range NC,sC i*(Complex.exp (δ i*t)*FC i t))) t := by
    intro t ht
    rw [h t ht]
    simp only [Pi.add_apply,sub_eq_add_neg]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by ring
  have eSB' := hasLogExp_smul (-1) eSB
  have eSC' := hasLogExp_smul (-1) eSC
  simp only [neg_one_mul] at eSB' eSC'
  have eAB := hasLogExp_add eSA eSB'
  rw [logCoeff_congr hU hs hne hsum eF,
    logCoeff_add hU hs hne eAB eSC',logCoeff_add hU hs hne eSA eSB']
  have nB : logCoeff overlapDomain (fun t => -(s*∑ i∈Finset.range NB,sB i*FB i t)) μ k=
      -(s*∑ i∈Finset.range NB,sB i*logCoeff overlapDomain (FB i) μ k) := by
    have he := logCoeff_smul hU hs hne (-1) eSB μ k
    simp only [neg_one_mul] at he
    rw [he,logCoeff_smul hU hs hne _ (hasLogExp_sum (Finset.range NB) (fun i _ => eB' i)),
      logCoeff_sum hU hs hne _ (fun i _ => eB' i)]
    congr 2
    exact Finset.sum_congr rfl fun i _ => logCoeff_smul hU hs hne _ (eB i) μ k
  have nC : logCoeff overlapDomain
      (fun t => -(∑ i∈Finset.range NC,sC i*(Complex.exp (δ i*t)*FC i t))) μ k=
      -(∑ i∈Finset.range NC,sC i*logCoeff overlapDomain (FC i) (μ-δ i) k) := by
    have he := logCoeff_smul hU hs hne (-1) eSC μ k
    simp only [neg_one_mul] at he
    rw [he,logCoeff_sum hU hs hne _ (fun i _ => eC' i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logCoeff_smul hU hs hne _ (hasLogExp_exp_mul (eC i) _)]
    congr 1
    have he := logCoeff_exp_mul hU hs hne (eC i) (δ i) (μ-δ i) k
    rw [sub_add_cancel] at he
    exact he
  rw [nB,nC,logCoeff_sum hU hs hne _ (fun i _ => eA' i)]
  simp only [sub_eq_add_neg]
  congr 2
  exact Finset.sum_congr rfl fun i _ => logCoeff_smul hU hs hne _ (eA i) μ k

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

/-- The all-log right Jacobi relation on the actual bilinear coefficient,
on every genuine generalized homogeneous input pair. -/
theorem coefficient_coproduct_homogeneous {d : ℤ} {u : V} (hu : u∈W.grading d)
    (p : ℤ) (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    {NA NX NZ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (N₄.YM u) (p-i)=0)
    (hX : ∀ i : ℕ, NX ≤ i → mode (N₁.YM u) i x=0)
    (hZ : ∀ i : ℕ, NZ ≤ i → mode (N₃.YM u) i z=0) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k
        x (mode (N₂.YM u) p y)
      + ∑ r∈Finset.range NX,cbz p r*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k
          (mode (N₁.YM u) r x) y =
      ∑ i∈Finset.range NA,negOnePow i*cbz p i*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          (f ∘ₗ mode (N₄.YM u) (p-i)) z c (β-d+(p-i : ℤ)+1) (γ-d+p+1) k x y
      - negOnePow p*∑ i∈Finset.range NZ,negOnePow i*cbz p i*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f (mode (N₃.YM u) i z) (c+d-i-1) β (γ-d+p+1) k x y := by
  have hE (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β : ℂ) :=
    log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z a b c β
  have he := logCoeff_assoc_identity
    (fun i => negOnePow i*cbz p i) (fun i => negOnePow i*cbz p i) (fun r => cbz p r)
    (negOnePow p) (fun r => ((p-r : ℤ) : ℂ))
    (hE f x (mode (N₂.YM u) p y) z a (b+d-p-1) c β)
    (fun i => hE (f ∘ₗ mode (N₄.YM u) (p-i)) x y z a b c (β-d+(p-i : ℤ)+1))
    (fun i => hE f x y (mode (N₃.YM u) i z) a b (c+d-i-1) β)
    (fun r => hE f (mode (N₁.YM u) r x) y z (a+d-r-1) b c β)
    (fun t ht => spectrum_assoc_right hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ u d p f x y z hA hX hZ a b c β ht)
    (γ-a-(b+d-p-1)) k
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
    f z c β γ k hx (N₂.mode_mem_weight hu hy p)]
  have eA (i : ℕ) := coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (f ∘ₗ mode (N₄.YM u) (p-i))
    z c (β-d+(p-i : ℤ)+1) (γ-d+p+1) k hx hy
  have eB (i : ℕ) := coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f (mode (N₃.YM u) i z)
    (c+d-i-1) β (γ-d+p+1) k hx hy
  have eC (r : ℕ) := coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k (N₁.mode_mem_weight hu hx r) hy
  simp_rw [eA,eB,eC]
  rw [show γ-(d : ℂ)+p+1-a-b=γ-a-(b+d-p-1) by ring]
  have eCs : (∑ r∈Finset.range NX,cbz p r*
      logCoeff overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
        f (mode (N₁.YM u) r x) y z (a+d-r-1) b c β)
        (γ-(a+d-r-1)-b) k)=
      (∑ r∈Finset.range NX,cbz p r*
      logCoeff overlapDomain (logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1
        f (mode (N₁.YM u) r x) y z (a+d-r-1) b c β)
        (γ-a-(b+d-p-1)-((p-r : ℤ) : ℂ)) k) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 2
    push_cast
    ring
  simp only [Int.cast_natCast]
  rw [eCs]
  linear_combination he


/-- The true transposed coproduct is a finite sum of actual coefficients
with modified outside data, with the same logarithmic index. -/
theorem coefficient_coproduct {d : ℤ} {u : V} (hu : u∈W.grading d)
    (p : ℤ) (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ) {NA NZ : ℕ}
    (hA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (N₄.YM u) (p-i)=0)
    (hZ : ∀ i : ℕ, NZ ≤ i → mode (N₃.YM u) i z=0) :
    rhoL N₁.toWeakModule N₂.toWeakModule u p
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k)=
      (∑ i∈Finset.range NA,(negOnePow i*cbz p i) •
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          (f ∘ₗ mode (N₄.YM u) (p-i)) z c (β-d+(p-i : ℤ)+1) (γ-d+p+1) k)
      - negOnePow p • (∑ i∈Finset.range NZ,(negOnePow i*cbz p i) •
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f (mode (N₃.YM u) i z) (c+d-i-1) β (γ-d+p+1) k) := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  obtain ⟨NX,hX⟩ := LogAssocCoefficientCompatibility.exists_nat_truncation N₁ u x
  rw [rhoL_apply]
  rw [finsum_eq_sum_range (R := NX) (fun r hr => by rw [cbz_apply_neg _ hr,zero_mul])
    (fun r hr => by
      obtain ⟨i,rfl⟩ : ∃ i : ℕ,r=(i : ℤ) := ⟨r.toNat,by omega⟩
      rw [hX i (by exact_mod_cast hr),map_zero,LinearMap.zero_apply,mul_zero])]
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.sum_apply,
    LinearMap.coe_sum,Finset.sum_apply,smul_eq_mul]
  exact coefficient_coproduct_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hu p f z c β γ k hx hy hA hX hZ

end VOA.Huang.LogAssocCoefficientCoproduct
