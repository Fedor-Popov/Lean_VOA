import VOA.Huang.LogAssocCoefficients

/-! The actual collision coefficient is bilinear in its outside data.
True all-log convergence justifies additivity of the complete integer rows. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficients
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules VOA.Huang.MatrixCoeff
open VOA.Huang.LogAssocJacobi VOA.Huang.AssocCommutator
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

theorem fullCoset_add_functional (f g : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (a b : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductFullCosetFun Y₁.1 Y₂.1 (f+g) x y z a b t=
      logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b t+
        logProductFullCosetFun Y₁.1 Y₂.1 g x y z a b t := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hzero : ∀ n k,K≤k → Y₁.1 n k=0 := fun n k hk => hK Y₁ n k hk
  simp only [fullCoset_eq_sum_log Y₂.1 hzero,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold logProductIntegerCosetFun prodFunZ
  rw [← mul_add]
  congr 1
  unfold prodValueZ
  have hsum (f : M₄ →ₗ[ℂ] ℂ) : Summable
      (prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0) f x y z (a+b) b (1+Complex.exp t) 1) :=
    summable_log_product_integerCoset hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z (a+b) b k 0 one_ne_zero (by simpa only [norm_one] using one_lt_norm ht)
  rw [← (hsum f).tsum_add (hsum g)]
  apply tsum_congr
  intro n
  simp only [prodTermZ,prodCoeff,LinearMap.add_apply,add_mul]

omit hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ in
theorem fullCoset_smul_functional (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (s a b t : ℂ) :
    logProductFullCosetFun Y₁ Y₂ (s•f) x y z a b t=
      s*logProductFullCosetFun Y₁ Y₂ f x y z a b t := by
  unfold logProductFullCosetFun
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hval : prodValueZ (fun n => Y₁ n k) (fun n => Y₂ n 0) (s•f) x y z (a+b) b
      (1+Complex.exp t) 1=
      s*prodValueZ (fun n => Y₁ n k) (fun n => Y₂ n 0) f x y z (a+b) b
        (1+Complex.exp t) 1 := by
    unfold prodValueZ
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [prodTermZ,prodCoeff,LinearMap.smul_apply,smul_eq_mul]
    ring
  unfold logProductIntegerCosetFun prodFunZ
  rw [hval]
  ring

theorem fullCoset_add_third (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z z' : M₃) (a b : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductFullCosetFun Y₁.1 Y₂.1 f x y (z+z') a b t=
      logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b t+
        logProductFullCosetFun Y₁.1 Y₂.1 f x y z' a b t := by
  have hh := fullCoset_sum_inputs hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f a b (Finset.univ : Finset Unit) (Finset.univ : Finset Unit)
    (Finset.univ : Finset (Fin 2)) (fun _ => x) (fun _ => y) ![z,z'] ht
  simpa only [Fin.sum_univ_two,Fintype.sum_unique,Matrix.cons_val_zero,Matrix.cons_val_one] using hh.symm

private theorem spectrum_add_functional (f g : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 (f+g) x y z a b c β t=
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β t+
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 g x y z a b c β t := by
  unfold logProductSpectrumFun
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun mu _ =>
    fullCoset_add_functional hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f g x y z _ _ ht

private theorem spectrum_smul_functional (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (s a b c β t : ℂ) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 (s•f) x y z a b c β t=
      s*logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β t := by
  unfold logProductSpectrumFun
  simp only [fullCoset_smul_functional,Finset.mul_sum]

private theorem spectrum_add_third (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z z' : M₃) (a b c β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y (z+z') a b c β t=
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β t+
        logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z' a b c β t := by
  unfold logProductSpectrumFun
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun mu _ =>
    fullCoset_add_third hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z z' _ _ ht

private theorem spectrum_smul_third (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (s a b c β t : ℂ) :
    logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y (s•z) a b c β t=
      s*logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β t := by
  unfold logProductSpectrumFun
  simp only [fullCoset_smul_third,Finset.mul_sum]


/-- Actual outside-data linearity of the unique full-product coefficient. -/
theorem coefficient_add_f (f g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (f+g) z c β γ k=coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k+coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ g z c β γ k := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (f+g) z c β γ k hx hy]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hx hy]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ g z c β γ k hx hy]
  have hF := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β
  have hG := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ g x y z a b c β
  have hL := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (f+g) x y z a b c β
  have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (fun t ht => spectrum_add_functional hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f g x y z a b c β ht) hL (γ-a-b) k
  rw [he]
  exact logCoeff_add isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hF hG _ _

/-- Actual outside-data linearity of the unique full-product coefficient. -/
theorem coefficient_smul_f (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (s : ℂ) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (s•f) z c β γ k=s•coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (s•f) z c β γ k hx hy]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hx hy]
  have hF := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β
  have hL := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ (s•f) x y z a b c β
  have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (fun t ht => spectrum_smul_functional hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z s a b c β t) hL (γ-a-b) k
  rw [he]
  exact logCoeff_smul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty s hF _ _

/-- Actual outside-data linearity of the unique full-product coefficient. -/
theorem coefficient_add_z (f : M₄ →ₗ[ℂ] ℂ) (z z' : M₃) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f (z+z') c β γ k=coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k+coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z' c β γ k := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f (z+z') c β γ k hx hy]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hx hy]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z' c β γ k hx hy]
  have hF := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β
  have hG := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z' a b c β
  have hL := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y (z+z') a b c β
  have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (fun t ht => spectrum_add_third hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z z' a b c β ht) hL (γ-a-b) k
  rw [he]
  exact logCoeff_add isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hF hG _ _

/-- Actual outside-data linearity of the unique full-product coefficient. -/
theorem coefficient_smul_z (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (s : ℂ) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f (s•z) c β γ k=s•coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k := by
  apply bilinear_ext_homogeneous N₁ N₂
  intro a b x y hx hy
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f (s•z) c β γ k hx hy]
  rw [coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hx hy]
  have hF := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β
  have hL := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y (s•z) a b c β
  have he := logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
    (fun t ht => spectrum_smul_third hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z s a b c β t) hL (γ-a-b) k
  rw [he]
  exact logCoeff_smul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty s hF _ _

/-- The true full-product coefficient, bilinear in the actual outside
functional and vector, with values in the genuine inside tensor dual. -/
noncomputable def outsideCoefficient (c β γ : ℂ) (k : ℕ) :
    (M₄ →ₗ[ℂ] ℂ) →ₗ[ℂ] M₃ →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂) :=
  LinearMap.mk₂ ℂ
    (fun f z => coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k)
    (fun f g z => coefficient_add_f hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f g z c β γ k)
    (fun s f z => coefficient_smul_f hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z s c β γ k)
    (fun f z z' => coefficient_add_z hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z z' c β γ k)
    (fun s f z => coefficient_smul_z hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z s c β γ k)

end VOA.Huang.LogAssocCoefficients
