import VOA.Huang.LogAssocSpectrum
import VOA.Huang.LogAssocConvergence
import VOA.Modules.LogTensorPzPointEvaluation

/-! The literal completed product pairs an actual point-evaluation block
with every component of the genuine intermediate completion. Proved
finite disjoint spectrum cosets reindex that scalar sum without duplication. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.FrobeniusLog
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- A scalar function supported on the actual spectrum sums over the finitely
many disjoint proved integer cosets, exactly once per genuine weight. -/
theorem tsum_spectrumCosets (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) (g : ℂ → ℂ)
    (hweight : ∀ a,g a≠0 → N.weight a≠⊥)
    (hs : ∀ mu∈spectrumCosets hC2 N hfg,
      Summable fun d : ℤ => g (spectrumCosetRep hC2 N hfg mu+d)) :
    Summable g ∧ ∑' a : ℂ,g a=
      ∑ mu∈spectrumCosets hC2 N hfg,∑' d : ℤ,g (spectrumCosetRep hC2 N hfg mu+d) := by
  classical
  let I := ↥(spectrumCosets hC2 N hfg)
  let e : I×ℤ → ℂ := fun p => spectrumCosetRep hC2 N hfg p.1+p.2
  have hinj : Function.Injective e := by
    rintro ⟨mu,d⟩ ⟨nu,j⟩ he
    have hh : (mu : ℂ)=(nu : ℂ) :=
      spectrumCoset_weight_unique hC2 N hfg mu.2 nu.2 d j he
    have hmn : mu=nu := Subtype.ext hh
    subst hmn
    have hd : d=j := by
      have hc : (d : ℂ)=(j : ℂ) := add_left_cancel he
      exact_mod_cast hc
    subst hd
    rfl
  have hsupport : Function.support g⊆Set.range e := by
    intro a ha
    obtain ⟨mu,hmu,d,hd⟩ := exists_spectrumCoset_weight hC2 N hfg a (hweight a ha)
    exact ⟨(⟨mu,hmu⟩,d),hd.symm⟩
  have heSum : Summable (fun p : I×ℤ => g (e p)) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun p => norm_nonneg (g (e p)))).mpr
    refine ⟨fun mu => (summable_norm_iff (E := ℂ)).mpr (hs mu mu.2),?_⟩
    exact Summable.of_finite
  have hvan : ∀ a,a∉Set.range e → g a=0 := by
    intro a ha
    by_contra hh
    exact ha (hsupport hh)
  have hg : Summable g := (hinj.summable_iff hvan).mp heSum
  refine ⟨hg,?_⟩
  rw [← hinj.tsum_eq hsupport,heSum.tsum_prod]
  simpa only [e,I] using Finset.tsum_subtype (spectrumCosets hC2 N hfg)
    (fun mu => ∑' d : ℤ,g (spectrumCosetRep hC2 N hfg mu+d))

variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- Literal pairing with the actual componentwise completed outer evaluation.
Its input is a genuine intermediate completion, rather than assumed coefficients. -/
noncomputable def completedProductPair
    (N₁ : LogVModule W M₁) (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (ell a c : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : N₁.weight a) (q : Completion N₅) : ℂ :=
  ∑' b : ℂ,f (pointEvaluationBlock N₁ N₅ N₄ Y₁ ell a b c x (q b))

/-- The genuine completed product of the two actual logarithmic operators. -/
noncomputable def completedLogProduct
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (ell₁ ell₂ a c : ℂ) (f : M₄ →ₗ[ℂ] ℂ) (x : N₁.weight a) (y : M₂) (z : M₃) : ℂ :=
  completedProductPair N₁ N₄ N₅ Y₁ ell₁ a c f x (evaluatePoint N₂ N₃ N₅ Y₂ ell₂ y z)

open VOA.Huang.AssocExpansion VOA.Huang.MatrixCoeff
open VOA.Huang.AssocCommutator (prodTermZ prodValueZ)
open VOA.Huang.LogAssocJacobi (summable_log_product_integerCoset)

/-- The finite spectrum expansion is literally the actual completed product,
with genuine point-evaluation blocks, the actual branch, and all logarithms. -/
theorem completedLogProduct_eq_spectrum (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x ∈ N₁.weight α₁) (hy : y ∈ N₂.weight α₂) (hz : z ∈ N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {t : ℂ} (ht : t∈VOA.Huang.AssocExpansion.overlapDomain)  :
    completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log (1+Complex.exp t)) 0
      α₁ β f ⟨x,hx⟩ y z=
      logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z α₁ α₂ α₃ β t := by
  classical
  let ell := Complex.log (1+Complex.exp t)
  let z₁ := 1+Complex.exp t
  let q := evaluatePoint N₂ N₃ N₅ Y₂ 0 y z
  let g : ℂ → ℂ := fun γ => f (pointEvaluationBlock N₁ N₅ N₄ Y₁ ell α₁ γ β ⟨x,hx⟩ (q γ))
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hzero : ∀ n k,K≤k → Y₁.1 n k=0 := fun n k hk => hK Y₁ n k hk
  have hq (γ : ℂ) : (q γ : M₅)=Y₂.1 (α₂+α₃-γ-1) 0 y z := by
    dsimp only [q]
    rw [evaluatePoint_zero,evaluateOne_homogeneous N₂ N₃ N₅ Y₂ hy hz γ]
  have hg (γ : ℂ) : g γ=Complex.exp (ell*(β-α₁-γ)) *
      ∑ k∈Finset.range K,ell^k*f (Y₁.1 (α₁+γ-β-1) k x
        (Y₂.1 (α₂+α₃-γ-1) 0 y z)) := by
    dsimp only [g]
    rw [pointEvaluationBlock_fixed_cutoff N₁ N₅ N₄ Y₁ ell α₁ γ β ⟨x,hx⟩ (q γ) K
      (fun k hk => by rw [hzero _ k hk]; rfl),map_smul,map_sum]
    simp only [map_smul,smul_eq_mul,hq]
  have hweight : ∀ γ,g γ≠0 → N₅.weight γ≠⊥ := by
    intro γ hγ he
    have hq0 : q γ=0 := by
      apply Subtype.ext
      have hbot : N₅.weight γ≤(⊥ : Submodule ℂ M₅) := by rw [he]
      exact (Submodule.mem_bot ℂ).mp (hbot (q γ).2)
    apply hγ
    simp only [g,hq0,map_zero,Submodule.coe_zero]
  have hrow (r : ℂ) (d : ℤ) : g (r+d)=
      ∑ k∈Finset.range K,ell^k * prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0)
        f x y z (α₁+α₂+α₃-β-2) (α₂+α₃-r-1) z₁ 1 d := by
    rw [hg,Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [prodTermZ,prodCoeff,Complex.one_cpow,mul_one]
    have he₁ : α₁+α₂+α₃-β-2-(α₂+α₃-r-1)+(d : ℂ)=α₁+(r+d)-β-1 := by ring
    have he₂ : α₂+α₃-r-1-(d : ℂ)=α₂+α₃-(r+d)-1 := by ring
    have he₃ : -(α₁+(r+d)-β-1)-1=β-α₁-(r+d) := by ring
    rw [he₁,he₂,he₃,Complex.cpow_def_of_ne_zero (one_add_exp_ne_zero ht)]
    dsimp only [ell,z₁]
    ring
  have hs (r : ℂ) (k : ℕ) : Summable
      (prodTermZ (fun n => Y₁.1 n k) (fun n => Y₂.1 n 0) f x y z
        (α₁+α₂+α₃-β-2) (α₂+α₃-r-1) z₁ 1) :=
    summable_log_product_integerCoset hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z _ _ k 0 one_ne_zero (by simpa only [norm_one] using one_lt_norm ht)
  have hrows : ∀ mu∈spectrumCosets hC2 N₅ hfg₅,
      Summable fun d : ℤ => g (spectrumCosetRep hC2 N₅ hfg₅ mu+d) := by
    intro mu hmu
    have hh := summable_sum fun k (hk : k∈Finset.range K) =>
      (hs (spectrumCosetRep hC2 N₅ hfg₅ mu) k).mul_left (ell^k)
    exact hh.congr fun d => (hrow _ d).symm
  have hsum := (tsum_spectrumCosets hC2 N₅ hfg₅ g hweight hrows).2
  change (∑' γ : ℂ,g γ)=_
  rw [hsum]
  unfold logProductSpectrumFun
  refine Finset.sum_congr rfl fun mu hmu => ?_
  rw [tsum_congr (hrow (spectrumCosetRep hC2 N₅ hfg₅ mu)),
    Summable.tsum_finsetSum (fun k _ => (hs (spectrumCosetRep hC2 N₅ hfg₅ mu) k).mul_left (ell^k)),
    fullCoset_eq_sum_log Y₂.1 hzero]
  simp only [tsum_mul_left,logProductIntegerCosetFun,VOA.Huang.AssocCoeffRules.prodFunZ,prodValueZ]
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only [ell,z₁]
  congr 2
  have he : α₁+α₂+α₃-β-2=
      (α₁+spectrumCosetRep hC2 N₅ hfg₅ mu-β-1)+
      (α₂+α₃-spectrumCosetRep hC2 N₅ hfg₅ mu-1) := by ring
  rw [he]

/-- The literal composition of the two actual completed logarithmic
evaluations has a finite convergent logarithmic collision expansion. -/
theorem completedLogProduct_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x ∈ N₁.weight α₁) (hy : y ∈ N₂.weight α₂) (hz : z ∈ N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ)  :
    VOA.Huang.LogRemovalCoeff.HasLogExp overlapDomain (fun t =>
      completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log (1+Complex.exp t)) 0
        α₁ β f ⟨x,hx⟩ y z) := by
  have hE := log_product_spectrum_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
    Y₁ Y₂ f x y z α₁ α₂ α₃ β
  exact VOA.Huang.AssocCoeffRules.hasLogExp_congr
    (fun t ht => (completedLogProduct_eq_spectrum hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz f β ht).symm) hE

end VOA.Huang.LogAssocExpansion
