import VOA.Huang.LogAssocExpansionHelpers
import VOA.Huang.AssocCoeffRules

/-! Absolute convergence of actual logarithmic product coefficients.
All five modules are genuine finitely generated grading-restricted generalized
modules. C2-cofiniteness supplies C1 reduction; the coupled logarithmic
derivative supplies the regular Euler equation. No ordinary-module or
L0-semisimplicity premise appears. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.FuchsianODE VOA.Huang.Convergence
open VOA.Huang.HuangODEAlgebra VOA.Huang.LogHuangODEProduct VOA.Huang.MatrixCoeff
open VOA.Huang.HuangODEIterPoint VOA.Huang.LogHuangODEIterPoint
open VOA.Huang.AssocExpansion VOA.Huang.FrobeniusLog VOA.Huang.LogRemovalCoeff
open VOA.Huang.AssocCoeffRules (hasLogExp_congr hasLogExp_sum)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The actual shifted coset matrix coefficient at z2=1 and z1=1+exp(t).
Every mode and complex power is kept; the global lower bound determines K. -/
noncomputable def logProductCosetFun
    (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (a b : ℂ) (k l K : ℕ) (t : ℂ) : ℂ :=
  (1+Complex.exp t)^(-a+K-1) *
    psEval (logProductShiftSeries Y₁ Y₂ f x y z a b k l K) (xt t)

/-- Every true logarithmic product coset has a finite convergent logarithmic
expansion at the collision point, including its actual outer logarithm. -/
theorem log_product_coset_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x ∈ N₁.weight α₁) (hy : y ∈ N₂.weight α₂) (hz : z ∈ N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (a b : ℂ)  :
    ∃ K : ℕ, (∀ l, IsBase (fun n => Y₂.1 n l) y z (b+K)) ∧ ∀ k l : ℕ,
      HasLogExp overlapDomain (fun t => (Complex.log (1+Complex.exp t))^k *
        logProductCosetFun Y₁.1 Y₂.1 f x y z a b k l K t) := by
  classical
  obtain ⟨s,K,hbase,hrel⟩ := exists_collision_equation_log_product hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz f a b
  refine ⟨K,hbase,?_⟩
  intro k l
  let G := logProductShiftSeries Y₁.1 Y₂.1 f x y z a b k l K
  have hG : G∈SubexpPS := by
    apply subexp_of_summable_unitDisc
    intro t ht
    have hh := summable_log_product hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f x y z (a-K) (b+K) k l ht
    refine hh.congr fun n => ?_
    simp only [G,logProductShiftSeries,coeff_mk]
    have he₁ : a-(K : ℂ)+(n : ℂ)=a+n-K := by ring
    have he₂ : b+(K : ℂ)-(n : ℂ)=b-n+K := by ring
    rw [he₁,he₂]
  let H := (1-X)^s*G
  have hH : H∈SubexpPS := SubexpPS.mul_mem (SubexpPS.pow_mem one_sub_X_mem_subexp s) hG
  let κ : ℂ := a-K+1-s
  have hF : HasLogExp overlapDomain (Ev κ s H) := hasLogExp_collision hH κ s (hrel k l κ s)
  have hGp : prodSeries (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) f x y z (a+b) (b+K)=G := by
    ext n
    simp only [coeff_prodSeries,prodCoeff,G,logProductShiftSeries,coeff_mk]
    have he₁ : a+b-(b+(K : ℂ))+(n : ℂ)=a+n-K := by ring
    have he₂ : b+(K : ℂ)-(n : ℂ)=b-n+K := by ring
    rw [he₁,he₂]
  have hRaw : HasLogExp overlapDomain
      (logProductCosetFun Y₁.1 Y₂.1 f x y z a b k l K) := by
    refine hasLogExp_congr (fun t ht => ?_) hF
    have hh := prodFun_eq_Ev (fun n => Y₁.1 n k) (fun n => Y₂.1 n l)
      f x y z (a+b) (b+K) s 0 (hGp.symm ▸ hG) ht
    rw [prodFun_eq _ _ _ _ _ _ _ _ ht,hGp] at hh
    have he : -(a+b-(b+(K : ℂ)))-1=-a+K-1 := by ring
    have heκ : a+b-(b+(K : ℂ))+1-s-(0 : ℕ)=κ := by dsimp [κ]; ring
    simp only [he,heκ,pow_zero,one_mul] at hh
    exact hh.symm
  exact hasLogExp_logOneAdd_mul hRaw k

/-- The complete actual integer mode coset at z2=1, with its outer logarithm. -/
noncomputable def logProductIntegerCosetFun
    (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃)
    (a b : ℂ) (k l : ℕ) (t : ℂ) : ℂ :=
  (Complex.log (1+Complex.exp t))^k *
    VOA.Huang.AssocCoeffRules.prodFunZ (fun n => Y₁ n k) (fun n => Y₂ n l)
      f x y z (a+b) b t

/-- The actual full integer coset has a finite convergent collision expansion. -/
theorem log_product_integerCoset_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x ∈ N₁.weight α₁) (hy : y ∈ N₂.weight α₂) (hz : z ∈ N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (a b : ℂ)  (k l : ℕ) :
    HasLogExp overlapDomain (logProductIntegerCosetFun Y₁.1 Y₂.1 f x y z a b k l) := by
  obtain ⟨K,hbase,hE⟩ := log_product_coset_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz f a b
  refine hasLogExp_congr (fun t ht => ?_) (hE k l)
  dsimp only [logProductIntegerCosetFun]
  congr 1
  have hShift := VOA.Huang.AssocCoeffRules.prodFunZ_shift
    (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) f x y z (a+b) b (K : ℤ) t
  simp only [Int.cast_natCast] at hShift
  rw [← hShift,VOA.Huang.AssocCoeffRules.prodFunZ_eq_prodFun f x (hbase l) t,
    prodFun_eq _ _ _ _ _ _ _ _ ht]
  unfold logProductCosetFun
  have hGp : prodSeries (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) f x y z (a+b) (b+K)=
      logProductShiftSeries Y₁.1 Y₂.1 f x y z a b k l K := by
    ext n
    simp only [coeff_prodSeries,prodCoeff,logProductShiftSeries,coeff_mk]
    have he₁ : a+b-(b+(K : ℂ))+(n : ℂ)=a+n-K := by ring
    have he₂ : b+(K : ℂ)-(n : ℂ)=b-n+K := by ring
    rw [he₁,he₂]
  rw [hGp]
  have he : -(a+b-(b+(K : ℂ)))-1=-a+K-1 := by ring
  rw [he]
  rfl

/-- The genuine entire logarithmic product on one integer mode coset at
z2=1: all outer logarithmic degrees are summed, and log(1)=0 selects the
inner zeroth degree. The actual global Jordan bound makes this sum finite. -/
noncomputable def logProductFullCosetFun
    (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b t : ℂ) : ℂ :=
  ∑' k : ℕ,logProductIntegerCosetFun Y₁ Y₂ f x y z a b k 0 t

/-- All logarithmic degrees of the actual product have a finite convergent
collision expansion, with their genuine generalized-module Jordan bounds. -/
theorem log_product_fullCoset_hasLogExp (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x ∈ N₁.weight α₁) (hy : y ∈ N₂.weight α₂) (hz : z ∈ N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (a b : ℂ)  :
    HasLogExp overlapDomain (logProductFullCosetFun Y₁.1 Y₂.1 f x y z a b) := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  have hE : HasLogExp overlapDomain (fun t =>
      ∑ k∈Finset.range K,logProductIntegerCosetFun Y₁.1 Y₂.1 f x y z a b k 0 t) :=
    hasLogExp_sum _ fun k _ => log_product_integerCoset_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz f a b k 0
  refine hasLogExp_congr (fun t _ => ?_) hE
  unfold logProductFullCosetFun
  refine (tsum_eq_sum (s := Finset.range K) fun k hk => ?_).symm
  have hk' : K≤k := by simpa only [Finset.mem_range,not_lt] using hk
  simp only [logProductIntegerCosetFun,VOA.Huang.AssocCoeffRules.prodFunZ,
    VOA.Huang.AssocCommutator.prodValueZ,VOA.Huang.AssocCommutator.prodTermZ,prodCoeff,
    hK Y₁ _ k hk',LinearMap.zero_apply,map_zero,zero_mul,tsum_zero,mul_zero]

end VOA.Huang.LogAssocExpansion
