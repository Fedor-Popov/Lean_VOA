/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.LogAssocCompletedIterate
import VOA.Huang.LogAssocCompletedProduct

/-! # O3: summability of completed iterates and products

The proofs of `completedLogIterate_eq_lowerSpectrum` and `completedLogProduct_eq_spectrum`
establish that the weight sums defining the completed iterate and the completed product are
summable (the first component of `tsum_lowerSpectrum` / `tsum_spectrumCosets`). That fact is
not exported there; it is restated here with the same proof, for use in O3 associativity.
-/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.FrobeniusLog
open VOA.Huang.LogHuangODEIterate VOA.Huang.AssocExpansion
open VOA.Huang.HuangODEIterPoint
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The outer block at the zero branch is the log-degree-0 coefficient. -/
theorem pointEvaluationBlock_zero'
    (A₁ : LogVModule W M₅) (A₂ : LogVModule W M₃) (A₃ : LogVModule W M₄)
    (Y : LogIntertwiningOperator A₁.toWeakModule A₂.toWeakModule A₃.toWeakModule)
    (a b c : ℂ) (x : A₁.weight a) (y : A₂.weight b) :
    (pointEvaluationBlock A₁ A₂ A₃ Y 0 a b c x y : M₄)=Y.1 (a+b-c-1) 0 x y := by
  unfold pointEvaluationBlock
  simp only [zero_mul,Complex.exp_zero,one_smul]
  rw [Finset.sum_eq_single 0]
  · simp [logarithmicBlock]
  · intro k hk hk0
    rw [zero_pow hk0,zero_smul]
  · intro hh
    exfalso
    apply hh
    simp only [Finset.mem_range,pointLogCutoff]
    omega

/-- The weight sum of a completed iterate is summable on the overlap. -/
theorem completedLogIterate_summable (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {α₁ α₂ α₃ : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight α₁) (hy : y∈N₂.weight α₂) (hz : z∈N₃.weight α₃)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    Summable fun γ : ℂ => f (pointEvaluationBlock N₅ N₃ N₄ Y₃ 0 γ α₃ β
      (evaluatePoint N₁ N₂ N₅ Y₄ t x y γ) ⟨z,hz⟩) := by
  classical
  let q := evaluatePoint N₁ N₂ N₅ Y₄ t x y
  let g : ℂ → ℂ := fun γ => f (pointEvaluationBlock N₅ N₃ N₄ Y₃ 0 γ α₃ β (q γ) ⟨z,hz⟩)
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₁ N₂ N₅ hfg₁ hfg₂ hfg₅
  have hzero : ∀ n l,K≤l → Y₄.1 n l=0 := fun n l hl => hK Y₄ n l hl
  have hq (γ : ℂ) : (q γ : M₅)=Complex.exp (t*(γ-α₁-α₂)) •
      ∑ l∈Finset.range K,t^l•Y₄.1 (α₁+α₂-γ-1) l x y := by
    dsimp only [q]
    rw [evaluatePoint,fromBlocks_homogeneous N₁ N₂ _ hx hy]
    exact pointEvaluationBlock_fixed_cutoff N₁ N₂ N₅ Y₄ t α₁ α₂ γ ⟨x,hx⟩ ⟨y,hy⟩ K
      (fun l hl => by rw [hzero _ l hl]; rfl)
  have hg (γ : ℂ) : g γ=Complex.exp (t*(γ-α₁-α₂)) *
      ∑ l∈Finset.range K,t^l*f (Y₃.1 (γ+α₃-β-1) 0 (Y₄.1 (α₁+α₂-γ-1) l x y) z) := by
    dsimp only [g]
    rw [pointEvaluationBlock_zero' N₅ N₃ N₄ Y₃ γ α₃ β (q γ) ⟨z,hz⟩]
    rw [hq,map_smul,LinearMap.smul_apply,map_smul,map_sum,LinearMap.sum_apply,map_sum]
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  have hweight : ∀ γ,g γ≠0 → N₅.weight γ≠⊥ := by
    intro γ hγ he
    have hq0 : q γ=0 := by
      apply Subtype.ext
      have hbot : N₅.weight γ≤(⊥ : Submodule ℂ M₅) := by rw [he]
      exact (Submodule.mem_bot ℂ).mp (hbot (q γ).2)
    apply hγ
    simp only [g,hq0,map_zero,LinearMap.zero_apply,Submodule.coe_zero]
  have hrow (r : ℂ) (n : ℕ) : g (r+n)=
      ∑ l∈Finset.range K,t^l*Complex.exp ((r-α₁-α₂)*t)*
        (PowerSeries.coeff n (logIterateLowerCosetSeries Y₃.1 Y₄.1 f x y z α₁ α₂ α₃ β r l)*
          (Complex.exp t)^n) := by
    rw [hg,Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [logIterateLowerCosetSeries,PowerSeries.coeff_mk]
    have he : Complex.exp (t*(r+(n : ℂ)-α₁-α₂))=
        Complex.exp ((r-α₁-α₂)*t)*(Complex.exp t)^n := by
      rw [show t*(r+(n : ℂ)-α₁-α₂)=(r-α₁-α₂)*t+(n : ℂ)*t by ring,
        Complex.exp_add,Complex.exp_nat_mul]
    rw [he]
    have hn : α₁+α₂-(r+(n : ℂ))-1=α₁+α₂-r-1-n := by ring
    have ho : r+(n : ℂ)+α₃-β-1=r+α₃-β-1+n := by ring
    rw [hn,ho]
    ring
  have hs (r : ℂ) (l : ℕ) : Summable fun n : ℕ =>
      PowerSeries.coeff n (logIterateLowerCosetSeries Y₃.1 Y₄.1 f x y z α₁ α₂ α₃ β r l)*(Complex.exp t)^n := by
    simpa only [logIterateLowerCosetSeries,PowerSeries.coeff_mk] using
      summable_log_iterate_series hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄
        f x y z (r+α₃-β-1) (α₁+α₂-r-1) 0 l (by rw [Complex.norm_exp]; exact Real.exp_lt_one_iff.mpr ht.1)
  have hrows : ∀ mu∈spectrumCosets hC2 N₅ hfg₅,
      Summable fun n : ℕ => g (lowerSpectrumRep hC2 N₅ hfg₅ mu+n) := by
    intro mu hmu
    have hh := summable_sum fun l (hl : l∈Finset.range K) =>
      (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) l).mul_left
        (t^l*Complex.exp ((lowerSpectrumRep hC2 N₅ hfg₅ mu-α₁-α₂)*t))
    exact hh.congr fun n => (hrow _ n).symm
  exact (tsum_lowerSpectrum hC2 N₅ hfg₅ g hweight hrows).1

open VOA.Huang.MatrixCoeff
open VOA.Huang.AssocCommutator (prodTermZ prodValueZ)
open VOA.Huang.LogAssocJacobi (summable_log_product_integerCoset)

/-- The weight sum of a completed product is summable on the overlap. -/
theorem completedLogProduct_summable (hC2 : C2Cofinite W)
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
    Summable fun γ : ℂ => f (pointEvaluationBlock N₁ N₅ N₄ Y₁ (Complex.log (1+Complex.exp t))
      α₁ γ β ⟨x,hx⟩ (evaluatePoint N₂ N₃ N₅ Y₂ 0 y z γ)) := by
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
  exact (tsum_spectrumCosets hC2 N₅ hfg₅ g hweight hrows).1

end VOA.Huang.LogAssocExpansion
