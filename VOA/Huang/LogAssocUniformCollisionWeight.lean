import VOA.Huang.LogAssocRenormalizedExpansion
import VOA.Huang.LogAssocExpansionHelpers
import VOA.Huang.LogHuangODEIterPointGenerators
import VOA.Huang.LogRemovalBound
import VOA.Huang.LogRemovalWeightBound

/-! Every actual collision-renormalized tuple has a genuine logarithmic
Frobenius expansion with a common normalization. This exposes the finite
base tuples used for uniform generalized-module coefficient bounds. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEIterPoint
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.HuangODEAlgebra
open VOA.Huang.FuchsianODE
open VOA.Huang.LogHuangODEProduct VOA.Huang.LogAssocExpansion
open VOA.Huang.HuangODEIterPoint VOA.Huang.AssocExpansion
open VOA.Huang.LogRemovalCoeff VOA.Huang.LogRemovalBound
open VOA.Huang.LogRemovalWeightBound
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- A single genuine collision-exponent lower bound covers all tuple levels and all
actual original log degrees on fixed lower generalized coset bases. -/
theorem exists_uniform_collision_weight_bound (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {h₁ h₂ h₃ h₄ ν : ℂ} {B₁ B₂ B₃ B₄ : ℕ}
    (hl₁ : CosetBase N₁.toGW h₁) (hl₂ : CosetBase N₂.toGW h₂)
    (hl₃ : CosetBase N₃.toGW h₃) (hl₄ : CosetBase N₄.toGW h₄)
    (hUB : ∀ l,UnifBase N₂.toGW N₃.toGW (fun n => Y₂.1 n l) h₂ h₃ ν)
    (hC₁ : C1Graded N₁.toGW h₁ B₁) (hC₂ : C1Graded N₂.toGW h₂ B₂)
    (hC₃ : C1Graded N₃.toGW h₃ B₃) (hD₄ : DualC1Graded N₄.toGW h₄ B₄)
 :
    ∃ M : ℝ,∀ (n₁ n₂ n₃ n₄ k l : ℕ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃),
      x∈N₁.weight (h₁+n₁) → y∈N₂.weight (h₂+n₂) → z∈N₃.weight (h₃+n₃) →
      ExpGE M (Phi (h₁+h₂+h₃-h₄-2-ν)
        ((1-X)^(n₁+n₂+n₃+n₄)*
          QT (fun n => Y₁.1 n k) (fun n => Y₂.1 n l) (h₁+h₂+h₃-h₄-2) ν f x y z n₄
            (n₁+n₂+n₃+n₄))) := by
  classical
  obtain ⟨K₁,hK₁⟩ := uniform_log_degree_of_finGen N₁ N₅ N₄ hfg₁ hfg₅ hfg₄
  obtain ⟨K₂,hK₂⟩ := uniform_log_degree_of_finGen N₂ N₃ N₅ hfg₂ hfg₃ hfg₅
  have hJ₁ (q : ℕ) := logCoefficient_isGradedJacobi Y₁.2 q
  have hJ₂ (q : ℕ) := logCoefficient_isGradedJacobi Y₂.2 q
  let I := (Fin K₁×Fin K₂)×(Fin (B₁+1)×Fin (B₂+1)×Fin (B₃+1)×Fin (B₄+1))
  choose T hTfin hTform hTspan using fun q : I =>
    exists_finite_span_actual (h₁ := h₁) (h₂ := h₂) (h₃ := h₃) (h₄ := h₄) (ν := ν)
      (hJ₁ q.1.1) (hJ₂ q.1.2) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  let lev : I → ℕ := fun q => (q.2.1 : ℕ)+(q.2.2.1 : ℕ)+(q.2.2.2.1 : ℕ)+(q.2.2.2.2 : ℕ)
  let S : Set (PowerSeries ℂ) := ⋃ q,(fun g => (1-X)^(lev q)*g) '' T q
  have hSfin : S.Finite := Set.finite_iUnion fun q => (hTfin q).image _
  let c := h₁+h₂+h₃-h₄-2
  have hSgood : ∀ Z∈S,∃ M,Z∈expModule (c-ν) M := by
    intro Z hZS
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hZS
    obtain ⟨g,hg,rfl⟩ := hq
    obtain ⟨f,x,y,z,hx,hy,hz,rfl⟩ := hTform q g hg
    have hE := renormalized_QT_hasLogExp hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ hl₁ hl₂ hl₃ hl₄ hUB hC₁ hC₂ hC₃ hD₄
      q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 q.1.1 q.1.2 f x y z hx hy hz
    obtain ⟨M,hK⟩ := exists_expGE hE
    refine ⟨M,?_,hK⟩
    apply SubexpPS.mul_mem (SubexpPS.pow_mem one_sub_X_mem_subexp (lev q))
    apply subexp_of_summable_unitDisc
    intro t ht
    have hh := summable_log_product hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
      f x y z (c-ν-2*q.2.2.2.2) (ν+lev q) q.1.1 q.1.2 ht
    refine hh.congr fun n => ?_
    simp only [QT,coeff_prodQ,c,lev]
  choose! MZ hKZ using hSgood
  let M : ℝ := -∑ Z∈hSfin.toFinset,|MZ Z|
  have hSK : ∀ Z∈S,Z∈expModule (c-ν) M := by
    intro Z hZS
    obtain ⟨h₁',h₂'⟩ := hKZ Z hZS
    have hle : M≤MZ Z := by
      have hh : |MZ Z|≤∑ Y∈hSfin.toFinset,|MZ Y| :=
        Finset.single_le_sum (fun Y _ => abs_nonneg (MZ Y)) (hSfin.mem_toFinset.mpr hZS)
      exact (neg_le_neg hh).trans (neg_abs_le (MZ Z))
    exact ⟨h₁',h₂'.mono hle⟩
  let NN := expModule (c-ν) M
  refine ⟨M,?_⟩
  intro n₁ n₂ n₃ n₄ k l f x y z hx hy hz
  by_cases hk : K₁≤k
  · rw [QT_zero_log_left _ _ _ _ _ _ _ _ _ _ (fun n => hK₁ Y₁ n k hk),mul_zero]
    exact (NN.zero_mem).2
  by_cases hl : K₂≤l
  · rw [QT_zero_log_right _ _ _ _ _ _ _ _ _ _ (fun n => hK₂ Y₂ n l hl),mul_zero]
    exact (NN.zero_mem).2
  have hbase : ∀ (m₁ m₂ m₃ m₄ : ℕ),m₁≤B₁ → m₂≤B₂ → m₃≤B₃ → m₄≤B₄ →
      ∀ (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃),x∈N₁.weight (h₁+m₁) →
        y∈N₂.weight (h₂+m₂) → z∈N₃.weight (h₃+m₃) →
        (1-X)^(m₁+m₂+m₃+m₄)*QT (fun n => Y₁.1 n k) (fun n => Y₂.1 n l)
          c ν f x y z m₄ (m₁+m₂+m₃+m₄)∈NN := by
    intro m₁ m₂ m₃ m₄ b₁ b₂ b₃ b₄ f x y z hx hy hz
    let q : I := ((⟨k,by omega⟩,⟨l,by omega⟩),
      (⟨m₁,by omega⟩,⟨m₂,by omega⟩,⟨m₃,by omega⟩,⟨m₄,by omega⟩))
    have hmem := hTspan q f x y z hx hy hz
    have hmem' : (1-X)^(m₁+m₂+m₃+m₄)*QT (fun n => Y₁.1 n k) (fun n => Y₂.1 n l)
        c ν f x y z m₄ (m₁+m₂+m₃+m₄)∈
        Submodule.span ℂ ((fun g => (1-X)^(lev q)*g) '' T q) := by
      have hh := Submodule.mem_map_of_mem (f := LinearMap.mulLeft ℂ ((1-X)^(lev q))) hmem
      rw [Submodule.map_span] at hh
      exact hh
    have hle : Submodule.span ℂ ((fun g => (1-X)^(lev q)*g) '' T q)≤NN.restrictScalars ℂ := by
      rw [Submodule.span_le]
      intro Z hZ
      exact hSK Z (Set.mem_iUnion.mpr ⟨q,hZ⟩)
    exact hle hmem'
  have hall := pt_mem (hJ₁ k) (hJ₂ l) hl₁ hl₂ hl₃ hl₄ (hUB l) hC₁ hC₂ hC₃ hD₄ NN hbase
  exact (hall _ n₁ n₂ n₃ n₄ rfl f x y z hx hy hz).2

end VOA.Huang.LogHuangODEIterPoint
