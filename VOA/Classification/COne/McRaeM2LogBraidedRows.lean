import VOA.Huang.LogAssocCompletedIterate
import VOA.Huang.LogAssocCompletedProduct
import VOA.Huang.LogHuangODEProductMain
import VOA.Huang.CommutativityAnalytic

/-! # Completed logarithmic iterates and products at two free branches

For homogeneous inputs, the literal completed iterate at independent chosen
branches `ℓ₀` (inner) and `ℓ₂` (outer) is, on `Re ℓ₀ < Re ℓ₂`, the finite sum over
the lower spectrum rows of the intermediate module and the logarithmic degrees of
`e^{ℓ₀(ρ-a-b)} e^{ℓ₂(β-ρ-c)} ℓ₀^l ℓ₂^k · Σₙ cₙ (e^{ℓ₀-ℓ₂})ⁿ`, with every row series
convergent on the unit disc (`completedLogIterate_eq_iterValue`). The same holds
for completed products in `e^{m₂-m₁}` (`completedLogProduct_eq_prodValue`).
Consequently both are holomorphic in the pair of branches on these open sets
(`differentiableOn_iterValue`, `differentiableOn_prodValue`), with no branch cut. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogBraided
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-! ## Rows -/

/-- One literal iterate coefficient row. -/
def iterRow (Y₃ : LogModes M₅ M₃ M₄) (Y₄ : LogModes M₁ M₂ M₅) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (A B : ℂ) (k l : ℕ) (n : ℕ) : ℂ :=
  f (Y₃ (A+n) k (Y₄ (B-n) l x y) z)

/-- One literal product coefficient row. -/
def prodRow (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (A B : ℂ) (k l : ℕ) (n : ℕ) : ℂ :=
  f (Y₁ (A+n) k x (Y₂ (B-n) l y z))

/-- The value of a coefficient row on the unit disc. -/
def rowEval (c : ℕ → ℂ) (w : ℂ) : ℂ := ∑' n : ℕ, c n * w^n

/-- The finite lower-spectrum expansion of a completed iterate. -/
def iterValue (hC2 : C2Cofinite W) (N₅ : LogVModule W M₅) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogModes M₅ M₃ M₄) (Y₄ : LogModes M₁ M₂ M₅) (K L : ℕ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (a b c β ℓ₀ ℓ₂ : ℂ) : ℂ :=
  ∑ mu∈spectrumCosets hC2 N₅ hfg₅, ∑ k∈Finset.range K, ∑ l∈Finset.range L,
    Complex.exp (ℓ₀*(lowerSpectrumRep hC2 N₅ hfg₅ mu-a-b)) *
      Complex.exp (ℓ₂*(β-lowerSpectrumRep hC2 N₅ hfg₅ mu-c)) * ℓ₀^l * ℓ₂^k *
      rowEval (iterRow Y₃ Y₄ f x y z (lowerSpectrumRep hC2 N₅ hfg₅ mu+c-β-1)
        (a+b-lowerSpectrumRep hC2 N₅ hfg₅ mu-1) k l) (Complex.exp (ℓ₀-ℓ₂))

/-- The finite lower-spectrum expansion of a completed product. -/
def prodValue (hC2 : C2Cofinite W) (N₅ : LogVModule W M₅) (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogModes M₁ M₅ M₄) (Y₂ : LogModes M₂ M₃ M₅) (K L : ℕ) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (a b c β m₁ m₂ : ℂ) : ℂ :=
  ∑ mu∈spectrumCosets hC2 N₅ hfg₅, ∑ k∈Finset.range K, ∑ l∈Finset.range L,
    Complex.exp (m₁*(β-a-lowerSpectrumRep hC2 N₅ hfg₅ mu)) *
      Complex.exp (m₂*(lowerSpectrumRep hC2 N₅ hfg₅ mu-b-c)) * m₁^k * m₂^l *
      rowEval (prodRow Y₁ Y₂ f x y z (a+lowerSpectrumRep hC2 N₅ hfg₅ mu-β-1)
        (b+c-lowerSpectrumRep hC2 N₅ hfg₅ mu-1) k l) (Complex.exp (m₂-m₁))

theorem norm_exp_sub_lt_one {p q : ℂ} (h : p.re < q.re) : ‖Complex.exp (p-q)‖ < 1 := by
  rw [Complex.norm_exp, Complex.sub_re]
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-! ## The iterate -/

/-- The literal completed iterate at two free branches is its finite
lower-spectrum expansion, and its weight series is summable. -/
theorem completedLogIterate_eq_iterValue (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    {K L : ℕ} (hK : ∀ n k, K ≤ k → Y₃.1 n k = 0) (hL : ∀ n l, L ≤ l → Y₄.1 n l = 0)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {ℓ₀ ℓ₂ : ℂ} (hlt : ℓ₀.re < ℓ₂.re) :
    Summable (fun γ : ℂ => f (pointEvaluationBlock N₅ N₃ N₄ Y₃ ℓ₂ γ c β
        (evaluatePoint N₁ N₂ N₅ Y₄ ℓ₀ x y γ) ⟨z,hz⟩)) ∧
    completedLogIterate N₁ N₂ N₃ N₄ N₅ Y₃ Y₄ ℓ₀ ℓ₂ c β f x y ⟨z,hz⟩ =
      iterValue hC2 N₅ hfg₅ Y₃.1 Y₄.1 K L f x y z a b c β ℓ₀ ℓ₂ := by
  classical
  let q := evaluatePoint N₁ N₂ N₅ Y₄ ℓ₀ x y
  let g : ℂ → ℂ := fun γ => f (pointEvaluationBlock N₅ N₃ N₄ Y₃ ℓ₂ γ c β (q γ) ⟨z,hz⟩)
  have hq (γ : ℂ) : (q γ : M₅) = Complex.exp (ℓ₀*(γ-a-b)) •
      ∑ l∈Finset.range L, ℓ₀^l • Y₄.1 (a+b-γ-1) l x y := by
    dsimp only [q]
    rw [evaluatePoint, fromBlocks_homogeneous N₁ N₂ _ hx hy]
    exact pointEvaluationBlock_fixed_cutoff N₁ N₂ N₅ Y₄ ℓ₀ a b γ ⟨x,hx⟩ ⟨y,hy⟩ L
      (fun l hl => by rw [hL _ l hl]; rfl)
  have hg (γ : ℂ) : g γ = ∑ k∈Finset.range K, ∑ l∈Finset.range L,
      Complex.exp (ℓ₀*(γ-a-b)) * Complex.exp (ℓ₂*(β-γ-c)) * ℓ₀^l * ℓ₂^k *
        f (Y₃.1 (γ+c-β-1) k (Y₄.1 (a+b-γ-1) l x y) z) := by
    dsimp only [g]
    rw [pointEvaluationBlock_fixed_cutoff N₅ N₃ N₄ Y₃ ℓ₂ γ c β (q γ) ⟨z,hz⟩ K
      (fun k hk => by rw [hK _ k hk]; rfl)]
    rw [map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    change Complex.exp (ℓ₂*(β-γ-c)) * (ℓ₂^k * f (Y₃.1 (γ+c-β-1) k (q γ : M₅) z)) = _
    rw [hq, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, map_sum,
      LinearMap.sum_apply, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
    ring
  have hweight : ∀ γ, g γ ≠ 0 → N₅.weight γ ≠ ⊥ := by
    intro γ hγ he
    have hq0 : q γ = 0 := by
      apply Subtype.ext
      have hbot : N₅.weight γ ≤ (⊥ : Submodule ℂ M₅) := by rw [he]
      exact (Submodule.mem_bot ℂ).mp (hbot (q γ).2)
    apply hγ
    simp only [g, hq0, map_zero, LinearMap.zero_apply, Submodule.coe_zero]
  have ht : ‖Complex.exp (ℓ₀-ℓ₂)‖ < 1 := norm_exp_sub_lt_one hlt
  have hs (r : ℂ) (k l : ℕ) : Summable fun n : ℕ =>
      iterRow Y₃.1 Y₄.1 f x y z (r+c-β-1) (a+b-r-1) k l n * Complex.exp (ℓ₀-ℓ₂)^n :=
    VOA.Huang.LogHuangODEIterate.summable_log_iterate_series hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ f x y z _ _ k l ht
  have hrow (r : ℂ) (n : ℕ) : g (r+n) = ∑ k∈Finset.range K, ∑ l∈Finset.range L,
      Complex.exp (ℓ₀*(r-a-b)) * Complex.exp (ℓ₂*(β-r-c)) * ℓ₀^l * ℓ₂^k *
        (iterRow Y₃.1 Y₄.1 f x y z (r+c-β-1) (a+b-r-1) k l n * Complex.exp (ℓ₀-ℓ₂)^n) := by
    rw [hg]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have he : Complex.exp (ℓ₀*(r+n-a-b)) * Complex.exp (ℓ₂*(β-(r+n)-c)) =
        Complex.exp (ℓ₀*(r-a-b)) * Complex.exp (ℓ₂*(β-r-c)) * Complex.exp (ℓ₀-ℓ₂)^n := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    have h1 : r+(n : ℂ)+c-β-1 = r+c-β-1+n := by ring
    have h2 : a+b-(r+(n : ℂ))-1 = a+b-r-1-n := by ring
    simp only [iterRow, h1, h2]
    linear_combination (ℓ₀^l * ℓ₂^k *
      f (Y₃.1 (r+c-β-1+n) k (Y₄.1 (a+b-r-1-n) l x y) z)) * he
  have hrows : ∀ mu∈spectrumCosets hC2 N₅ hfg₅,
      Summable fun n : ℕ => g (lowerSpectrumRep hC2 N₅ hfg₅ mu+n) := by
    intro mu _
    have hh := summable_sum fun k (_ : k∈Finset.range K) => summable_sum fun l
      (_ : l∈Finset.range L) => (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) k l).mul_left
        (Complex.exp (ℓ₀*(lowerSpectrumRep hC2 N₅ hfg₅ mu-a-b)) *
          Complex.exp (ℓ₂*(β-lowerSpectrumRep hC2 N₅ hfg₅ mu-c)) * ℓ₀^l * ℓ₂^k)
    exact hh.congr fun n => (hrow _ n).symm
  obtain ⟨hsum, hval⟩ := tsum_lowerSpectrum hC2 N₅ hfg₅ g hweight hrows
  refine ⟨hsum, ?_⟩
  change (∑' γ : ℂ, g γ) = _
  rw [hval]
  unfold iterValue
  refine Finset.sum_congr rfl fun mu _ => ?_
  rw [tsum_congr (hrow (lowerSpectrumRep hC2 N₅ hfg₅ mu)),
    Summable.tsum_finsetSum (fun k _ => summable_sum fun l (_ : l∈Finset.range L) =>
      (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) k l).mul_left _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Summable.tsum_finsetSum (fun l _ => (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) k l).mul_left _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tsum_mul_left]
  rfl

/-! ## The product -/

/-- The literal completed product at two free branches is its finite
lower-spectrum expansion, and its weight series is summable. -/
theorem completedLogProduct_eq_prodValue (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    {K L : ℕ} (hK : ∀ n k, K ≤ k → Y₁.1 n k = 0) (hL : ∀ n l, L ≤ l → Y₂.1 n l = 0)
    {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {m₁ m₂ : ℂ} (hlt : m₂.re < m₁.re) :
    Summable (fun γ : ℂ => f (pointEvaluationBlock N₁ N₅ N₄ Y₁ m₁ a γ β ⟨x,hx⟩
        (evaluatePoint N₂ N₃ N₅ Y₂ m₂ y z γ))) ∧
    completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ m₁ m₂ a β f ⟨x,hx⟩ y z =
      prodValue hC2 N₅ hfg₅ Y₁.1 Y₂.1 K L f x y z a b c β m₁ m₂ := by
  classical
  let q := evaluatePoint N₂ N₃ N₅ Y₂ m₂ y z
  let g : ℂ → ℂ := fun γ => f (pointEvaluationBlock N₁ N₅ N₄ Y₁ m₁ a γ β ⟨x,hx⟩ (q γ))
  have hq (γ : ℂ) : (q γ : M₅) = Complex.exp (m₂*(γ-b-c)) •
      ∑ l∈Finset.range L, m₂^l • Y₂.1 (b+c-γ-1) l y z := by
    dsimp only [q]
    rw [evaluatePoint, fromBlocks_homogeneous N₂ N₃ _ hy hz]
    exact pointEvaluationBlock_fixed_cutoff N₂ N₃ N₅ Y₂ m₂ b c γ ⟨y,hy⟩ ⟨z,hz⟩ L
      (fun l hl => by rw [hL _ l hl]; rfl)
  have hg (γ : ℂ) : g γ = ∑ k∈Finset.range K, ∑ l∈Finset.range L,
      Complex.exp (m₁*(β-a-γ)) * Complex.exp (m₂*(γ-b-c)) * m₁^k * m₂^l *
        f (Y₁.1 (a+γ-β-1) k x (Y₂.1 (b+c-γ-1) l y z)) := by
    dsimp only [g]
    rw [pointEvaluationBlock_fixed_cutoff N₁ N₅ N₄ Y₁ m₁ a γ β ⟨x,hx⟩ (q γ) K
      (fun k hk => by rw [hK _ k hk]; rfl)]
    rw [map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    change Complex.exp (m₁*(β-a-γ)) * (m₁^k * f (Y₁.1 (a+γ-β-1) k x (q γ : M₅))) = _
    rw [hq, map_smul, map_smul, smul_eq_mul, map_sum, map_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
    ring
  have hweight : ∀ γ, g γ ≠ 0 → N₅.weight γ ≠ ⊥ := by
    intro γ hγ he
    have hq0 : q γ = 0 := by
      apply Subtype.ext
      have hbot : N₅.weight γ ≤ (⊥ : Submodule ℂ M₅) := by rw [he]
      exact (Submodule.mem_bot ℂ).mp (hbot (q γ).2)
    apply hγ
    simp only [g, hq0, map_zero, Submodule.coe_zero]
  have ht : ‖Complex.exp (m₂-m₁)‖ < 1 := norm_exp_sub_lt_one hlt
  have hs (r : ℂ) (k l : ℕ) : Summable fun n : ℕ =>
      prodRow Y₁.1 Y₂.1 f x y z (a+r-β-1) (b+c-r-1) k l n * Complex.exp (m₂-m₁)^n :=
    VOA.Huang.LogHuangODEProduct.summable_log_product_series hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z _ _ k l ht
  have hrow (r : ℂ) (n : ℕ) : g (r+n) = ∑ k∈Finset.range K, ∑ l∈Finset.range L,
      Complex.exp (m₁*(β-a-r)) * Complex.exp (m₂*(r-b-c)) * m₁^k * m₂^l *
        (prodRow Y₁.1 Y₂.1 f x y z (a+r-β-1) (b+c-r-1) k l n * Complex.exp (m₂-m₁)^n) := by
    rw [hg]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have he : Complex.exp (m₁*(β-a-(r+n))) * Complex.exp (m₂*(r+n-b-c)) =
        Complex.exp (m₁*(β-a-r)) * Complex.exp (m₂*(r-b-c)) * Complex.exp (m₂-m₁)^n := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    have h1 : a+(r+(n : ℂ))-β-1 = a+r-β-1+n := by ring
    have h2 : b+c-(r+(n : ℂ))-1 = b+c-r-1-n := by ring
    simp only [prodRow, h1, h2]
    linear_combination (m₁^k * m₂^l *
      f (Y₁.1 (a+r-β-1+n) k x (Y₂.1 (b+c-r-1-n) l y z))) * he
  have hrows : ∀ mu∈spectrumCosets hC2 N₅ hfg₅,
      Summable fun n : ℕ => g (lowerSpectrumRep hC2 N₅ hfg₅ mu+n) := by
    intro mu _
    have hh := summable_sum fun k (_ : k∈Finset.range K) => summable_sum fun l
      (_ : l∈Finset.range L) => (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) k l).mul_left
        (Complex.exp (m₁*(β-a-lowerSpectrumRep hC2 N₅ hfg₅ mu)) *
          Complex.exp (m₂*(lowerSpectrumRep hC2 N₅ hfg₅ mu-b-c)) * m₁^k * m₂^l)
    exact hh.congr fun n => (hrow _ n).symm
  obtain ⟨hsum, hval⟩ := tsum_lowerSpectrum hC2 N₅ hfg₅ g hweight hrows
  refine ⟨hsum, ?_⟩
  change (∑' γ : ℂ, g γ) = _
  rw [hval]
  unfold prodValue
  refine Finset.sum_congr rfl fun mu _ => ?_
  rw [tsum_congr (hrow (lowerSpectrumRep hC2 N₅ hfg₅ mu)),
    Summable.tsum_finsetSum (fun k _ => summable_sum fun l (_ : l∈Finset.range L) =>
      (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) k l).mul_left _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Summable.tsum_finsetSum (fun l _ => (hs (lowerSpectrumRep hC2 N₅ hfg₅ mu) k l).mul_left _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tsum_mul_left]
  rfl

/-! ## Holomorphy in the two branches -/

/-- A row whose series converges absolutely at every radius below one is
holomorphic on the unit disc. -/
theorem analyticOnNhd_rowEval {c : ℕ → ℂ}
    (hc : ∀ t : ℂ, ‖t‖ < 1 → Summable fun n => ‖c n * t^n‖) :
    AnalyticOnNhd ℂ (rowEval c) (Metric.ball 0 1) := by
  have h := VOA.Huang.CommutativityTarget.analyticOnNhd_tsum_pow c (fun r hr0 hr1 => by
    have hh := hc (r : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    refine hh.congr fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0])
  exact h

/-- Composite of a disc-holomorphic row with `e^{p-q}` is holomorphic on `Re p < Re q`. -/
theorem differentiableAt_rowEval_exp {c : ℕ → ℂ}
    (hc : ∀ t : ℂ, ‖t‖ < 1 → Summable fun n => ‖c n * t^n‖) {p : ℂ × ℂ}
    (hp : p.1.re < p.2.re) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => rowEval c (Complex.exp (p.1-p.2))) p := by
  have hmem : Complex.exp (p.1-p.2) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact norm_exp_sub_lt_one hp
  have h1 := ((analyticOnNhd_rowEval hc) _ hmem).differentiableAt
  have h2 : DifferentiableAt ℂ (fun p : ℂ × ℂ => Complex.exp (p.1-p.2)) p :=
    (differentiableAt_fst.sub differentiableAt_snd).cexp
  exact h1.comp p h2

theorem isOpen_re_lt_pair : IsOpen {p : ℂ × ℂ | p.1.re < p.2.re} :=
  isOpen_lt (Complex.continuous_re.comp continuous_fst) (Complex.continuous_re.comp continuous_snd)

/-- The iterate expansion is holomorphic in both branches on `Re ℓ₀ < Re ℓ₂`. -/
theorem differentiableOn_iterValue (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₃ : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y₄ : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₅.toWeakModule)
    (K L : ℕ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β : ℂ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      iterValue hC2 N₅ hfg₅ Y₃.1 Y₄.1 K L f x y z a b c β p.1 p.2)
      {p : ℂ × ℂ | p.1.re < p.2.re} := by
  intro p hp
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold iterValue
  refine DifferentiableAt.fun_sum fun mu _ => DifferentiableAt.fun_sum fun k _ =>
    DifferentiableAt.fun_sum fun l _ => ?_
  refine DifferentiableAt.mul ?_ (differentiableAt_rowEval_exp (fun t ht =>
    VOA.Huang.LogHuangODEIterate.summable_log_iterate hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₃ Y₄ f x y z _ _ k l ht) hp)
  fun_prop

/-- The product expansion is holomorphic in both branches on `Re m₂ < Re m₁`. -/
theorem differentiableOn_prodValue (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (K L : ℕ) (f : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β : ℂ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      prodValue hC2 N₅ hfg₅ Y₁.1 Y₂.1 K L f x y z a b c β p.1 p.2)
      {p : ℂ × ℂ | p.2.re < p.1.re} := by
  intro p hp
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold prodValue
  refine DifferentiableAt.fun_sum fun mu _ => DifferentiableAt.fun_sum fun k _ =>
    DifferentiableAt.fun_sum fun l _ => ?_
  have hp' : (p.2, p.1).1.re < (p.2, p.1).2.re := hp
  have hd : DifferentiableAt ℂ (fun p : ℂ × ℂ => (p.2, p.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  have hr0 := differentiableAt_rowEval_exp (fun t ht =>
    VOA.Huang.LogHuangODEProduct.summable_log_product hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z (a+lowerSpectrumRep hC2 N₅ hfg₅ mu-β-1)
        (b+c-lowerSpectrumRep hC2 N₅ hfg₅ mu-1) k l ht) hp'
  have hr := DifferentiableAt.comp (x := p) hr0 hd
  refine DifferentiableAt.mul ?_ hr
  fun_prop

end VOA.Huang.LogBraided
