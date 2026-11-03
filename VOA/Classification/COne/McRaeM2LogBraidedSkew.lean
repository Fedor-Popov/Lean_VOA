import VOA.Classification.COne.McRaeM2LogBraidedRows
import VOA.Modules.LogTensorPzPointScaling

/-! # Point evaluation of HLZ's skew-symmetry operator

For a logarithmic intertwining operator `𝒴` and `r ∈ ℤ` put `κ_r = (2r+1)πi`.
On every weight block the chosen-branch evaluation of `Ω_r(𝒴)` is the finite
translated evaluation of `𝒴` at the rotated branch (`pointEvaluationBlock_omega`):

`Ω_r(𝒴)(y, e^ℓ)x |_γ = Σ_j (e^{jℓ}/j!) L(−1)^j (𝒴(x, e^{ℓ+κ_r})y |_{γ-j})`,

i.e. `e^{zL(−1)}𝒴(x, e^{κ_r}z)y` with the logarithm `ℓ + κ_r`. The phases cancel
exactly because `e^{-κ_r} = -1`. Consequently the completed product whose outer
operator is `Ω_r(K)` is the finite `L(−1)`-sum of completed iterates of `K` at
the rotated outer branch (`completedLogProduct_omega`). -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogBraided
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion VOA.LogSkew
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The rotation `κ_r = (2r+1)πi` of the branch made by `Ω_r`. -/
def kap (r : ℤ) : ℂ := (2*r+1 : ℂ) * (Real.pi * Complex.I)

theorem exp_neg_kap (r : ℤ) : Complex.exp (-kap r) = -1 := by
  rw [kap, show -((2*(r : ℂ)+1) * (↑Real.pi * Complex.I)) =
      ((-r-1 : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) + ↑Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
  ring

theorem exp_kap (r : ℤ) : Complex.exp (kap r) = -1 := by
  have h := exp_neg_kap r
  rw [Complex.exp_neg, inv_eq_iff_eq_inv] at h
  rw [h]; norm_num

/-- The coefficient `e^{jℓ}/j!` of the translation. -/
def transCoeff (ell : ℂ) (j : ℕ) : ℂ := Complex.exp (ell*j) * ((j.factorial : ℂ))⁻¹

/-- A log-shifted mode which lands in a vanishing weight space is zero. -/
theorem logShift_mode_eq_zero (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell : ℂ) {a b γ : ℂ} (x : N₁.weight a) (y : N₂.weight b) (hγ : N₃.weight γ = ⊥) :
    logShift ell Y.1 (a+b-γ-1) 0 x y = 0 := by
  have h := evaluatePoint_logShift N₁ N₂ N₃ Y ell x.2 y.2 γ
  have hz : (evaluatePoint N₁ N₂ N₃ Y ell x y γ : M₃) = 0 := by
    have hbot : N₃.weight γ ≤ (⊥ : Submodule ℂ M₃) := by rw [hγ]
    exact (Submodule.mem_bot ℂ).mp (hbot (evaluatePoint N₁ N₂ N₃ Y ell x y γ).2)
  rw [hz] at h
  have h' := congrArg (fun v : M₃ => (Complex.exp (ell*(γ-a-b)))⁻¹ • v) h
  simp only [smul_zero, smul_smul, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_smul] at h'
  exact h'.symm

/-- **Block evaluation of `Ω_r`.** -/
theorem pointEvaluationBlock_omega (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃)
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (r : ℤ) (ell : ℂ) {a b γ : ℂ} (y : N₂.weight b) (x : N₁.weight a) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → N₃.weight (γ-j) = ⊥) :
    (pointEvaluationBlock N₂ N₁ N₃
        (omegaEquiv N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule r Y) ell b a γ y x : M₃) =
      ∑ j∈Finset.range J, transCoeff ell j • (Lm1 N₃.toWeakModule ^ j)
        (pointEvaluationBlock N₁ N₂ N₃ Y (ell+kap r) a b (γ-j) x y : M₃) := by
  have hc := omegaPhase_succ r
  have hc0 := omegaPhase_ne_zero r
  have hS := Y.2.isLogIntertwining_skewK hc hc0
  have hL := Y.2.isLogIntertwining_logShift (ell+kap r)
  rw [← evaluatePoint_eq_block N₂ N₁ N₃ _ ell y.2 x.2 γ,
    evaluatePoint_logShift N₂ N₁ N₃ _ ell y.2 x.2 γ]
  have hΩ : (omegaEquiv N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule r Y).1 =
      omega N₃.toWeakModule r Y.1 := rfl
  rw [hΩ, omega, logShift_logShift hS.logFin, show ell + (2*(r : ℂ)+1)*(↑Real.pi*Complex.I) =
    ell+kap r by rw [kap], ← Y.2.skewK_logShift hc hc0]
  set n := b+a-γ-1 with hn
  have hJ' : ∀ j : ℕ, J ≤ j → logShift (ell+kap r) Y.1 (n+j) 0 x y = 0 := by
    intro j hj
    have h := logShift_mode_eq_zero N₁ N₂ N₃ Y (ell+kap r) x y (hJ j hj)
    rw [show a+b-(γ-j)-1 = n+j by rw [hn]; ring] at h
    exact h
  rw [hL.skewK_eq_sum (omegaPhase r) n 0 y x J hJ', smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← evaluatePoint_eq_block N₁ N₂ N₃ Y (ell+kap r) x.2 y.2 (γ-j),
    evaluatePoint_logShift N₁ N₂ N₃ Y (ell+kap r) x.2 y.2 (γ-j),
    show a+b-(γ-j)-1 = n+j by rw [hn]; ring, map_smul, smul_smul, smul_smul]
  congr 1
  have hp : omegaPhase r n = Complex.exp (-kap r * (n+1)) := by
    rw [omegaPhase, kap]
  have hneg : Complex.exp (-kap r * j) = (-1 : ℂ)^j := by
    rw [← exp_neg_kap r, ← Complex.exp_nat_mul]; congr 1; ring
  rw [hp, transCoeff, sc]
  have e1 : Complex.exp (ell*(γ-b-a)) * Complex.exp (-kap r * (n+1)) * Complex.exp (-kap r * j) =
      Complex.exp (ell*j) * Complex.exp ((ell+kap r)*(γ-j-a-b)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hn]
    congr 1
    ring
  rw [← hneg]
  linear_combination ((j.factorial : ℂ))⁻¹ * e1

/-- **Product side of the hexagon**: a completed product whose outer operator
is `Ω_r(K)` is the finite `L(−1)`-sum of completed iterates of `K` with outer
branch `m₁ + κ_r`. -/
theorem completedLogProduct_omega (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
    (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
    (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
    (hfg₅ : FinGen N₅.toWeakModule)
    (K : LogIntertwiningOperator N₅.toWeakModule N₁.toWeakModule N₄.toWeakModule)
    (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
    (r : ℤ) {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {m₁ m₂ : ℂ} (hlt : m₂.re < m₁.re) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → N₄.weight (β-j) = ⊥) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅
        (omegaEquiv N₅.toWeakModule N₁.toWeakModule N₄.toWeakModule r K) Y₂ m₁ m₂ a β f
        ⟨x,hx⟩ y z =
      ∑ j∈Finset.range J, transCoeff m₁ j *
        completedLogIterate N₂ N₃ N₁ N₄ N₅ K Y₂ m₂ (m₁+kap r) a (β-j)
          (f ∘ₗ (Lm1 N₄.toWeakModule ^ j)) y z ⟨x,hx⟩ := by
  obtain ⟨K₁,hK₁⟩ := uniform_log_degree_of_finGen N₅ N₁ N₄ hfg₅ hfg₁ hfg₄
  obtain ⟨K₂,hK₂⟩ := uniform_log_degree_of_finGen N₂ N₃ N₅ hfg₂ hfg₃ hfg₅
  have hlt' : m₂.re < (m₁+kap r).re := by
    rw [Complex.add_re, kap]; simp; exact hlt
  have hsum (j : ℕ) := (completedLogIterate_eq_iterValue hC2 N₂ N₃ N₁ N₄ N₅
    hfg₂ hfg₃ hfg₁ hfg₄ hfg₅ K Y₂ (fun n k hk => hK₁ K n k hk) (fun n l hl => hK₂ Y₂ n l hl)
    hy hz hx (f ∘ₗ (Lm1 N₄.toWeakModule ^ j)) (β-j) hlt').1
  unfold completedLogProduct completedProductPair
  have hterm : ∀ γ : ℂ, f (pointEvaluationBlock N₁ N₅ N₄
      (omegaEquiv N₅.toWeakModule N₁.toWeakModule N₄.toWeakModule r K) m₁ a γ β ⟨x,hx⟩
        (evaluatePoint N₂ N₃ N₅ Y₂ m₂ y z γ)) =
      ∑ j∈Finset.range J, transCoeff m₁ j *
        (f ∘ₗ (Lm1 N₄.toWeakModule ^ j)) (pointEvaluationBlock N₅ N₁ N₄ K (m₁+kap r) γ a (β-j)
          (evaluatePoint N₂ N₃ N₅ Y₂ m₂ y z γ) ⟨x,hx⟩) := by
    intro γ
    rw [pointEvaluationBlock_omega N₅ N₁ N₄ K r m₁ ⟨x,hx⟩ _ J hJ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  rw [tsum_congr hterm, Summable.tsum_finsetSum (fun j _ => (hsum j).mul_left _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left]
  rfl

end VOA.Huang.LogBraided
