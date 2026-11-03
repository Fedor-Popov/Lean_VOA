import VOA.Classification.COne.McRaeM2LogBraidedTaylor

/-! # The iterate side of the hexagon: braiding the inner pair translates the outer point

Let `M` be an outer and `𝒴'` an inner logarithmic intertwining operator. The
completed iterate whose inner operator is `Ω_r(𝒴')` is the completed iterate of `𝒴'`
with inner branch rotated by `κ_r` and outer point translated (
`completedLogIterate_omega_inner`):

`⟨g, M(Ω_r(𝒴')(x, e^{ℓ₀})y, e^{ℓ₂})z⟩ = ⟨g, M(𝒴'(y, e^{ℓ₀+κ_r})x, e^{ℓ₂}(1+e^{ℓ₀-ℓ₂}))z⟩`

with outer branch `ℓ₂ + log(1 + e^{ℓ₀-ℓ₂})`, whenever `|e^{ℓ₀-ℓ₂}| < 1/2`.
Skew-symmetry produces `e^{zL(−1)}` on the inner vector (`pointEvaluationBlock_omega`);
the `L(−1)`-derivative property turns it into the Taylor series of the outer
evaluation (`hasSum_outerEval_taylor`); Cauchy's estimate on the circle of radius
`1/2` (`norm_outerEval_vraw_le`) makes the double series over intermediate weights
and Taylor orders absolutely summable, so it may be reordered. -/
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

/-! ## Elementary bounds on the circle of radius `1/2` -/

theorem half_le_norm_one_add {w : ℂ} (hw : ‖w‖ = 1/2) : 1/2 ≤ ‖1+w‖ := by
  have h := norm_sub_le (1+w) w
  rw [add_sub_cancel_right, norm_one, hw] at h
  linarith

theorem norm_one_add_le {w : ℂ} (hw : ‖w‖ = 1/2) : ‖1+w‖ ≤ 3/2 := by
  have h := norm_add_le (1 : ℂ) w
  rw [norm_one, hw] at h
  linarith

theorem abs_log_norm_one_add_le {w : ℂ} (hw : ‖w‖ = 1/2) : |Real.log ‖1+w‖| ≤ 1 := by
  have h1 := half_le_norm_one_add hw
  have h2 := norm_one_add_le hw
  have hpos : 0 < ‖1+w‖ := by linarith
  rw [abs_le]
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have hinv : ‖1+w‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    linarith
  · have h := Real.log_le_sub_one_of_pos hpos
    linarith

theorem norm_log_one_add_le {w : ℂ} (hw : ‖w‖ = 1/2) : ‖Complex.log (1+w)‖ ≤ 1+Real.pi := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  have h1 := abs_log_norm_one_add_le hw
  have h2 := Complex.abs_arg_le_pi (1+w)
  linarith

theorem neg_log_norm_one_add_le {w : ℂ} (hw : ‖w‖ = 1/2) : -Real.log ‖1+w‖ ≤ Real.log 2 := by
  have h1 := half_le_norm_one_add hw
  have h := Real.log_le_log (by norm_num) h1
  rw [one_div, Real.log_inv] at h
  linarith

/-! ## The inner vector and the bound -/

/-- The literal inner evaluation vector of weight `δ`, with log cutoff `L`. -/
def vraw (Y' : LogModes M₂ M₁ M₅) (L : ℕ) (y : M₂) (x : M₁) (b a ℓ δ : ℂ) : M₅ :=
  Complex.exp (ℓ*(δ-b-a)) • ∑ l∈Finset.range L, ℓ^l • Y' (b+a-δ-1) l y x

theorem outerEval_vraw (M : LogModes M₅ M₃ M₄) (Y' : LogModes M₂ M₁ M₅) (K L : ℕ)
    (g : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β ℓ' lam δ : ℂ) :
    outerEval M K g z c β lam δ (vraw Y' L y x b a ℓ' δ) =
      ∑ k∈Finset.range K, ∑ l∈Finset.range L,
        Complex.exp (lam*(β-δ-c)) * Complex.exp (ℓ'*(δ-b-a)) * lam^k * ℓ'^l *
          g (M (δ+c-β-1) k (Y' (b+a-δ-1) l y x) z) := by
  unfold outerEval vraw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, map_sum, LinearMap.sum_apply,
    map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  ring

/-- The row bound for the translated outer evaluation on the circle `|w| = 1/2`. -/
def rowBound (M : LogModes M₅ M₃ M₄) (Y' : LogModes M₂ M₁ M₅) (K L : ℕ) (g : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (a b c β ℓ₀ ℓ₂ κ ρ : ℂ) (n : ℕ) : ℝ :=
  ∑ k∈Finset.range K, ∑ l∈Finset.range L,
    Real.exp ((‖ℓ₂‖+1+Real.pi) * ‖β-ρ-c‖) * ‖Complex.exp ((ℓ₀+κ)*(ρ-b-a))‖ *
      (‖ℓ₂‖+1+Real.pi)^k * ‖ℓ₀+κ‖^l *
      (‖iterRow M Y' g y x z (ρ+c-β-1) (b+a-ρ-1) k l n‖ * (2*‖Complex.exp (ℓ₀-ℓ₂)‖)^n)

theorem rowBound_nonneg (M : LogModes M₅ M₃ M₄) (Y' : LogModes M₂ M₁ M₅) (K L : ℕ)
    (g : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β ℓ₀ ℓ₂ κ ρ : ℂ) (n : ℕ) :
    0 ≤ rowBound M Y' K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n := by
  unfold rowBound
  refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => ?_
  have : 0 ≤ ‖ℓ₂‖+1+Real.pi := by positivity
  positivity

/-- **The circle bound.** -/
theorem norm_outerEval_vraw_le (M : LogModes M₅ M₃ M₄) (Y' : LogModes M₂ M₁ M₅) (K L : ℕ)
    (g : M₄ →ₗ[ℂ] ℂ) (x : M₁) (y : M₂) (z : M₃) (a b c β ℓ₀ ℓ₂ κ : ℂ) (hκ : κ.re = 0)
    (ρ : ℂ) (n : ℕ) {w : ℂ} (hw : ‖w‖ = 1/2) :
    ‖outerEval M K g z c β (ℓ₂+Complex.log (1+w)) (ρ+n) (vraw Y' L y x b a (ℓ₀+κ) (ρ+n))‖ ≤
      rowBound M Y' K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n := by
  set lam := ℓ₂+Complex.log (1+w) with hlam
  set Λ : ℝ := ‖ℓ₂‖+1+Real.pi with hΛ
  have hlamΛ : ‖lam‖ ≤ Λ := by
    have := norm_log_one_add_le hw
    have := norm_add_le ℓ₂ (Complex.log (1+w))
    rw [hΛ]; linarith
  have hΛ0 : 0 ≤ Λ := by positivity
  rw [outerEval_vraw]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_))
  have hexp : Complex.exp (lam*(β-(ρ+n)-c)) * Complex.exp ((ℓ₀+κ)*((ρ+n)-b-a)) =
      Complex.exp (lam*(β-ρ-c)) * Complex.exp ((ℓ₀+κ)*(ρ-b-a)) *
        Complex.exp (n*((ℓ₀+κ)-lam)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have hcoef : g (M ((ρ+n)+c-β-1) k (Y' (b+a-(ρ+n)-1) l y x) z) =
      iterRow M Y' g y x z (ρ+c-β-1) (b+a-ρ-1) k l n := by
    unfold iterRow
    rw [show (ρ+n)+c-β-1 = ρ+c-β-1+n by ring, show b+a-(ρ+n)-1 = b+a-ρ-1-n by ring]
  have he1 : ‖Complex.exp (lam*(β-ρ-c))‖ ≤ Real.exp (Λ * ‖β-ρ-c‖) := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hlamΛ (norm_nonneg _)
  have he3 : ‖Complex.exp (n*((ℓ₀+κ)-lam))‖ ≤ (2*‖Complex.exp (ℓ₀-ℓ₂)‖)^n := by
    rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_log (show (0:ℝ) < 2 by norm_num),
      ← Real.exp_add, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hre : (n*((ℓ₀+κ)-lam)).re = n * (ℓ₀.re + κ.re - ℓ₂.re - Real.log ‖1+w‖) := by
      simp only [hlam, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.sub_re,
        Complex.add_re, Complex.log_re, zero_mul, sub_zero]
      ring
    rw [hre, hκ, Complex.sub_re]
    have := neg_log_norm_one_add_le hw
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hpow : ‖lam‖^k ≤ Λ^k := pow_le_pow_left₀ (norm_nonneg _) hlamΛ k
  rw [hexp, hcoef]
  simp only [norm_mul, norm_pow]
  have h0 := norm_nonneg (Complex.exp ((ℓ₀+κ)*(ρ-b-a)))
  have h0' := norm_nonneg (iterRow M Y' g y x z (ρ+c-β-1) (b+a-ρ-1) k l n)
  have h0'' := norm_nonneg (ℓ₀+κ)
  have h3 := norm_nonneg (Complex.exp (n*((ℓ₀+κ)-lam)))
  have h4 := norm_nonneg (Complex.exp (lam*(β-ρ-c)))
  calc ‖Complex.exp (lam*(β-ρ-c))‖ * ‖Complex.exp ((ℓ₀+κ)*(ρ-b-a))‖ *
        ‖Complex.exp (n*((ℓ₀+κ)-lam))‖ * ‖lam‖^k * ‖ℓ₀+κ‖^l *
        ‖iterRow M Y' g y x z (ρ+c-β-1) (b+a-ρ-1) k l n‖
      ≤ Real.exp (Λ * ‖β-ρ-c‖) * ‖Complex.exp ((ℓ₀+κ)*(ρ-b-a))‖ *
        (2*‖Complex.exp (ℓ₀-ℓ₂)‖)^n * Λ^k * ‖ℓ₀+κ‖^l *
        ‖iterRow M Y' g y x z (ρ+c-β-1) (b+a-ρ-1) k l n‖ := by gcongr
    _ = _ := by ring

/-! ## The translation theorem -/

variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)

/-- The shear `(δ, j) ↦ (δ + j, j)` of weights and Taylor orders. -/
def shearC : ℂ × ℕ ≃ ℂ × ℕ where
  toFun p := (p.1+p.2, p.2)
  invFun q := (q.1-q.2, q.2)
  left_inv p := by simp
  right_inv q := by simp

include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ in
/-- **Braiding the inner pair of an iterate translates its outer point.** -/
theorem completedLogIterate_omega_inner
    (M : LogIntertwiningOperator N₅.toWeakModule N₃.toWeakModule N₄.toWeakModule)
    (Y' : LogIntertwiningOperator N₂.toWeakModule N₁.toWeakModule N₅.toWeakModule)
    (r : ℤ) {a b c : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (g : M₄ →ₗ[ℂ] ℂ) (β : ℂ) {ℓ₀ ℓ₂ : ℂ} (hu : ‖Complex.exp (ℓ₀-ℓ₂)‖ < 1/2) :
    completedLogIterate N₁ N₂ N₃ N₄ N₅ M
        (omegaEquiv N₂.toWeakModule N₁.toWeakModule N₅.toWeakModule r Y') ℓ₀ ℓ₂ c β g x y
        ⟨z,hz⟩ =
      completedLogIterate N₂ N₁ N₃ N₄ N₅ M Y' (ℓ₀+kap r)
        (ℓ₂+Complex.log (1+Complex.exp (ℓ₀-ℓ₂))) c β g y x ⟨z,hz⟩ := by
  classical
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N₅ N₃ N₄ hfg₅ hfg₃ hfg₄
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen N₂ N₁ N₅ hfg₂ hfg₁ hfg₅
  have hKM : ∀ n k, K ≤ k → M.1 n k = 0 := fun n k hk => hK M n k hk
  have hLY : ∀ n l, L ≤ l → Y'.1 n l = 0 := fun n l hl => hL Y' n l hl
  set u := Complex.exp (ℓ₀-ℓ₂) with hudef
  set κ := kap r with hκdef
  have hκ : κ.re = 0 := by rw [hκdef, kap]; simp
  set Lm := Lm1 N₅.toWeakModule with hLm
  set v : ℂ → M₅ := vraw Y'.1 L y x b a (ℓ₀+κ) with hvdef
  have hv : ∀ δ, (evaluatePoint N₂ N₁ N₅ Y' (ℓ₀+κ) y x δ : M₅) = v δ := by
    intro δ
    rw [evaluatePoint, fromBlocks_homogeneous N₂ N₁ _ hy hx]
    exact pointEvaluationBlock_fixed_cutoff N₂ N₁ N₅ Y' (ℓ₀+κ) b a δ ⟨y,hy⟩ ⟨x,hx⟩ L
      (fun l hl => by rw [hLY _ l hl]; rfl)
  have hvbot : ∀ δ, N₅.weight δ = ⊥ → v δ = 0 := by
    intro δ hδ
    rw [← hv δ]
    have hbot : N₅.weight δ ≤ (⊥ : Submodule ℂ M₅) := by rw [hδ]
    exact (Submodule.mem_bot ℂ).mp (hbot (evaluatePoint N₂ N₁ N₅ Y' (ℓ₀+κ) y x δ).2)
  let G : ℂ × ℕ → ℂ := fun p =>
    transCoeff ℓ₀ p.2 * outerEval M.1 K g z c β ℓ₂ (p.1+p.2) ((Lm^p.2) (v p.1))
  let F : ℂ × ℕ → ℂ := fun p =>
    transCoeff ℓ₀ p.2 * outerEval M.1 K g z c β ℓ₂ p.1 ((Lm^p.2) (v (p.1-p.2)))
  have hFG : ∀ p, F (shearC p) = G p := by
    intro p
    simp only [F, G, shearC, Equiv.coe_fn_mk, add_sub_cancel_right]
  have hu1 : ‖u‖ < 1 := by linarith
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  -- the Taylor identity
  have hB : ∀ δ, HasSum (fun j => G (δ,j))
      (outerEval M.1 K g z c β (ℓ₂+Complex.log (1+u)) δ (v δ)) := by
    intro δ
    refine (hasSum_outerEval_taylor M.2 hKM g z c β ℓ₂ δ (v δ) hu1).congr_fun fun j => ?_
    simp only [G, transCoeff]
    have he : u^j * Complex.exp (j*ℓ₂) = Complex.exp (ℓ₀*j) := by
      rw [hudef, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; ring
    rw [← he]
    ring
  -- the bound
  have hGb : ∀ (ρ : ℂ) (n j : ℕ), ‖G (ρ+n, j)‖ ≤
      rowBound M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n * (2*‖u‖)^j := by
    intro ρ n j
    have hC := norm_outerEval_taylor_le M.2 hKM g z c β ℓ₂ (ρ+n) (v (ρ+n))
      (R := 1/2) (C := rowBound M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n)
      (by norm_num) (by norm_num)
      (fun w hw => norm_outerEval_vraw_le M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ hκ ρ n
        (by rwa [mem_sphere_zero_iff_norm] at hw)) j
    have hG : G (ρ+n, j) = (((j.factorial : ℂ))⁻¹ * u^j) *
        (Complex.exp (j*ℓ₂) * outerEval M.1 K g z c β ℓ₂ (ρ+n+j) ((Lm^j) (v (ρ+n)))) := by
      simp only [G, transCoeff]
      have he : u^j * Complex.exp (j*ℓ₂) = Complex.exp (ℓ₀*j) := by
        rw [hudef, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; ring
      rw [← he]
      ring
    rw [hG, norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have hf : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    calc (j.factorial : ℝ)⁻¹ * ‖u‖^j *
          ‖Complex.exp (j*ℓ₂) * outerEval M.1 K g z c β ℓ₂ (ρ+n+j) ((Lm^j) (v (ρ+n)))‖
        ≤ (j.factorial : ℝ)⁻¹ * ‖u‖^j *
          (j.factorial * rowBound M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n / (1/2)^j) := by
          gcongr
      _ = rowBound M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n * (2*‖u‖)^j := by
          rw [div_eq_mul_inv, one_div, inv_pow, inv_inv, mul_pow]
          field_simp
  have hrowB : ∀ ρ : ℂ, Summable (fun n : ℕ =>
      rowBound M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n) := by
    intro ρ
    unfold rowBound
    refine summable_sum fun k _ => summable_sum fun l _ => Summable.mul_left _ ?_
    have ht : ‖((2*‖u‖ : ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; linarith
    refine (VOA.Huang.LogHuangODEIterate.summable_log_iterate hC2 N₂ N₁ N₃ N₄ N₅
      hfg₂ hfg₁ hfg₃ hfg₄ hfg₅ M Y' g y x z (ρ+c-β-1) (b+a-ρ-1) k l ht).congr fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*‖u‖)]
    rfl
  have h2u : 2*‖u‖ < 1 := by linarith
  have hgeo : Summable (fun j : ℕ => (2*‖u‖)^j) := summable_geometric_of_lt_one (by positivity) h2u
  have hcol : ∀ (ρ : ℂ) (n : ℕ), ∑' j, ‖G (ρ+n, j)‖ ≤
      rowBound M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n * (1-2*‖u‖)⁻¹ := by
    intro ρ n
    have hs := hgeo.mul_left (rowBound M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ ρ n)
    have hle := Summable.tsum_le_tsum (fun j => hGb ρ n j)
      (hs.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hGb ρ n j)) hs
    rwa [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) h2u] at hle
  have hGs : Summable G := by
    refine Summable.of_norm ((summable_prod_of_nonneg (fun p => norm_nonneg (G p))).mpr ⟨?_, ?_⟩)
    · intro δ
      have hδ : δ = δ + ((0:ℕ) : ℂ) := by simp
      refine (hgeo.mul_left (rowBound M.1 Y'.1 K L g x y z a b c β ℓ₀ ℓ₂ κ δ 0)).of_nonneg_of_le
        (fun j => norm_nonneg _) (fun j => ?_)
      have := hGb δ 0 j
      rwa [← hδ] at this
    · obtain ⟨hs, -⟩ := tsum_lowerSpectrum hC2 N₅ hfg₅
        (fun δ => (((∑' j, ‖G (δ,j)‖ : ℝ)) : ℂ))
        (fun δ hne hbot => hne (by
          have h0 : ∀ j, G (δ,j) = 0 := by
            intro j
            simp only [G, hvbot δ hbot, map_zero, outerEval_zero, mul_zero]
          simp only [h0, norm_zero, tsum_zero, Complex.ofReal_zero]))
        (fun mu _ => by
          refine Summable.of_norm_bounded ((hrowB (lowerSpectrumRep hC2 N₅ hfg₅ mu)).mul_right
            (1-2*‖u‖)⁻¹) (fun n => ?_)
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (tsum_nonneg fun j => norm_nonneg _)]
          exact hcol _ n)
      exact Complex.summable_ofReal.mp hs
  have hFs : Summable F := by
    have h : Summable (F ∘ shearC) := hGs.congr fun p => (hFG p).symm
    exact shearC.summable_iff.mp h
  -- Step A: the left side
  obtain ⟨Bd,hBd⟩ := N₅.boundedBelow
  have hJ : ∀ (γ : ℂ) (j : ℕ), ⌈γ.re-Bd⌉₊+1 ≤ j → N₅.weight (γ-j) = ⊥ := by
    intro γ j hj
    by_contra hne
    have h1 := hBd _ hne
    have h2 := Nat.le_ceil (γ.re-Bd)
    have h3 : ((⌈γ.re-Bd⌉₊ : ℕ) : ℝ) + 1 ≤ j := by exact_mod_cast hj
    rw [Complex.sub_re, Complex.natCast_re] at h1
    linarith
  have hA : completedLogIterate N₁ N₂ N₃ N₄ N₅ M
      (omegaEquiv N₂.toWeakModule N₁.toWeakModule N₅.toWeakModule r Y') ℓ₀ ℓ₂ c β g x y
      ⟨z,hz⟩ = ∑' γ, ∑' j, F (γ,j) := by
    unfold completedLogIterate completedIteratePair
    refine tsum_congr fun γ => ?_
    rw [pointEvaluationBlock_eq_outerEval M hKM g ⟨z,hz⟩ β ℓ₂ γ,
      evaluatePoint_eq_block N₁ N₂ N₅ _ ℓ₀ hx hy γ,
      pointEvaluationBlock_omega N₂ N₁ N₅ Y' r ℓ₀ ⟨x,hx⟩ ⟨y,hy⟩ _ (hJ γ), outerEval_sum]
    rw [tsum_eq_sum (s := Finset.range (⌈γ.re-Bd⌉₊+1)) (fun j hj => by
      rw [Finset.mem_range, not_lt] at hj
      simp only [F, hvbot _ (hJ γ j hj), map_zero, outerEval_zero, mul_zero])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [outerEval_smul, ← evaluatePoint_eq_block N₂ N₁ N₅ Y' (ℓ₀+kap r) hy hx (γ-j), hv]
  -- Step B: the right side
  have hR : completedLogIterate N₂ N₁ N₃ N₄ N₅ M Y' (ℓ₀+kap r)
      (ℓ₂+Complex.log (1+Complex.exp (ℓ₀-ℓ₂))) c β g y x ⟨z,hz⟩ =
      ∑' δ, outerEval M.1 K g z c β (ℓ₂+Complex.log (1+u)) δ (v δ) := by
    unfold completedLogIterate completedIteratePair
    refine tsum_congr fun δ => ?_
    rw [pointEvaluationBlock_eq_outerEval M hKM g ⟨z,hz⟩ β _ δ, hv]
  rw [hA, hR]
  calc ∑' γ, ∑' j, F (γ,j) = ∑' q, F q := (hFs.tsum_prod' fun γ => hFs.prod_factor γ).symm
    _ = ∑' p, F (shearC p) := (shearC.tsum_eq F).symm
    _ = ∑' p, G p := tsum_congr hFG
    _ = ∑' δ, ∑' j, G (δ,j) := hGs.tsum_prod' fun δ => hGs.prod_factor δ
    _ = _ := tsum_congr fun δ => (hB δ).tsum_eq

end VOA.Huang.LogBraided
