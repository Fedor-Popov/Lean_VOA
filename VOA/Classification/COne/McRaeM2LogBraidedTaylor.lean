import VOA.Classification.COne.McRaeM2LogBraidedSkew
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville

/-! # Taylor expansion of one outer logarithmic evaluation

For a logarithmic intertwining operator `M` with a uniform logarithmic cutoff, the
scalar outer evaluation `ℓ ↦ ⟨g, M(w, e^ℓ)z⟩_β` of a fixed vector `w` of weight
`γ` (`outerEval`) is an entire function of the branch `ℓ`, and the
`L(−1)`-derivative property of `M` is exactly
`d/dℓ ⟨g, M(w, e^ℓ)z⟩ = e^ℓ ⟨g, M(L(−1)w, e^ℓ)z⟩` (`hasDerivAt_outerEval`), including
every logarithmic coefficient. Hence the translated evaluation
`u ↦ ⟨g, M(w, e^{ℓ}(1+u))z⟩` with branch `ℓ + log(1+u)` is holomorphic on the unit
disc, its Taylor coefficients at `0` are `e^{jℓ}⟨g, M(L(−1)^j w, e^ℓ)z⟩/j!`
(`hasSum_outerEval_taylor`), and Cauchy's estimate bounds them
(`norm_outerEval_taylor_le`). -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogBraided
open VOA VOA.LogTensor VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₃ M₄ M₅ : Type u}
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The scalar outer evaluation `⟨g, M(w, e^ℓ)z⟩` on the output weight `β`, for a
vector `w` of weight `γ` and `z` of weight `c`, with a uniform log cutoff `K`. -/
def outerEval (M : LogModes M₅ M₃ M₄) (K : ℕ) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β ℓ γ : ℂ)
    (w : M₅) : ℂ :=
  Complex.exp (ℓ*(β-γ-c)) * ∑ k∈Finset.range K, ℓ^k * g (M (γ+c-β-1) k w z)

/-- Outer evaluation is linear in the vector. -/
theorem outerEval_add (M : LogModes M₅ M₃ M₄) (K : ℕ) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃)
    (c β ℓ γ : ℂ) (w w' : M₅) :
    outerEval M K g z c β ℓ γ (w+w') = outerEval M K g z c β ℓ γ w + outerEval M K g z c β ℓ γ w' := by
  simp only [outerEval, map_add, LinearMap.add_apply, mul_add, Finset.sum_add_distrib]

theorem outerEval_smul (M : LogModes M₅ M₃ M₄) (K : ℕ) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃)
    (c β ℓ γ : ℂ) (s : ℂ) (w : M₅) :
    outerEval M K g z c β ℓ γ (s • w) = s * outerEval M K g z c β ℓ γ w := by
  simp only [outerEval, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem outerEval_zero (M : LogModes M₅ M₃ M₄) (K : ℕ) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃)
    (c β ℓ γ : ℂ) : outerEval M K g z c β ℓ γ 0 = 0 := by
  simp [outerEval]

theorem outerEval_sum {ι : Type*} (s : Finset ι) (M : LogModes M₅ M₃ M₄) (K : ℕ)
    (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β ℓ γ : ℂ) (w : ι → M₅) :
    outerEval M K g z c β ℓ γ (∑ i∈s, w i) = ∑ i∈s, outerEval M K g z c β ℓ γ (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [outerEval_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, outerEval_add, ih]

/-- The outer block evaluation of a genuine intertwiner is `outerEval`. -/
theorem pointEvaluationBlock_eq_outerEval {A₅ : LogVModule W M₅} {A₃ : LogVModule W M₃}
    {A₄ : LogVModule W M₄}
    (M : LogIntertwiningOperator A₅.toWeakModule A₃.toWeakModule A₄.toWeakModule)
    {K : ℕ} (hK : ∀ n k, K ≤ k → M.1 n k = 0) (g : M₄ →ₗ[ℂ] ℂ) {c : ℂ} (z : A₃.weight c)
    (β ℓ γ : ℂ) (w : A₅.weight γ) :
    g (pointEvaluationBlock A₅ A₃ A₄ M ℓ γ c β w z) = outerEval M.1 K g z c β ℓ γ w := by
  rw [pointEvaluationBlock_fixed_cutoff A₅ A₃ A₄ M ℓ γ c β w z K
    (fun k hk => by rw [hK _ k hk]; rfl), map_smul, map_sum, smul_eq_mul, outerEval]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]

/-- Removing the boundary term of a derivative of a log polynomial. -/
theorem sum_range_deriv_shift (K : ℕ) (ℓ : ℂ) (a : ℕ → ℂ) (ha : a K = 0) :
    ∑ k∈Finset.range K, ((k : ℂ) * ℓ^(k-1)) * a k =
      ∑ k∈Finset.range K, ((k : ℂ)+1) * ℓ^k * a (k+1) := by
  cases K with
  | zero => simp
  | succ K =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ (fun k => ((k : ℂ)+1) * ℓ^k * a (k+1)), ha]
    try simp

variable {A₃ : WeakModule W M₃} {A₄ : WeakModule W M₄} {A₅ : WeakModule W M₅}

/-- **The `L(−1)`-derivative property at a chosen branch.** -/
theorem hasDerivAt_outerEval {M : LogModes M₅ M₃ M₄} (hM : IsLogIntertwining A₅ A₃ A₄ M)
    {K : ℕ} (hK : ∀ n k, K ≤ k → M n k = 0) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ)
    (w : M₅) (ℓ : ℂ) :
    HasDerivAt (fun ℓ => outerEval M K g z c β ℓ γ w)
      (Complex.exp ℓ * outerEval M K g z c β ℓ (γ+1) (Lm1 A₅ w)) ℓ := by
  set a : ℕ → ℂ := fun k => g (M (γ+c-β-1) k w z) with ha
  have h1 : HasDerivAt (fun ℓ : ℂ => Complex.exp (ℓ*(β-γ-c)))
      (Complex.exp (ℓ*(β-γ-c)) * (1*(β-γ-c))) ℓ :=
    ((hasDerivAt_id ℓ).mul_const (β-γ-c)).cexp
  have h2 : HasDerivAt (fun ℓ : ℂ => ∑ k∈Finset.range K, ℓ^k * a k)
      (∑ k∈Finset.range K, ((k : ℂ) * ℓ^(k-1)) * a k) ℓ :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_pow k ℓ).mul_const (a k)
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  have hmode : ∀ k : ℕ, g (M (γ+1+c-β-1) k (Lm1 A₅ w) z) =
      (-(γ+c-β-1+1)) * a k + ((k : ℂ)+1) * a (k+1) := by
    intro k
    have hL := hM.L_neg_one w (γ+1+c-β-1) k
    rw [show γ+1+c-β-1-1 = γ+c-β-1 by ring, show γ+1+c-β-1 = γ+c-β-1+1 by ring] at hL
    rw [show γ+1+c-β-1 = γ+c-β-1+1 by ring, hL]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul, ha]
  have hsum : ∑ k∈Finset.range K, ℓ^k * g (M (γ+1+c-β-1) k (Lm1 A₅ w) z) =
      (-(γ+c-β-1+1)) * ∑ k∈Finset.range K, ℓ^k * a k +
        ∑ k∈Finset.range K, ((k : ℂ)+1) * ℓ^k * a (k+1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hmode]; ring
  have haK : a K = 0 := by simp only [ha, hK _ K le_rfl, LinearMap.zero_apply, map_zero]
  rw [outerEval, hsum, ← sum_range_deriv_shift K ℓ a haK]
  have he : Complex.exp ℓ * Complex.exp (ℓ*(β-(γ+1)-c)) = Complex.exp (ℓ*(β-γ-c)) := by
    rw [← Complex.exp_add]; congr 1; ring
  linear_combination (-((β-γ-c) * ∑ k∈Finset.range K, ℓ^k * a k +
      ∑ k∈Finset.range K, ((k : ℂ) * ℓ^(k-1)) * a k)) * he

/-- The `j`-th derivative family `ψ_j(ℓ) = ⟨g, M(L(−1)^j w, e^ℓ)z⟩`. -/
def psiJ (M : LogModes M₅ M₃ M₄) (K : ℕ) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β δ : ℂ) (w : M₅)
    (L : Module.End ℂ M₅) (j : ℕ) (ℓ : ℂ) : ℂ :=
  outerEval M K g z c β ℓ (δ+j) ((L^j) w)

theorem hasDerivAt_psiJ {M : LogModes M₅ M₃ M₄} (hM : IsLogIntertwining A₅ A₃ A₄ M)
    {K : ℕ} (hK : ∀ n k, K ≤ k → M n k = 0) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β δ : ℂ)
    (w : M₅) (j : ℕ) (ℓ : ℂ) :
    HasDerivAt (psiJ M K g z c β δ w (Lm1 A₅) j)
      (Complex.exp ℓ * psiJ M K g z c β δ w (Lm1 A₅) (j+1) ℓ) ℓ := by
  have h := hasDerivAt_outerEval hM hK g z c β (δ+j) ((Lm1 A₅ ^ j) w) ℓ
  have he : psiJ M K g z c β δ w (Lm1 A₅) (j+1) ℓ =
      outerEval M K g z c β ℓ (δ+j+1) (Lm1 A₅ ((Lm1 A₅ ^ j) w)) := by
    rw [psiJ, pow_succ', Module.End.mul_apply]
    congr 1
    push_cast; ring
  rw [he]
  exact h

/-- The translated evaluation `u ↦ ⟨g, M(w, e^ℓ(1+u))z⟩` at branch `ℓ + log(1+u)`. -/
def transEval (M : LogModes M₅ M₃ M₄) (K : ℕ) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β ℓ δ : ℂ)
    (w : M₅) (u : ℂ) : ℂ :=
  outerEval M K g z c β (ℓ+Complex.log (1+u)) δ w

theorem one_add_mem_slitPlane {u : ℂ} (hu : ‖u‖ < 1) : 1+u ∈ Complex.slitPlane := by
  refine Or.inl ?_
  have := Complex.abs_re_le_norm u
  rw [Complex.add_re, Complex.one_re]
  have := neg_abs_le u.re
  linarith

theorem one_add_ne_zero_of_norm {u : ℂ} (hu : ‖u‖ < 1) : 1+u ≠ 0 :=
  Complex.slitPlane_ne_zero (one_add_mem_slitPlane hu)

theorem differentiableAt_outerEval {M : LogModes M₅ M₃ M₄} (hM : IsLogIntertwining A₅ A₃ A₄ M)
    {K : ℕ} (hK : ∀ n k, K ≤ k → M n k = 0) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ)
    (w : M₅) (ℓ : ℂ) : DifferentiableAt ℂ (fun ℓ => outerEval M K g z c β ℓ γ w) ℓ :=
  (hasDerivAt_outerEval hM hK g z c β γ w ℓ).differentiableAt

theorem differentiableOn_transEval {M : LogModes M₅ M₃ M₄} (hM : IsLogIntertwining A₅ A₃ A₄ M)
    {K : ℕ} (hK : ∀ n k, K ≤ k → M n k = 0) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β ℓ δ : ℂ)
    (w : M₅) : DifferentiableOn ℂ (transEval M K g z c β ℓ δ w) (Metric.ball 0 1) := by
  intro u hu
  rw [Metric.mem_ball, dist_zero_right] at hu
  refine DifferentiableAt.differentiableWithinAt ?_
  have hl : DifferentiableAt ℂ (fun u : ℂ => ℓ+Complex.log (1+u)) u :=
    (differentiableAt_const _).add ((differentiableAt_const 1).add differentiableAt_id |>.clog
      (one_add_mem_slitPlane hu))
  exact (differentiableAt_outerEval hM hK g z c β δ w _).comp u hl

/-- The iterated derivatives of the translated evaluation. -/
theorem iteratedDeriv_transEval {M : LogModes M₅ M₃ M₄} (hM : IsLogIntertwining A₅ A₃ A₄ M)
    {K : ℕ} (hK : ∀ n k, K ≤ k → M n k = 0) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β ℓ δ : ℂ)
    (w : M₅) (j : ℕ) : ∀ u ∈ Metric.ball (0 : ℂ) 1,
      iteratedDeriv j (transEval M K g z c β ℓ δ w) u =
        Complex.exp (j*ℓ) * psiJ M K g z c β δ w (Lm1 A₅) j (ℓ+Complex.log (1+u)) := by
  induction j with
  | zero =>
    intro u _
    simp [transEval, psiJ]
  | succ j ih =>
    intro u hu
    have hu' : ‖u‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hu
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (transEval M K g z c β ℓ δ w) =ᶠ[nhds u]
        fun u => Complex.exp (j*ℓ) * psiJ M K g z c β δ w (Lm1 A₅) j (ℓ+Complex.log (1+u)) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hu) fun v hv => ih v hv
    rw [hev.deriv_eq]
    have hl : HasDerivAt (fun u : ℂ => ℓ+Complex.log (1+u)) (1/(1+u)) u := by
      have h := ((hasDerivAt_id u).const_add 1).clog (one_add_mem_slitPlane hu')
      have h' := h.const_add ℓ
      convert h' using 1
      try simp
    have hd : HasDerivAt (fun u => Complex.exp (j*ℓ) *
        psiJ M K g z c β δ w (Lm1 A₅) j (ℓ+Complex.log (1+u)))
        (Complex.exp (j*ℓ) * (Complex.exp (ℓ+Complex.log (1+u)) *
          psiJ M K g z c β δ w (Lm1 A₅) (j+1) (ℓ+Complex.log (1+u)) * (1/(1+u)))) u :=
      ((hasDerivAt_psiJ hM hK g z c β δ w j (ℓ+Complex.log (1+u))).comp u hl).const_mul
        (Complex.exp (j*ℓ))
    rw [hd.deriv]
    have h1 := one_add_ne_zero_of_norm hu'
    have he : Complex.exp (ℓ+Complex.log (1+u)) = Complex.exp ℓ * (1+u) := by
      rw [Complex.exp_add, Complex.exp_log h1]
    rw [he]
    have he2 : Complex.exp (((j+1 : ℕ) : ℂ)*ℓ) = Complex.exp (j*ℓ) * Complex.exp ℓ := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [he2]
    field_simp

/-- **Taylor expansion of the translated outer evaluation.** -/
theorem hasSum_outerEval_taylor {M : LogModes M₅ M₃ M₄} (hM : IsLogIntertwining A₅ A₃ A₄ M)
    {K : ℕ} (hK : ∀ n k, K ≤ k → M n k = 0) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β ℓ δ : ℂ)
    (w : M₅) {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ => ((j.factorial : ℂ))⁻¹ * u^j * Complex.exp (j*ℓ) *
        outerEval M K g z c β ℓ (δ+j) ((Lm1 A₅ ^ j) w))
      (outerEval M K g z c β (ℓ+Complex.log (1+u)) δ w) := by
  have hu' : u ∈ Metric.ball (0 : ℂ) 1 := by rwa [Metric.mem_ball, dist_zero_right]
  have h := Complex.hasSum_taylorSeries_on_ball (differentiableOn_transEval hM hK g z c β ℓ δ w) hu'
  refine h.congr_fun fun j => ?_
  rw [iteratedDeriv_transEval hM hK g z c β ℓ δ w j 0 (Metric.mem_ball_self one_pos)]
  simp only [add_zero, Complex.log_one, sub_zero, smul_eq_mul, psiJ]
  ring

/-- **Cauchy's estimate** for the Taylor coefficients. -/
theorem norm_outerEval_taylor_le {M : LogModes M₅ M₃ M₄} (hM : IsLogIntertwining A₅ A₃ A₄ M)
    {K : ℕ} (hK : ∀ n k, K ≤ k → M n k = 0) (g : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β ℓ δ : ℂ)
    (w : M₅) {R C : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hC : ∀ v ∈ Metric.sphere (0 : ℂ) R,
      ‖outerEval M K g z c β (ℓ+Complex.log (1+v)) δ w‖ ≤ C) (j : ℕ) :
    ‖Complex.exp (j*ℓ) * outerEval M K g z c β ℓ (δ+j) ((Lm1 A₅ ^ j) w)‖ ≤
      j.factorial * C / R^j := by
  have hd : DiffContOnCl ℂ (transEval M K g z c β ℓ δ w) (Metric.ball 0 R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    exact (differentiableOn_transEval hM hK g z c β ℓ δ w).mono
      (Metric.closedBall_subset_ball hR1)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR hd
    (fun v hv => hC v hv)
  rw [iteratedDeriv_transEval hM hK g z c β ℓ δ w j 0 (Metric.mem_ball_self one_pos)] at h
  simpa only [add_zero, Complex.log_one, psiJ] using h

end VOA.Huang.LogBraided
