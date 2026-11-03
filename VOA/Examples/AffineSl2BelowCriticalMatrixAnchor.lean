/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BelowCriticalMatrixRigidity
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The large-negative-level anchor for layer signs of polynomial Hermitian matrices

Pure linear algebra and asymptotics; nothing VOA-specific.

Let `P` be a matrix of polynomials on a finite index set with a length function `ℓ` such that

* `deg P_ij ≤ min(ℓ i, ℓ j)`;
* for `ℓ i = ℓ j` the coefficient of `X^{ℓ i}` in `P_ij` is `δ_ij d_i` with `d_i > 0` real;
* `P(x)` is Hermitian for all sufficiently negative real `x`.

Then for every sufficiently negative real `x` the matrix `P(x)` has all graded-unitary layer signs
(`matrixLayerSign_eventually`).  Proof: rescaling by `diag(μ^{ℓ i})` with `x = -μ²` gives a
family tending to `diag((-1)^{ℓ i} d_i)`, whose Schur complements have the required definite
signs; positive definiteness is an open condition, and layer signs are invariant under
congruence by a positive diagonal matrix.
-/

namespace VOA

namespace MatrixRigidity

open Matrix Filter Topology Polynomial
open scoped ComplexOrder

noncomputable section

/-! ## Positive definiteness is an open condition -/

/-- A Hermitian matrix whose quadratic form has positive real part on the unit sphere is
positive definite. -/
theorem posDef_of_sphere {n : Type*} [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : ∀ x ∈ Metric.sphere (0 : n → ℂ) 1, 0 < (star x ⬝ᵥ (A *ᵥ x)).re) : A.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨hA, fun y hy => ?_⟩
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  set c : ℂ := ((‖y‖⁻¹ : ℝ) : ℂ) with hc
  have hxs : c • y ∈ Metric.sphere (0 : n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hny), inv_mul_cancel₀ hny.ne']
  have hpos := h _ hxs
  have hscale : star (c • y) ⬝ᵥ (A *ᵥ (c • y)) =
      ((‖y‖⁻¹ ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (A *ᵥ y)) := by
    rw [mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      hc, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [hscale, Complex.re_ofReal_mul] at hpos
  have hre : 0 < (star y ⬝ᵥ (A *ᵥ y)).re := pos_of_mul_pos_right hpos (by positivity)
  have him : (star y ⬝ᵥ (A *ᵥ y)).im = 0 := by
    simpa using hA.im_star_dotProduct_mulVec_self y
  exact Complex.pos_iff.mpr ⟨hre, him.symm⟩

/-- **Positive definiteness persists along convergent families of Hermitian matrices.** -/
theorem posDef_eventually {α : Type*} {l : Filter α} {n : Type*} [Fintype n]
    {T : α → Matrix n n ℂ} {T₀ : Matrix n n ℂ} (hT : Tendsto T l (𝓝 T₀))
    (hH : ∀ᶠ a in l, (T a).IsHermitian) (hP : T₀.PosDef) : ∀ᶠ a in l, (T a).PosDef := by
  have hK : IsCompact (Metric.sphere (0 : n → ℂ) 1) := isCompact_sphere 0 1
  have hF : Continuous fun p : Matrix n n ℂ × (n → ℂ) => star p.2 ⬝ᵥ (p.1 *ᵥ p.2) :=
    (continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hO : ∀ᶠ A in 𝓝 T₀, ∀ x ∈ Metric.sphere (0 : n → ℂ) 1, 0 < (star x ⬝ᵥ (A *ᵥ x)).re := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx; exact zero_ne_one hx
    have hpos : 0 < (star x ⬝ᵥ (T₀ *ᵥ x)).re :=
      (Complex.pos_iff.mp (hP.dotProduct_mulVec_pos hx0)).1
    exact (Complex.continuous_re.comp hF).continuousAt.eventually (lt_mem_nhds hpos)
  filter_upwards [hT.eventually hO, hH] with a ha hha
  exact posDef_of_sphere hha ha

/-! ## Congruence by a positive diagonal matrix -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ}

/-- Layer signs are invariant under congruence by a positive real diagonal matrix. -/
theorem matrixLayerSign_congr {M : Matrix ι ι ℂ} (s : ι → ℝ) (hs : ∀ i, 0 < s i) (r : ℕ)
    (hM : MatrixLayerSign ℓ M r) :
    MatrixLayerSign ℓ (fun i j => (s i : ℂ) * M i j * (s j : ℂ)) r := by
  intro y hsupp horth hy
  set z : ι → ℂ := fun i => (s i : ℂ) * y i with hz
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.mpr (hs i).ne'
  have hmv : ∀ i, ((fun i j => (s i : ℂ) * M i j * (s j : ℂ)) *ᵥ y) i =
      (s i : ℂ) * (M *ᵥ z) i := by
    intro i
    simp only [mulVec, dotProduct, z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hzsupp : ∀ i, r < ℓ i → z i = 0 := fun i hi => by simp [z, hsupp i hi]
  have hzorth : ∀ i, ℓ i < r → (M *ᵥ z) i = 0 := by
    intro i hi
    have := horth i hi
    rw [hmv] at this
    exact (mul_eq_zero.mp this).resolve_left (hs0 i)
  have hzne : z ≠ 0 := by
    intro h
    apply hy
    funext i
    have := congrFun h i
    simp only [z, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (hs0 i)
  have hq : star y ⬝ᵥ ((fun i j => (s i : ℂ) * M i j * (s j : ℂ)) *ᵥ y) =
      star z ⬝ᵥ (M *ᵥ z) := by
    simp only [dotProduct, hmv, z, Pi.star_apply, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hq]
  exact hM z hzsupp hzorth hzne

/-! ## The model: a signed positive diagonal matrix -/

/-- A diagonal matrix with positive real entries is positive definite. -/
theorem posDef_diagonal_pos {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ)
    (hd : ∀ i, 0 < d i) : (diagonal fun i => (d i : ℂ)).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun y hy => ?_⟩
  · exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by
      simp [Complex.star_def, Complex.conj_ofReal])
  · have hterm : ∀ i, star y i * ((diagonal fun i => (d i : ℂ)) *ᵥ y) i =
        ((d i * Complex.normSq (y i) : ℝ) : ℂ) := by
      intro i
      rw [mulVec_diagonal, Pi.star_apply, Complex.star_def]
      push_cast
      rw [← Complex.mul_conj, mul_comm (y i)]
      ring
    simp only [dotProduct, hterm]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    rw [← Complex.ofReal_sum]
    apply Complex.zero_lt_real.mpr
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hd j).le (Complex.normSq_nonneg _))
    exact ⟨i, Finset.mem_univ i, mul_pos (hd i) (Complex.normSq_pos.mpr hi)⟩

/-! ## Asymptotics of the rescaled matrix -/

theorem tendsto_inv_pow (k : ℕ) :
    Tendsto (fun μ : ℝ => ((μ : ℂ)⁻¹) ^ k) atTop (𝓝 (if k = 0 then 1 else 0)) := by
  have h0 : Tendsto (fun μ : ℝ => ((μ : ℂ))⁻¹) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def, Complex.ofReal_inv] using this
  split_ifs with hk
  · subst hk; simp
  · simpa [zero_pow hk] using h0.pow k

/-- One rescaled monomial. -/
theorem rescaled_monomial {μ : ℂ} (hμ : μ ≠ 0) {a b m : ℕ} (hm : 2 * m ≤ a + b) :
    (-μ ^ 2) ^ m / (μ ^ a * μ ^ b) = (-1) ^ m * (μ⁻¹) ^ (a + b - 2 * m) := by
  have hpow : μ ^ a * μ ^ b = μ ^ (a + b - 2 * m) * μ ^ (2 * m) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hpow, neg_pow, ← pow_mul, inv_pow]
  field_simp

variable (ℓ) in
/-- The rescaled matrix `diag(μ^{-ℓ}) P(-μ²) diag(μ^{-ℓ})`. -/
def rescaled (P : Matrix ι ι ℂ[X]) (μ : ℝ) : Matrix ι ι ℂ :=
  fun i j => (P i j).eval (-(μ : ℂ) ^ 2) / ((μ : ℂ) ^ ℓ i * (μ : ℂ) ^ ℓ j)

/-- **The rescaled matrix tends to the signed diagonal model.** -/
theorem tendsto_rescaled (P : Matrix ι ι ℂ[X]) (d : ι → ℝ)
    (hdeg : ∀ i j, (P i j).natDegree ≤ min (ℓ i) (ℓ j))
    (htop : ∀ i j, ℓ i = ℓ j → (P i j).coeff (ℓ i) = if i = j then (d i : ℂ) else 0) :
    Tendsto (rescaled ℓ P) atTop
      (𝓝 (diagonal fun i => (-1 : ℂ) ^ ℓ i * (d i : ℂ))) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  set a := ℓ i
  set b := ℓ j
  have hN : (P i j).natDegree < min a b + 1 := Nat.lt_succ_of_le (hdeg i j)
  have heq : ∀ᶠ μ : ℝ in atTop, rescaled ℓ P μ i j =
      ∑ m ∈ Finset.range (min a b + 1),
        (P i j).coeff m * ((-1) ^ m * ((μ : ℂ)⁻¹) ^ (a + b - 2 * m)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
    have hμ0 : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
    simp only [rescaled]
    rw [eval_eq_sum_range' hN, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : 2 * m ≤ a + b := by
      have := Finset.mem_range.mp hm
      omega
    rw [mul_div_assoc, rescaled_monomial hμ0 hm']
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  have hlim : Tendsto (fun μ : ℝ => ∑ m ∈ Finset.range (min a b + 1),
      (P i j).coeff m * ((-1) ^ m * ((μ : ℂ)⁻¹) ^ (a + b - 2 * m))) atTop
      (𝓝 (∑ m ∈ Finset.range (min a b + 1),
        (P i j).coeff m * ((-1) ^ m * (if a + b - 2 * m = 0 then 1 else 0)))) :=
    tendsto_finset_sum _ fun m _ =>
      tendsto_const_nhds.mul (tendsto_const_nhds.mul (tendsto_inv_pow _))
  convert hlim using 2
  -- evaluate the limit
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, Finset.sum_eq_single a]
    · rw [if_pos (show a + a - 2 * a = 0 by omega), htop i i rfl, if_pos rfl]
      ring
    · intro m hm hma
      have : a + a - 2 * m ≠ 0 := by
        have := Finset.mem_range.mp hm
        omega
      rw [if_neg this, mul_zero, mul_zero]
    · intro ha
      exact absurd (Finset.mem_range.mpr (by omega)) ha
  · rw [diagonal_apply_ne _ hij]
    symm
    refine Finset.sum_eq_zero fun m hm => ?_
    by_cases hm2 : a + b - 2 * m = 0
    · have hmr := Finset.mem_range.mp hm
      have hma : m = a := by omega
      have hab : ℓ i = ℓ j := by omega
      rw [hma, htop i j hab, if_neg hij, zero_mul]
    · rw [if_neg hm2, mul_zero, mul_zero]

/-! ## Convergence of Schur complements -/

theorem tendsto_matrix_mul' {α : Type*} {l : Filter α} {m n p : Type*} [Fintype n]
    {f : α → Matrix m n ℂ} {g : α → Matrix n p ℂ} {F : Matrix m n ℂ} {G : Matrix n p ℂ}
    (hf : Tendsto f l (𝓝 F)) (hg : Tendsto g l (𝓝 G)) :
    Tendsto (fun a => f a * g a) l (𝓝 (F * G)) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun q => ?_
  simp only [Matrix.mul_apply]
  exact tendsto_finset_sum _ fun j _ =>
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf i) j).mul
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hg j) q)

theorem tendsto_submatrix' {α : Type*} {l : Filter α} {m n m' n' : Type*}
    {f : α → Matrix m n ℂ} {F : Matrix m n ℂ} (hf : Tendsto f l (𝓝 F))
    (e₁ : m' → m) (e₂ : n' → n) :
    Tendsto (fun a => (f a).submatrix e₁ e₂) l (𝓝 (F.submatrix e₁ e₂)) :=
  ((continuous_id.matrix_submatrix e₁ e₂).tendsto F).comp hf

theorem tendsto_schur {α : Type*} {l : Filter α} {M : α → Matrix ι ι ℂ} {L : Matrix ι ι ℂ}
    (hM : Tendsto M l (𝓝 L)) (r : ℕ) (hL : (stepMatrix ℓ L r).det ≠ 0) :
    Tendsto (fun a => schur ℓ (M a) r) l (𝓝 (schur ℓ L r)) := by
  have hstep : Tendsto (fun a => stepMatrix ℓ (M a) r) l (𝓝 (stepMatrix ℓ L r)) :=
    tendsto_submatrix' hM _ _
  have hinv : Tendsto (fun a => (stepMatrix ℓ (M a) r)⁻¹) l (𝓝 (stepMatrix ℓ L r)⁻¹) := by
    have h1 : ∀ A : Matrix {i // ℓ i < r} {i // ℓ i < r} ℂ, A⁻¹ = (A.det)⁻¹ • A.adjugate := by
      intro A; rw [inv_def, Ring.inverse_eq_inv']
    simp only [h1]
    have hdet := ((continuous_id.matrix_det).tendsto _).comp hstep
    have hadj := ((continuous_id.matrix_adjugate).tendsto _).comp hstep
    exact (hdet.inv₀ hL).smul hadj
  unfold schur blkEE blkEL blkLE
  exact (tendsto_submatrix' hM _ _).sub
    (tendsto_matrix_mul' (tendsto_matrix_mul' (tendsto_submatrix' hM _ _) hinv)
      (tendsto_submatrix' hM _ _))

/-! ## The anchor -/

/-- Past the largest length, a layer-sign condition only asks for a trivial kernel. -/
theorem matrixLayerSign_of_large {A : Matrix ι ι ℂ} {R : ℕ} (hR : ∀ i, ℓ i < R)
    (hA : (stepMatrix ℓ A R).det ≠ 0) {r : ℕ} (hr : R ≤ r) : MatrixLayerSign ℓ A r := by
  intro y _ horth hy
  exfalso
  apply hy
  set z : {i // ℓ i < R} → ℂ := fun i => y i
  have hz : stepMatrix ℓ A R *ᵥ z = 0 := by
    funext i
    have := horth i.1 (by have := hR i.1; omega)
    change (stepMatrix ℓ A R *ᵥ z) i = 0
    rw [← this]
    change ∑ j : {i // ℓ i < R}, A i j * y j = ∑ j, A i j * y j
    exact sum_subtype_of_vanish (fun j => ℓ j < R) (fun j => A i j * y j)
      (fun j hj => absurd (hR j) hj)
  have hz0 := Matrix.eq_zero_of_mulVec_eq_zero hA hz
  funext i
  exact congrFun hz0 ⟨i, hR i⟩

theorem stepMatrix_diagonal (D : ι → ℂ) (r : ℕ) :
    stepMatrix ℓ (diagonal D) r = diagonal fun i : {i // ℓ i < r} => D i := by
  ext i j
  simp only [stepMatrix, submatrix_apply, diagonal_apply, Subtype.ext_iff]

theorem schur_diagonal (D : ι → ℂ) (r : ℕ) :
    schur ℓ (diagonal D) r = diagonal fun i : {i // ℓ i = r} => D i := by
  have hEL : blkEL ℓ (diagonal D) r = 0 := by
    ext i j
    simp only [blkEL, submatrix_apply, diagonal_apply, zero_apply]
    rw [if_neg]
    intro h
    have h1 := i.2
    have h2 := j.2
    rw [h] at h1
    omega
  rw [schur, hEL, Matrix.zero_mul, Matrix.zero_mul, sub_zero]
  ext i j
  simp only [blkEE, submatrix_apply, diagonal_apply, Subtype.ext_iff]

/-- **The large-negative-level anchor for polynomial Hermitian matrices.** -/
theorem matrixLayerSign_eventually (P : Matrix ι ι ℂ[X]) (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hdeg : ∀ i j, (P i j).natDegree ≤ min (ℓ i) (ℓ j))
    (htop : ∀ i j, ℓ i = ℓ j → (P i j).coeff (ℓ i) = if i = j then (d i : ℂ) else 0)
    (x₀ : ℝ) (hherm : ∀ x : ℝ, x < x₀ → (P.map (Polynomial.eval (x : ℂ))).IsHermitian) :
    ∃ K : ℝ, ∀ x : ℝ, x < K → ∀ r, MatrixLayerSign ℓ (P.map (Polynomial.eval (x : ℂ))) r := by
  set D : ι → ℂ := fun i => (-1 : ℂ) ^ ℓ i * (d i : ℂ) with hD
  set L : Matrix ι ι ℂ := diagonal D
  have hDne : ∀ i, D i ≠ 0 := fun i =>
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.ofReal_ne_zero.mpr (hd i).ne')
  have hT := tendsto_rescaled P d hdeg htop
  have hLstep : ∀ r, (stepMatrix ℓ L r).det ≠ 0 := by
    intro r
    rw [stepMatrix_diagonal, det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hDne i
  -- eventually Hermitian
  have hB : ∀ᶠ μ : ℝ in atTop, |x₀| + 1 < μ := eventually_gt_atTop _
  have hHerm : ∀ᶠ μ : ℝ in atTop, (rescaled ℓ P μ).IsHermitian := by
    filter_upwards [hB] with μ hμ
    have hμ0 : 0 < μ := by have := abs_nonneg x₀; linarith
    have hx : -μ ^ 2 < x₀ := by
      have h1 : |x₀| < μ := by linarith
      have h2 : -x₀ ≤ |x₀| := neg_le_abs x₀
      nlinarith
    have hP := hherm _ hx
    ext i j
    have hPij := congrFun (congrFun hP i) j
    simp only [conjTranspose_apply, map_apply, Complex.star_def] at hPij
    simp only [rescaled, conjTranspose_apply]
    rw [star_div₀, star_mul', star_pow, star_pow, Complex.star_def, Complex.conj_ofReal]
    have hc : ((((-μ ^ 2 : ℝ)) : ℂ)) = -(μ : ℂ) ^ 2 := by push_cast; ring
    rw [hc] at hPij
    rw [hPij, mul_comm]
  -- eventually the step minors are nonzero
  have hStep : ∀ r, ∀ᶠ μ : ℝ in atTop, (stepMatrix ℓ (rescaled ℓ P μ) r).det ≠ 0 := by
    intro r
    have := ((continuous_id.matrix_det).tendsto _).comp (tendsto_submatrix' hT
      (Subtype.val : {i // ℓ i < r} → ι) Subtype.val)
    exact this.eventually_ne (hLstep r)
  -- eventually each layer sign below the maximal length
  have hLayer : ∀ r, ∀ᶠ μ : ℝ in atTop, MatrixLayerSign ℓ (rescaled ℓ P μ) r := by
    intro r
    have hS := (tendsto_schur hT r (hLstep r)).const_smul ((-1 : ℂ) ^ r)
    have hLpos : ((-1 : ℂ) ^ r • schur ℓ L r).PosDef := by
      rw [schur_diagonal]
      have : ((-1 : ℂ) ^ r • diagonal fun i : {i // ℓ i = r} => D i) =
          diagonal fun i : {i // ℓ i = r} => ((d i : ℝ) : ℂ) := by
        ext i j
        simp only [smul_apply, diagonal_apply, hD, smul_eq_mul]
        split_ifs
        · rw [i.2, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
        · simp
      rw [this]
      exact posDef_diagonal_pos (fun i : {i // ℓ i = r} => d i.1) (fun i => hd i.1)
    have hHs : ∀ᶠ μ : ℝ in atTop, ((-1 : ℂ) ^ r • schur ℓ (rescaled ℓ P μ) r).IsHermitian := by
      filter_upwards [hHerm] with μ hμ
      unfold IsHermitian
      rw [conjTranspose_smul, (schur_isHermitian (r := r) hμ).eq]
      simp
    filter_upwards [posDef_eventually hS hHs hLpos, hHerm, hStep r] with μ hμ hμH hμS
    exact (matrixLayerSign_iff_schur hμS hμH).mpr hμ
  -- all lengths
  set R : ℕ := Finset.univ.sup ℓ + 1
  have hR : ∀ i, ℓ i < R := fun i => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  have hAll : ∀ᶠ μ : ℝ in atTop, ∀ r, MatrixLayerSign ℓ (rescaled ℓ P μ) r := by
    have hfin := (Filter.eventually_all_finset (Finset.range R)).mpr fun r _ => hLayer r
    filter_upwards [hfin, hStep R] with μ hμ hμR r
    by_cases hr : r < R
    · exact hμ r (Finset.mem_range.mpr hr)
    · exact matrixLayerSign_of_large hR hμR (by omega)
  -- undo the rescaling
  have hP : ∀ᶠ μ : ℝ in atTop,
      ∀ r, MatrixLayerSign ℓ (P.map (Polynomial.eval (((-μ ^ 2 : ℝ)) : ℂ))) r := by
    filter_upwards [hAll, eventually_gt_atTop (0 : ℝ)] with μ hμ hμ0 r
    have hcong := matrixLayerSign_congr (M := rescaled ℓ P μ) (fun i => μ ^ ℓ i)
      (fun i => pow_pos hμ0 _) r (hμ r)
    convert hcong using 1
    ext i j
    have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ0.ne'
    simp only [map_apply, rescaled]
    push_cast
    field_simp
  obtain ⟨μ₀, hμ₀⟩ := eventually_atTop.mp hP
  refine ⟨-(max μ₀ 1) ^ 2, fun x hx r => ?_⟩
  have hpos : 0 ≤ -x := by nlinarith [sq_nonneg (max μ₀ 1)]
  have hμ : μ₀ ≤ Real.sqrt (-x) := by
    have h1 : (max μ₀ 1) ^ 2 < -x := by linarith
    have h2 : max μ₀ 1 < Real.sqrt (-x) :=
      Real.lt_sqrt (le_trans zero_le_one (le_max_right _ _)) |>.mpr h1
    exact le_trans (le_max_left _ _) h2.le
  have := hμ₀ _ hμ r
  rwa [Real.sq_sqrt hpos, neg_neg] at this

end

end MatrixRigidity

end VOA
