/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMooreQSeries
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The modular Wronskian of an `S`-closed family (Anderson–Moore, step 2)

For a family `f : Fin n → ℂ → ℂ` of functions holomorphic on the upper half-plane, let
`ϑ^m = amSerreIter m` be the iterated Serre derivative and

* `jetMat f z = [ϑ^m f_j (z)]_{m,j}` (`m, j < n`), `topVec f z = (ϑ^n f_j (z))_j`;
* `wr f z = det (jetMat f z)` — the modular Wronskian;
* `wrc f z = cramer (jetMat f z)ᵀ (topVec f z)` — its Cramer minors, so that
  `wr_cramer`: `Σ_r wrc_r · ϑ^r f_j = wr · ϑ^n f_j` (the monic MLDE, with denominators cleared).

Transformation laws under `S : z ↦ −1/z` for a family closed under `S`
(`f_i(−1/z) = Σ_j S_ij f_j(z)`):

* `amSerreIter_S` — `ϑ^m f_i(−1/z) = z^{2m} Σ_j S_ij ϑ^m f_j(z)` (from the library's Serre
  equivariance `serreDerivC_slashC`);
* `wr_S` — `wr(−1/z) = z^{n(n−1)} · det S · wr(z)`;
* `wrc_S` — `wrc_r(−1/z) = z^{2n} · det S · (Π_{l≠r} z^{2l}) · wrc_r(z)` (via
  `adjugate_mul_distrib`, no division).

Under `T : z ↦ z + 1` for `q^ν`-families: `wr(z+1) = Π t_j · wr(z)`, `wrc(z+1) = Π t_j · wrc(z)`,
`t_j = e^{2πiν_j}`.

`exists_wr_ne_zero`: for `F_j = q^{ν_j} U_j` with pairwise distinct `ν_j` and `U_j(0) ≠ 0`,
the Wronskian is not identically zero: along `z = iy`, `e^{−2πiΣν z} wr(z) → Π U_j(0) ·
Vandermonde(ν)`, because the leading coefficient of `ϑ^m q^ν` is `Π_{l<m}(ν − l/6)`.

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

open Complex Filter Topology Matrix

noncomputable section

namespace VOA.Huang.AndersonMoore

open VOA

/-! ## Iterated Serre derivatives of analytic functions -/

theorem analyticAt_amSerreIter (m : ℕ) {f : ℂ → ℂ} (hf : ∀ z ∈ imGT 0, AnalyticAt ℂ f z)
    {z : ℂ} (hz : z ∈ imGT 0) : AnalyticAt ℂ (amSerreIter m f) z := by
  induction m generalizing z with
  | zero => exact hf z hz
  | succ m ih =>
    rw [amSerreIter_succ]
    -- `amSerreIter m f` is analytic near `z`
    have hev : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (amSerreIter m f) w := by
      filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
      exact ih hw
    exact analyticAt_serreDerivC _ (ih hz) hz

theorem ne_zero_of_mem_imGT {z : ℂ} (hz : z ∈ imGT 0) : z ≠ 0 := by
  rintro rfl; simp [imGT] at hz

theorem mobiusC_S (z : ℂ) : mobiusC ModularGroup.S z = -1 / z := by
  simp [mobiusC, denomC, ModularGroup.S]

theorem denomC_S (z : ℂ) : denomC ModularGroup.S z = z := by
  simp [denomC, ModularGroup.S]

theorem neg_one_div_mem_imGT {z : ℂ} (hz : z ∈ imGT 0) : -1 / z ∈ imGT 0 := by
  rw [← mobiusC_S]; exact mobiusC_mem_imGT _ hz

theorem add_one_mem_imGT {z : ℂ} (hz : z ∈ imGT 0) : z + 1 ∈ imGT 0 := by
  change (0 : ℝ) < (z + 1).im
  simpa using hz

/-- **`S`-equivariance of the iterated Serre derivative for an `S`-closed family.** -/
theorem amSerreIter_S {n : ℕ} {f : Fin n → ℂ → ℂ} (hf : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (f j) z)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : ∀ i, ∀ z ∈ imGT 0, f i (-1 / z) = ∑ j, S i j * f j z)
    (m : ℕ) (i : Fin n) {z : ℂ} (hz : z ∈ imGT 0) :
    amSerreIter m (f i) (-1 / z) = z ^ (2 * m) * ∑ j, S i j * amSerreIter m (f j) z := by
  induction m generalizing i z with
  | zero => simpa using hS i z hz
  | succ m ih =>
    have hz0 : z ≠ 0 := ne_zero_of_mem_imGT hz
    -- slash form of the induction hypothesis
    have hslash : ∀ i, ∀ w ∈ imGT 0, slashC (2 * (m : ℤ)) ModularGroup.S (amSerreIter m (f i)) w
        = ∑ j, S i j * amSerreIter m (f j) w := by
      intro i w hw
      have hw0 : w ≠ 0 := ne_zero_of_mem_imGT hw
      rw [slashC, mobiusC_S, denomC_S, ih i hw, mul_comm, ← mul_assoc,
        show (w : ℂ) ^ (-(2 * (m : ℤ))) * w ^ (2 * m) = 1 from by
          rw [zpow_neg, show (2 * (m : ℤ)) = ((2 * m : ℕ) : ℤ) from by push_cast; ring,
            zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hw0)], one_mul]
    have hdiff : DifferentiableAt ℂ (amSerreIter m (f i)) (mobiusC ModularGroup.S z) :=
      (analyticAt_amSerreIter m (hf i) (mobiusC_mem_imGT _ hz)).differentiableAt
    have hkey := serreDerivC_slashC (2 * (m : ℤ)) ModularGroup.S (amSerreIter m (f i)) hz hdiff
    -- the right side: Serre derivative of a finite sum
    have hev : slashC (2 * (m : ℤ)) ModularGroup.S (amSerreIter m (f i))
        =ᶠ[𝓝 z] fun w => ∑ j, S i j * amSerreIter m (f j) w := by
      filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
      exact hslash i w hw
    rw [serreDerivC_congr_of_eventuallyEq _ hev] at hkey
    have hsum : serreDerivC (2 * (m : ℤ)) (fun w => ∑ j, S i j * amSerreIter m (f j) w) z
        = ∑ j, S i j * serreDerivC (2 * (m : ℤ)) (amSerreIter m (f j)) z := by
      have h := serreDerivC_finset_sum (2 * (m : ℤ)) Finset.univ
        (fun j => fun w => S i j * amSerreIter m (f j) w) (z := z) (fun j _ =>
          (differentiableAt_const _).mul
            (analyticAt_amSerreIter m (hf j) hz).differentiableAt)
      rw [show (∑ j ∈ Finset.univ, fun w => S i j * amSerreIter m (f j) w)
          = fun w => ∑ j, S i j * amSerreIter m (f j) w from by
            funext w; simp] at h
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact serreDerivC_smul (2 * (m : ℤ)) (S i j) (amSerreIter m (f j)) (z := z)
        (analyticAt_amSerreIter m (hf j) hz).differentiableAt
    rw [hsum, slashC, mobiusC_S, denomC_S] at hkey
    simp only [amSerreIter_succ]
    rw [← hkey, show ((2 * (m : ℤ) + 2)) = ((2 * (m + 1) : ℕ) : ℤ) from by push_cast; ring,
      zpow_neg,
      zpow_natCast]
    field_simp
/-! ## The Wronskian and its Cramer minors -/

/-- The Serre jet matrix `[ϑ^m f_j(z)]_{m,j}`. -/
def jetMat {n : ℕ} (f : Fin n → ℂ → ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun m j => amSerreIter m (f j) z

/-- The top row `(ϑ^n f_j(z))_j`. -/
def topVec {n : ℕ} (f : Fin n → ℂ → ℂ) (z : ℂ) : Fin n → ℂ := fun j => amSerreIter n (f j) z

/-- The modular Wronskian. -/
def wr {n : ℕ} (f : Fin n → ℂ → ℂ) (z : ℂ) : ℂ := (jetMat f z).det

/-- The Cramer minors of the MLDE. -/
def wrc {n : ℕ} (f : Fin n → ℂ → ℂ) (z : ℂ) : Fin n → ℂ :=
  Matrix.cramer (jetMat f z)ᵀ (topVec f z)

/-- **The MLDE with cleared denominators**: `Σ_r wrc_r ϑ^r f_j = wr · ϑ^n f_j`. -/
theorem wr_cramer {n : ℕ} (f : Fin n → ℂ → ℂ) (z : ℂ) (j : Fin n) :
    ∑ r : Fin n, wrc f z r * amSerreIter r (f j) z = wr f z * amSerreIter n (f j) z := by
  have h := congrFun (Matrix.mulVec_cramer (jetMat f z)ᵀ (topVec f z)) j
  rw [Matrix.det_transpose] at h
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [wr, wrc, show amSerreIter n (f j) z = topVec f z j from rfl, ← h]
  exact Finset.sum_congr rfl fun r _ => by rw [mul_comm]; rfl

/-- The algebra behind the transformation law of the Cramer minors. -/
theorem cramer_transpose_mul {n : ℕ} (D M P : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℂ) :
    Matrix.cramer (D * M * Pᵀ)ᵀ (c • (P *ᵥ b))
      = (c * P.det) • (Matrix.adjugate Dᵀ *ᵥ Matrix.cramer Mᵀ b) := by
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.mulVec_smul,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec b (Matrix.adjugate P) P, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    smul_smul]

theorem prod_pow_two_mul (n : ℕ) (z : ℂ) :
    ∏ m : Fin n, z ^ (2 * (m : ℕ)) = z ^ (n * (n - 1)) := by
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun m => 2 * m) n,
    ← Finset.mul_sum, mul_comm, Finset.sum_range_id_mul_two]

/-! ## The law under `S` -/

theorem jetMat_S {n : ℕ} {f : Fin n → ℂ → ℂ} (hf : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (f j) z)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : ∀ i, ∀ z ∈ imGT 0, f i (-1 / z) = ∑ j, S i j * f j z)
    {z : ℂ} (hz : z ∈ imGT 0) :
    jetMat f (-1 / z) = Matrix.diagonal (fun m : Fin n => z ^ (2 * (m : ℕ))) * jetMat f z * Sᵀ := by
  ext m i
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, jetMat, Matrix.of_apply, Matrix.transpose_apply]
  rw [amSerreIter_S hf S hS m i hz, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem topVec_S {n : ℕ} {f : Fin n → ℂ → ℂ} (hf : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (f j) z)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : ∀ i, ∀ z ∈ imGT 0, f i (-1 / z) = ∑ j, S i j * f j z)
    {z : ℂ} (hz : z ∈ imGT 0) :
    topVec f (-1 / z) = z ^ (2 * n) • (S *ᵥ topVec f z) := by
  funext i
  simp only [topVec, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact amSerreIter_S hf S hS n i hz

/-- **The Wronskian is a modular form of weight `n(n−1)` with character `det S` at `S`.** -/
theorem wr_S {n : ℕ} {f : Fin n → ℂ → ℂ} (hf : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (f j) z)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : ∀ i, ∀ z ∈ imGT 0, f i (-1 / z) = ∑ j, S i j * f j z)
    {z : ℂ} (hz : z ∈ imGT 0) :
    wr f (-1 / z) = z ^ (n * (n - 1)) * S.det * wr f z := by
  rw [wr, jetMat_S hf S hS hz, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose, prod_pow_two_mul, wr]
  ring

/-- **The Cramer minors at `S`.** -/
theorem wrc_S {n : ℕ} {f : Fin n → ℂ → ℂ} (hf : ∀ j, ∀ z ∈ imGT 0, AnalyticAt ℂ (f j) z)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : ∀ i, ∀ z ∈ imGT 0, f i (-1 / z) = ∑ j, S i j * f j z)
    {z : ℂ} (hz : z ∈ imGT 0) (r : Fin n) :
    wrc f (-1 / z) r
      = z ^ (2 * n) * S.det * (∏ l ∈ Finset.univ.erase r, z ^ (2 * (l : ℕ))) * wrc f z r := by
  rw [wrc, jetMat_S hf S hS hz, topVec_S hf S hS hz, cramer_transpose_mul,
    Matrix.diagonal_transpose, Matrix.adjugate_diagonal]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal, wrc]
  ring

/-! ## `q^ν`-families: the law under `T` -/

/-- The family `F_j = q^{ν_j} U_j`. -/
def famF {n : ℕ} (ν : Fin n → ℂ) (U : Fin n → PowerSeries ℂ) : Fin n → ℂ → ℂ :=
  fun j => amEval (ν j) (U j)

/-- The `T`-eigenvalues `e^{2πiν_j}`. -/
def tvec {n : ℕ} (ν : Fin n → ℂ) : Fin n → ℂ :=
  fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ν j)

theorem analyticAt_famF {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (j : Fin n) : ∀ z ∈ imGT 0, AnalyticAt ℂ (famF ν U j) z :=
  fun _ hz => analyticAt_amEval (hU j) hz

theorem amSerreIter_famF_add_one {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (m : ℕ) (j : Fin n) {z : ℂ} (hz : z ∈ imGT 0) :
    amSerreIter m (famF ν U j) (z + 1) = tvec ν j * amSerreIter m (famF ν U j) z := by
  rw [famF, amSerreIter_amEval _ m (hU j) (add_one_mem_imGT hz), amEval_add_one,
    amSerreIter_amEval _ m (hU j) hz, tvec]

theorem jetMat_T {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) :
    jetMat (famF ν U) (z + 1) = 1 * jetMat (famF ν U) z * (Matrix.diagonal (tvec ν))ᵀ := by
  ext m j
  rw [Matrix.diagonal_transpose, one_mul, Matrix.mul_diagonal]
  simp only [jetMat, Matrix.of_apply]
  rw [amSerreIter_famF_add_one ν hU m j hz, mul_comm]

theorem topVec_T {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) :
    topVec (famF ν U) (z + 1) = (1 : ℂ) • (Matrix.diagonal (tvec ν) *ᵥ topVec (famF ν U) z) := by
  funext j
  rw [one_smul, Matrix.mulVec_diagonal]
  exact amSerreIter_famF_add_one ν hU n j hz

theorem wr_T {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) :
    wr (famF ν U) (z + 1) = (∏ j, tvec ν j) * wr (famF ν U) z := by
  rw [wr, jetMat_T ν hU hz, Matrix.det_mul, Matrix.det_mul, Matrix.det_one,
    Matrix.det_transpose, Matrix.det_diagonal, wr]
  ring

theorem wrc_T {n : ℕ} (ν : Fin n → ℂ) {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) (r : Fin n) :
    wrc (famF ν U) (z + 1) r = (∏ j, tvec ν j) * wrc (famF ν U) z r := by
  rw [wrc, jetMat_T ν hU hz, topVec_T ν hU hz, cramer_transpose_mul, Matrix.transpose_one,
    Matrix.adjugate_one, Matrix.one_mulVec, Matrix.det_diagonal, one_mul, wrc]
  rfl

/-! ## Nonvanishing of the Wronskian -/

theorem amEval_eq_exp_mul (ν : ℂ) (U : PowerSeries ℂ) (z : ℂ) :
    amEval ν U z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * ν) * amEval 0 U z := by
  rw [amEval, amEval, mul_zero, Complex.exp_zero, one_mul]

theorem constantCoeff_serreF (k : ℤ) (ν : ℂ) (U : PowerSeries ℂ) :
    PowerSeries.coeff 0 (serreF k ν U) = (ν - k / 12) * PowerSeries.coeff 0 U := by
  rw [serreF, map_add, coeff_thetaNu, PowerSeries.coeff_smul, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp [G1ser]
  ring

/-- The leading-coefficient polynomial `p_m = Π_{l<m} (X − l/6)`. -/
def leadPoly (m : ℕ) : Polynomial ℂ :=
  ∏ l ∈ Finset.range m, (Polynomial.X - Polynomial.C ((l : ℂ) / 6))

theorem leadPoly_monic (m : ℕ) : (leadPoly m).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem leadPoly_natDegree (m : ℕ) : (leadPoly m).natDegree = m := by
  rw [leadPoly, Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _]
  simp

theorem coeff_zero_amSerreF (ν : ℂ) (m : ℕ) (U : PowerSeries ℂ) :
    PowerSeries.coeff 0 (amSerreF ν m U) = (leadPoly m).eval ν * PowerSeries.coeff 0 U := by
  induction m with
  | zero => simp [leadPoly]
  | succ m ih =>
    rw [amSerreF_succ, constantCoeff_serreF, ih]
    simp only [leadPoly, Finset.prod_range_succ, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    push_cast
    ring

/-- **The Wronskian of a `q^ν`-family with distinct exponents is not identically zero.** -/
theorem exists_wr_ne_zero {n : ℕ} {ν : Fin n → ℂ} {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (hν : Function.Injective ν)
    (hU0 : ∀ j, PowerSeries.coeff 0 (U j) ≠ 0) :
    ∃ z ∈ imGT 0, wr (famF ν U) z ≠ 0 := by
  classical
  -- the reduced matrix
  let Mt : ℂ → Matrix (Fin n) (Fin n) ℂ := fun z =>
    Matrix.of fun m j => amEval 0 (amSerreF (ν j) m (U j)) z
  let M0 : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun m j => (leadPoly m).eval (ν j) * PowerSeries.coeff 0 (U j)
  have hsplit : ∀ z ∈ imGT 0, jetMat (famF ν U) z
      = Mt z *
        Matrix.diagonal (fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * ν j)) := by
    intro z hz
    ext m j
    rw [Matrix.mul_diagonal]
    simp only [jetMat, Matrix.of_apply, Mt, famF]
    rw [amSerreIter_amEval _ m (hU j) hz, amEval_eq_exp_mul, mul_comm]
  have hlim : Tendsto (fun y : ℝ => Mt (Complex.I * y)) atTop (𝓝 M0) := by
    refine tendsto_pi_nhds.2 fun m => tendsto_pi_nhds.2 fun j => ?_
    simp only [Mt, M0, Matrix.of_apply]
    rw [← coeff_zero_amSerreF]
    exact tendsto_amEval_zero (amSerreF_mem _ m (hU j))
  have hdet : Tendsto (fun y : ℝ => (Mt (Complex.I * y)).det) atTop (𝓝 M0.det) :=
    ((continuous_id.matrix_det).tendsto M0).comp hlim
  have hM0 : M0.det ≠ 0 := by
    have hfac : M0 = (Matrix.of fun (m j : Fin n) => (leadPoly m).eval (ν j)) *
        Matrix.diagonal (fun j => PowerSeries.coeff 0 (U j)) := by
      ext m j; rw [Matrix.mul_diagonal]; rfl
    rw [hfac, Matrix.det_mul, Matrix.det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun j _ => hU0 j)
    have hV := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde ν
      (fun i : Fin n => leadPoly i) (fun i => leadPoly_natDegree i) (fun i => leadPoly_monic i)
    have ht : (Matrix.of fun (m j : Fin n) => (leadPoly m).eval (ν j))
        = (Matrix.of fun (i j : Fin n) => (leadPoly j).eval (ν i))ᵀ := by
      ext; rfl
    rw [ht, Matrix.det_transpose, ← hV]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hν
  obtain ⟨y, hy, hy0⟩ := ((hdet.eventually_ne hM0).and (eventually_gt_atTop 0)).exists
  refine ⟨Complex.I * y, I_mul_mem_imGT hy0, ?_⟩
  rw [wr, hsplit _ (I_mul_mem_imGT hy0), Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero hy (Finset.prod_ne_zero_iff.mpr fun j _ => Complex.exp_ne_zero _)

end VOA.Huang.AndersonMoore
