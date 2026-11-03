/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Order

/-!
# Lee–Yang graded unitarity: the finite-dimensional reduction around the cochain inequality

This file formalizes the *matrix* part of a length-induction argument for graded unitarity
of the Lee–Yang vacuum module, by reconstruction of the cochain at each PBW length.

At a fixed conformal weight `N` and PBW length `r+1` of the simple Lee–Yang vacuum module,
the argument has the following exact finite-dimensional data (all matrices real):

* `Q`, positive definite: the inverse-metric Gram of multiplication from the preceding length
  (`Q = Σ_i T_i g_r[N-i]⁻¹ T_iᵀ`);
* `S`, the sign-adjusted Schur form of the new physical layer (Hermitian, sign unknown);
* the **reconstruction identity** `Q S Q = K` with `K = M + R` built from preceding-length data;
* the **null (Riccati) identity** `S Q S - a_N S = P` with `P = Σ_i A_iᵀ S_{N-i} A_i` built from the
  same length at lower weights, `a_N = N(N+1/5)/2 > 0`.

The theorems below are exactly the steps that turn the *uniform complete-cochain inequality*
`K ≥ 0` into graded unitarity at the new length, together with the sharpened form of the
conclusion that the Riccati identity forces:

* `posSemidef_inv_conj` — `K ≥ 0 ⇒ S = Q⁻¹ K Q⁻¹ ≥ 0`.
* `posDef_of_posSemidef_isUnit` — semidefinite plus nondegenerate is definite (the campaign's
  conditional prefix-nondegeneracy input).
* `posDef_of_riccati_posDef` — the *kernel descent*: `S ≥ 0`, `S Q S - a S = P` and `P > 0` force
  `S > 0` (a vector in the radical of `S` is killed by every lowering map).
* `posDef_sum_transpose_mul_mul` — `P = Σ A_iᵀ S_i A_i` is definite when the `S_i` are and the
  lowering maps have trivial joint kernel.
* `riccati_margin` — the **gap**: any positive definite Riccati solution satisfies
  `S ≥ a Q⁻¹`.  Hence, given lower-weight positivity, the inequality `K ≥ 0` is *equivalent* to
  the a priori stronger `K ≥ a_N Q`; the negative Riccati branch is separated from the physical one
  by the whole interval `(0, a_N)` in the `Q`-whitened spectrum.  The proof is square-root free.
* `tower_posDef` — the abstract weight induction: if at every weight the reconstruction gives
  `K_N ≥ 0`, the Riccati identity holds, and either the layer is nondegenerate or the lowering
  maps have trivial joint kernel, then every `S_N` is positive definite with margin `a_N Q_N⁻¹`.
* `posDef_of_inv_lower_bound` — the **`P`-whitened dichotomy**: a symmetric invertible Riccati
  solution with `S⁻¹ + a P⁻¹ ≥ 0` is positive definite.  This is the matrix step of the Bochner
  reduction (a Riccati reformulation of the gap margin): the Bochner identity
  on exact cochains gives exactly that lower bound whenever the Bochner form `𝔅` is nonnegative,
  so `𝔅 ≥ 0` implies graded unitarity at the new weight.

## What is and is not formalized

Everything here is unconditional finite-dimensional linear algebra over `ℝ`.  **Not**
formalized: that the Lee–Yang module actually produces matrices satisfying the hypotheses
(the Gordon-ring identification, the reconstruction identity `Q S Q = M + R`, the null
identity, and conditional nondegeneracy).  Those are paper-level theorems of the campaign.
In particular the uniform inequality `K_N ≥ 0` is an *open* hypothesis, not a theorem, and this
file must not be cited as a proof of graded unitarity.

Conventions: `x ⬝ᵥ M *ᵥ x` is the real quadratic form; `PosSemidef`/`PosDef` are Mathlib's.
-/

open Matrix

namespace VOA.LeeYangRiccati

variable {n : Type*} [Fintype n]

/-! ### Real quadratic-form conveniences -/

lemma psd_form_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef) (x : n → ℝ) :
    0 ≤ x ⬝ᵥ M *ᵥ x := by
  simpa using hM.dotProduct_mulVec_nonneg x

lemma pd_form_pos {M : Matrix n n ℝ} (hM : M.PosDef) {x : n → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ M *ᵥ x := by
  simpa using hM.dotProduct_mulVec_pos hx

lemma psd_of_form {M : Matrix n n ℝ} (h1 : M.IsHermitian) (h2 : ∀ x, 0 ≤ x ⬝ᵥ M *ᵥ x) :
    M.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg h1 (fun x => by simpa using h2 x)

lemma pd_of_form {M : Matrix n n ℝ} (h1 : M.IsHermitian)
    (h2 : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) : M.PosDef :=
  PosDef.of_dotProduct_mulVec_pos h1 (fun x hx => by simpa using h2 x hx)

lemma psd_mulVec_eq_zero [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosSemidef) {x : n → ℝ}
    (h : x ⬝ᵥ M *ᵥ x = 0) : M *ᵥ x = 0 :=
  (hM.dotProduct_mulVec_zero_iff x).mp (by simpa using h)

omit [Fintype n] in
/-- A real Hermitian matrix is symmetric. -/
lemma transpose_eq_of_isHermitian {M : Matrix n n ℝ} (h : M.IsHermitian) : Mᵀ = M := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact h.eq

/-- Symmetric real matrices can be moved across the dot product. -/
lemma dotProduct_mulVec_symm {M : Matrix n n ℝ} (h : Mᵀ = M) (w z : n → ℝ) :
    w ⬝ᵥ M *ᵥ z = (M *ᵥ w) ⬝ᵥ z := by
  rw [dotProduct_mulVec, ← mulVec_transpose, h]

/-! ### From the reconstruction identity to a semidefinite layer -/

/-- `K ≥ 0` and `Q > 0` give `Q⁻¹ K Q⁻¹ ≥ 0`: the reconstruction `S = Q⁻¹ K Q⁻¹` inherits the
sign of the complete cochain form. -/
theorem posSemidef_inv_conj [DecidableEq n] {Q K : Matrix n n ℝ} (hQ : Q.PosDef)
    (hK : K.PosSemidef) : (Q⁻¹ * K * Q⁻¹).PosSemidef := by
  have h := hK.conjTranspose_mul_mul_same Q⁻¹
  have hs : Q⁻¹ᴴ = Q⁻¹ := by rw [conjTranspose_nonsing_inv, hQ.1.eq]
  rwa [hs] at h

/-- Semidefinite and nondegenerate is definite. -/
theorem posDef_of_posSemidef_isUnit [DecidableEq n] {S : Matrix n n ℝ} (hS : S.PosSemidef) (hu : IsUnit S) :
    S.PosDef :=
  hS.posDef_iff_isUnit.mpr hu

/-! ### Kernel descent through the null identity -/

/-- **Kernel descent.**  If `S ≥ 0` solves `S Q S - a S = P` with `P > 0`, then `S > 0`:
a radical vector `v` of `S` has `S v = 0`, hence `vᵀ P v = 0`, contradicting `P > 0`.
In the campaign, `P = Σ A_iᵀ S_{N-i} A_i`, so this is the statement that every positive mode
kills a radical vector. -/
theorem posDef_of_riccati_posDef [DecidableEq n] {S Q P : Matrix n n ℝ} {a : ℝ} (hS : S.PosSemidef)
    (hP : P.PosDef) (hR : S * Q * S - a • S = P) : S.PosDef := by
  refine pd_of_form hS.1 (fun x hx => ?_)
  rcases (psd_form_nonneg hS x).lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 : S *ᵥ x = 0 := psd_mulVec_eq_zero hS h.symm
    have hPx : P *ᵥ x = 0 := by
      rw [← hR, sub_mulVec, smul_mulVec, h0, smul_zero, sub_zero,
        ← mulVec_mulVec, h0, mulVec_zero]
    have := pd_form_pos hP hx
    rw [hPx, dotProduct_zero] at this
    exact lt_irrefl _ this

/-- The lower-weight source `Σ A_iᵀ S_i A_i` is positive definite when each `S_i` is and the
lowering maps have trivial joint kernel. -/
theorem posDef_sum_transpose_mul_mul {ι : Type*} [Fintype ι] {m : ι → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (S : ∀ i, Matrix (m i) (m i) ℝ) (A : ∀ i, Matrix (m i) n ℝ)
    (hS : ∀ i, (S i).PosDef) (hjk : ∀ v : n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0) :
    (∑ i, (A i)ᵀ * S i * A i).PosDef := by
  have hterm : ∀ i (x : n → ℝ), x ⬝ᵥ ((A i)ᵀ * S i * A i) *ᵥ x
      = (A i *ᵥ x) ⬝ᵥ S i *ᵥ (A i *ᵥ x) := by
    intro i x
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x (A i)ᵀ, vecMul_transpose]
  refine pd_of_form ?_ (fun x hx => ?_)
  · unfold IsHermitian
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [conjTranspose_mul, conjTranspose_mul, (hS i).1.eq,
      conjTranspose_eq_transpose_of_trivial, conjTranspose_eq_transpose_of_trivial,
      transpose_transpose, Matrix.mul_assoc]
  · rw [sum_mulVec, dotProduct_sum]
    obtain ⟨i, hi⟩ : ∃ i, A i *ᵥ x ≠ 0 := by
      by_contra hcon
      exact hx (hjk x (fun i => by_contra fun h => hcon ⟨i, h⟩))
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rw [hterm]; exact psd_form_nonneg (hS j).posSemidef _
    · rw [hterm]; exact pd_form_pos (hS i) hi

/-! ### The Riccati gap: positive solutions carry the margin `a Q⁻¹` -/

/-- **Gap lemma (square-root free).**  If `S > 0`, `Q > 0`, `P ≥ 0`, `a > 0` and
`S Q S - a S = P`, then `S ≥ a Q⁻¹`.

Proof.  For any `x` put `y = Q⁻¹ x` and `w = a S⁻¹ y`, so `S w = a y`.  Completing the square
in `S` gives `xᵀ S x ≥ 2 xᵀ S w - wᵀ S w = 2a xᵀ y - wᵀ S w`, and the Riccati identity at `w`
gives `a wᵀ S w ≤ (S w)ᵀ Q (S w) = a² yᵀ Q y = a² xᵀ y`.  Hence `xᵀ S x ≥ a xᵀ Q⁻¹ x`.

Consequently, under positivity at lower weights, the cochain inequality `K = Q S Q ≥ 0` is
equivalent to `K ≥ a Q`: there is no positive Riccati solution with a whitened eigenvalue in
`(0, a)`. -/
theorem riccati_margin [DecidableEq n] {S Q P : Matrix n n ℝ} {a : ℝ} (ha : 0 < a) (hS : S.PosDef)
    (hQ : Q.PosDef) (hP : P.PosSemidef) (hR : S * Q * S - a • S = P) :
    (S - a • Q⁻¹).PosSemidef := by
  have hQi : Q⁻¹.PosDef := hQ.inv
  have hSt : Sᵀ = S := transpose_eq_of_isHermitian hS.1
  have hSdet : IsUnit S.det := (isUnit_iff_isUnit_det S).mp hS.isUnit
  have hQdet : IsUnit Q.det := (isUnit_iff_isUnit_det Q).mp hQ.isUnit
  refine psd_of_form ?_ (fun x => ?_)
  · unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, hS.1.eq, hQi.1.eq, star_trivial]
  · set y : n → ℝ := Q⁻¹ *ᵥ x with hy
    set w : n → ℝ := a • (S⁻¹ *ᵥ y) with hw
    have hSw : S *ᵥ w = a • y := by
      rw [hw, mulVec_smul, mulVec_mulVec, mul_nonsing_inv S hSdet, one_mulVec]
    have hQy : Q *ᵥ y = x := by
      rw [hy, mulVec_mulVec, mul_nonsing_inv Q hQdet, one_mulVec]
    -- completing the square in `S`
    have h1 : 0 ≤ (x - w) ⬝ᵥ S *ᵥ (x - w) := psd_form_nonneg hS.posSemidef _
    have h1' : (x - w) ⬝ᵥ S *ᵥ (x - w)
        = x ⬝ᵥ S *ᵥ x - 2 * (a * (x ⬝ᵥ y)) + w ⬝ᵥ S *ᵥ w := by
      rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hSw,
        dotProduct_smul, dotProduct_mulVec_symm hSt w x, hSw, smul_dotProduct,
        dotProduct_comm y x]
      simp only [smul_eq_mul]; ring
    -- the Riccati identity evaluated at `w`
    have h2 : 0 ≤ w ⬝ᵥ P *ᵥ w := psd_form_nonneg hP w
    have h2' : w ⬝ᵥ P *ᵥ w = a * (a * (x ⬝ᵥ y)) - a * (w ⬝ᵥ S *ᵥ w) := by
      rw [← hR, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
        ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec_symm hSt w, hSw, mulVec_smul,
        dotProduct_smul, smul_dotProduct, hQy, dotProduct_comm y x]
      simp only [smul_eq_mul]
    -- assemble
    have hQinvx : x ⬝ᵥ (S - a • Q⁻¹) *ᵥ x = x ⬝ᵥ S *ᵥ x - a * (x ⬝ᵥ y) := by
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, hy, smul_eq_mul]
    rw [hQinvx]
    have h3 : a * (w ⬝ᵥ S *ᵥ w) ≤ a * (a * (x ⬝ᵥ y)) := by linarith [h2, h2']
    have h4 : w ⬝ᵥ S *ᵥ w ≤ a * (x ⬝ᵥ y) := le_of_mul_le_mul_left h3 ha
    linarith [h1, h1', h4]

/-! ### The `P`-whitened dichotomy: the matrix step of the Bochner reduction -/

open scoped MatrixOrder in
/-- **Bochner-reduction matrix lemma.**  Let `S` be symmetric and invertible, `Q, P > 0`,
`a > 0`, with the Riccati identity `S Q S - a S = P`.  If `S⁻¹ + a P⁻¹ ≥ 0`, then `S > 0`.

Proof.  With `T = S⁻¹` the Riccati identity reads `T P T + a T = Q`.  Whitening by the
positive square root `C` of `P` (so `C C = P`), `Z = C T C` is symmetric with
`Z² + a Z = C Q C > 0` and `Z + a = C (T + a P⁻¹) C ≥ 0`.  Every eigenvalue `λ` of `Z` then
satisfies `λ ≥ -a` and `λ (λ + a) > 0`, hence `λ > 0`; so `Z > 0`, `T = C⁻¹ Z C⁻¹ > 0`, `S > 0`.

In the campaign this is the step "`𝔅(d₀w) ≥ 0` on exact cochains implies graded unitarity":
the Bochner identity supplies exactly the lower bound `S⁻¹ + a_N P⁻¹ ≥ 0`
(the Riccati reformulation of the gap margin). -/
theorem posDef_of_inv_lower_bound [DecidableEq n] {S Q P : Matrix n n ℝ} {a : ℝ} (ha : 0 < a)
    (hS : S.IsHermitian) (hSu : IsUnit S) (hQ : Q.PosDef) (hP : P.PosDef)
    (hR : S * Q * S - a • S = P) (hlow : (S⁻¹ + a • P⁻¹).PosSemidef) : S.PosDef := by
  have hSdet : IsUnit S.det := (isUnit_iff_isUnit_det S).mp hSu
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP.isUnit
  set T : Matrix n n ℝ := S⁻¹ with hTdef
  have hTS : T * S = 1 := nonsing_inv_mul S hSdet
  have hST : S * T = 1 := mul_nonsing_inv S hSdet
  have hTh : T.IsHermitian := by
    unfold IsHermitian; rw [hTdef, conjTranspose_nonsing_inv, hS.eq]
  -- the Riccati identity for `T = S⁻¹`
  have hTR : T * P * T + a • T = Q := by
    have h1 : T * (S * Q * S - a • S) * T = T * P * T := by rw [hR]
    have h2 : T * (S * Q * S - a • S) * T = Q - a • T := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [show T * (S * Q * S) * T = (T * S) * Q * (S * T) by
            simp only [Matrix.mul_assoc]]
      rw [hTS, hST]
      simp only [Matrix.one_mul, Matrix.mul_one]
    rw [← h1, h2, sub_add_cancel]
  -- the positive square root of `P`
  set C : Matrix n n ℝ := CFC.sqrt P with hCdef
  have hC0 : C.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hCC : C * C = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hCh : C.IsHermitian := hC0.1
  have hCdet : IsUnit C.det := by
    have : C.det * C.det = P.det := by rw [← det_mul, hCC]
    rw [isUnit_iff_ne_zero]
    intro h0
    have : P.det = 0 := by rw [← this, h0, zero_mul]
    exact (isUnit_iff_ne_zero.mp hPdet) this
  have hCu : IsUnit C := (isUnit_iff_isUnit_det C).mpr hCdet
  have hCinv : C * C⁻¹ = 1 := mul_nonsing_inv C hCdet
  have hinvC : C⁻¹ * C = 1 := nonsing_inv_mul C hCdet
  have hCPC : C * P⁻¹ * C = 1 := by
    rw [← hCC, Matrix.mul_inv_rev, show C * (C⁻¹ * C⁻¹) * C = (C * C⁻¹) * (C⁻¹ * C) by
          simp only [Matrix.mul_assoc], hCinv, hinvC, Matrix.one_mul]
  -- the whitened operator
  set Z : Matrix n n ℝ := C * T * C with hZdef
  have hZh : Z.IsHermitian := by
    unfold IsHermitian
    rw [hZdef, conjTranspose_mul, conjTranspose_mul, hCh.eq, hTh.eq, Matrix.mul_assoc]
  have hZ2 : Z * Z + a • Z = C * Q * C := by
    rw [← hTR, hZdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← hCC]
    simp only [Matrix.mul_assoc]
  have hZ1 : Z + a • (1 : Matrix n n ℝ) = C * (T + a • P⁻¹) * C := by
    rw [hZdef, Matrix.mul_add, Matrix.add_mul]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul, hCPC]
  have hZ2pd : (Z * Z + a • Z).PosDef := by
    rw [hZ2]
    have := hQ.conjTranspose_mul_mul_same (B := C) (mulVec_injective_of_isUnit hCu)
    rwa [hCh.eq] at this
  have hZ1psd : (Z + a • (1 : Matrix n n ℝ)).PosSemidef := by
    rw [hZ1]
    have := hlow.conjTranspose_mul_mul_same C
    rwa [hCh.eq] at this
  -- eigenvalue argument
  have hZpd : Z.PosDef := by
    rw [hZh.posDef_iff_eigenvalues_pos]
    intro i
    set lam := hZh.eigenvalues i with hlam
    set v : n → ℝ := ⇑(hZh.eigenvectorBasis i) with hv
    have hZv : Z *ᵥ v = lam • v := hZh.mulVec_eigenvectorBasis i
    have hv0 : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 <| hZh.eigenvectorBasis.orthonormal.ne_zero i
    have hvv : 0 < v ⬝ᵥ v := by
      rcases (dotProduct_self_star_nonneg v).lt_or_eq with h | h
      · simpa using h
      · exfalso; exact hv0 ((dotProduct_star_self_eq_zero (v := v)).mp (by simpa using h.symm))
    have e1 : v ⬝ᵥ (Z + a • (1 : Matrix n n ℝ)) *ᵥ v = (lam + a) * (v ⬝ᵥ v) := by
      rw [add_mulVec, smul_mulVec, one_mulVec, hZv]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
    have e2 : v ⬝ᵥ (Z * Z + a • Z) *ᵥ v = (lam * lam + a * lam) * (v ⬝ᵥ v) := by
      rw [add_mulVec, smul_mulVec, ← mulVec_mulVec, hZv, mulVec_smul, hZv]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; ring
    have h1 : 0 ≤ (lam + a) * (v ⬝ᵥ v) := by rw [← e1]; exact psd_form_nonneg hZ1psd v
    have h2 : 0 < (lam * lam + a * lam) * (v ⬝ᵥ v) := by rw [← e2]; exact pd_form_pos hZ2pd hv0
    have h1' : 0 ≤ lam + a := nonneg_of_mul_nonneg_left h1 hvv
    have h2' : 0 < lam * lam + a * lam := pos_of_mul_pos_left h2 hvv.le
    by_contra hneg
    have hneg' : lam ≤ 0 := not_lt.mp hneg
    have e3 : lam * lam + a * lam = lam * (lam + a) := by ring
    have : lam * (lam + a) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg' h1'
    linarith
  -- back to `S`
  have hT : T = C⁻¹ * Z * C⁻¹ := by
    rw [hZdef, show C⁻¹ * (C * T * C) * C⁻¹ = (C⁻¹ * C) * T * (C * C⁻¹) by
          simp only [Matrix.mul_assoc], hinvC, hCinv, Matrix.one_mul, Matrix.mul_one]
  have hTpd : T.PosDef := by
    rw [hT]
    have hCiu : IsUnit C⁻¹ := (isUnit_nonsing_inv_iff).mpr hCu
    have := hZpd.conjTranspose_mul_mul_same (B := C⁻¹) (mulVec_injective_of_isUnit hCiu)
    have hCih : C⁻¹ᴴ = C⁻¹ := by rw [conjTranspose_nonsing_inv, hCh.eq]
    rwa [hCih] at this
  have : S = T⁻¹ := by rw [hTdef, nonsing_inv_nonsing_inv S hSdet]
  rw [this]; exact hTpd.inv

/-! ### The abstract weight tower -/

section Tower

variable {ι : ℕ → Type*} [∀ N, Fintype (ι N)] [∀ N, DecidableEq (ι N)]

/-- The lower-weight source `P_N = Σ_{i<N} A_{N,i}ᵀ S_i A_{N,i}`; `A_{N,i}` lowers weight `N` to
weight `i`. -/
def towerSource (S : ∀ N, Matrix (ι N) (ι N) ℝ)
    (A : ∀ N, (i : Fin N) → Matrix (ι i) (ι N) ℝ) (N : ℕ) : Matrix (ι N) (ι N) ℝ :=
  ∑ i : Fin N, (A N i)ᵀ * S i * A N i

/-- **Abstract length-induction step.**  Suppose that at every weight `N` the preceding-length
Gram `Q N` is positive definite, the reconstructed complete cochain form `K N` is positive
semidefinite, the layer form is reconstructed as `S N = Q N⁻¹ K N Q N⁻¹`, the null identity
`S N Q N S N - a N • S N = P N` holds with `a N > 0`, and at each weight either the layer is
nondegenerate or the lowering maps have trivial joint kernel.  Then every layer form is positive
definite, with the Riccati margin `S N ≥ a N • Q N⁻¹`. -/
theorem tower_posDef (Q S K : ∀ N, Matrix (ι N) (ι N) ℝ) (a : ℕ → ℝ)
    (A : ∀ N, (i : Fin N) → Matrix (ι i) (ι N) ℝ)
    (hQ : ∀ N, (Q N).PosDef) (hK : ∀ N, (K N).PosSemidef)
    (hrec : ∀ N, S N = (Q N)⁻¹ * K N * (Q N)⁻¹)
    (hric : ∀ N, S N * Q N * S N - a N • S N = towerSource S A N)
    (ha : ∀ N, 0 < a N)
    (hker : ∀ N, IsUnit (S N) ∨ ∀ v : ι N → ℝ, (∀ i : Fin N, A N i *ᵥ v = 0) → v = 0) :
    ∀ N, (S N).PosDef ∧ (S N - a N • (Q N)⁻¹).PosSemidef := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hpsd : (S N).PosSemidef := by rw [hrec N]; exact posSemidef_inv_conj (hQ N) (hK N)
    have hP : (towerSource S A N).PosSemidef := by
      unfold towerSource
      refine posSemidef_sum Finset.univ (fun i _ => ?_)
      have := ((ih i i.2).1.posSemidef).conjTranspose_mul_mul_same (A N i)
      simpa [conjTranspose_eq_transpose_of_trivial] using this
    have hpd : (S N).PosDef := by
      rcases hker N with hu | hjk
      · exact posDef_of_posSemidef_isUnit hpsd hu
      · have hPd : (towerSource S A N).PosDef :=
          posDef_sum_transpose_mul_mul (fun i : Fin N => S i) (A N)
            (fun i => (ih i i.2).1) hjk
        exact posDef_of_riccati_posDef hpsd hPd (hric N)
    exact ⟨hpd, riccati_margin (ha N) hpd (hQ N) hP (hric N)⟩

end Tower

end VOA.LeeYangRiccati
