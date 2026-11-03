/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.LogarithmicPseudoTraceBlock

/-!
# Logarithmic pseudo-trace recursion: the polynomial derivative bridge

A logarithmic coefficient at exponent `e` is a polynomial `P_e(τ)`.  Thus the normalized
operator `q d/dq = (2πi)⁻¹ d/dτ` acts by

`P_e ↦ e P_e + (2πi)⁻¹ P_e'`.

The second summand must not be discarded by evaluating at a fixed value of `τ`.  This file
defines the polynomial-valued operator, proves its finite pseudo-trace exponential calculus, and
identifies insertion of the conformal-vector zero mode with the logarithmic derivative plus the
usual `c/24` term.

The only remaining genus-one input is bundled as `LogPseudoTraceRecursionData`: the exact Zhu
`[-1]` recursion with the actual two-zero-mode pseudo-trace.  From that single cross-weight
identity, the already-proved translation law gives the `[-2]` relation and conformal-vector
specialization gives the logarithmic omega relation.  No fixed-`τ` ordinary formal block,
existence from strong finiteness, convergence, spanning, or modularity is asserted.
-/

namespace VOA

open Module (End)
open scoped BigOperators

set_option autoImplicit false

universe u v w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]
variable {A : Type w} [Ring A] [Algebra ℂ A]
variable {N : LogVModule W M}
variable [∀ α : ℂ, Module A (N.weight α)]
variable [∀ α : ℂ, IsScalarTower ℂ A (N.weight α)]

/-! ## Polynomial-valued logarithmic `q`-calculus -/

/-- The normalization constant `2πi` relating `d/dτ` and `q d/dq`. -/
noncomputable def logDerivativeScale : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem logDerivativeScale_ne_zero : logDerivativeScale ≠ 0 := by
  simp [logDerivativeScale, Real.pi_ne_zero, Complex.I_ne_zero]

/-- The honest Euler derivative on polynomial-valued logarithmic q-series. -/
noncomputable def logQDeriv (χ : LogFormalQSeries) : LogFormalQSeries :=
  fun e => e • χ e + (logDerivativeScale)⁻¹ • (χ e).derivative

@[simp] theorem logQDeriv_zero : logQDeriv (0 : LogFormalQSeries) = 0 := by
  funext e
  simp [logQDeriv]

theorem logQDeriv_add (χ ψ : LogFormalQSeries) :
    logQDeriv (χ + ψ) = logQDeriv χ + logQDeriv ψ := by
  funext e
  simp only [logQDeriv, Pi.add_apply, Polynomial.derivative_add]
  module

theorem logQDeriv_smul (c : ℂ) (χ : LogFormalQSeries) :
    logQDeriv (c • χ) = c • logQDeriv χ := by
  funext e
  simp only [logQDeriv, Pi.smul_apply, Polynomial.derivative_smul]
  module

/-- Evaluation records both contributions: exponent differentiation and polynomial
differentiation. -/
theorem logQDeriv_eval (χ : LogFormalQSeries) (e τ : ℂ) :
    (logQDeriv χ e).eval τ =
      e * (χ e).eval τ + (logDerivativeScale)⁻¹ * (χ e).derivative.eval τ := by
  simp [logQDeriv]

/-- Cauchy action of an ordinary natural-exponent q-series on a logarithmic q-series. -/
noncomputable def logQConv (f : ℕ → ℂ) (χ : LogFormalQSeries) : LogFormalQSeries :=
  fun e => ∑ᶠ n : ℕ, f n • χ (e - (n : ℂ))

@[simp] theorem logQConv_zero_right (f : ℕ → ℂ) :
    logQConv f (0 : LogFormalQSeries) = 0 := by
  funext e
  simp [logQConv]

@[simp] theorem logQConv_zero_left (χ : LogFormalQSeries) :
    logQConv 0 χ = 0 := by
  funext e
  simp [logQConv]

/-- The logarithmic convolution is homogeneous in the coefficient-valued argument. -/
theorem logQConv_smul_right (f : ℕ → ℂ) (c : ℂ) (χ : LogFormalQSeries) :
    logQConv f (c • χ) = c • logQConv f χ := by
  funext e
  simp only [logQConv, Pi.smul_apply, smul_smul]
  rw [smul_finsum]
  apply finsum_congr
  intro n
  simp only [smul_smul]
  congr 1
  ring

/-! ## Finite pseudo-trace exponential differentiation -/

theorem logExpCoeff_succ (k : ℕ) :
    (logDerivativeScale)⁻¹ * (k + 1 : ℂ) * logExpCoeff (k + 1) = logExpCoeff k := by
  have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [logExpCoeff, logExpCoeff, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp [logDerivativeScale_ne_zero, hk]
  simp [logDerivativeScale, mul_comm]

section OnePiece

variable {P : Type*} [AddCommGroup P] [Module A P] [Module ℂ P]
variable [IsScalarTower ℂ A P] [Module.Finite A P] [Module.Projective A P]

/-- The finite exponential polynomial is additive in its insertion. -/
theorem pseudoTraceExpPolynomial_add (phi : symmetricFunctionals ℂ A)
    (S T R : Module.End A P) (r : ℕ) :
    pseudoTraceExpPolynomial P phi (S + T) R r =
      pseudoTraceExpPolynomial P phi S R r + pseudoTraceExpPolynomial P phi T R r := by
  ext k
  rw [pseudoTraceExpPolynomial_coeff, Polynomial.coeff_add,
    pseudoTraceExpPolynomial_coeff, pseudoTraceExpPolynomial_coeff]
  by_cases hk : k < r
  · rw [if_pos hk, if_pos hk, if_pos hk, add_mul, map_add, mul_add]
  · rw [if_neg hk, if_neg hk, if_neg hk, add_zero]

/-- The finite exponential polynomial is homogeneous in its insertion. -/
theorem pseudoTraceExpPolynomial_smul (phi : symmetricFunctionals ℂ A)
    (c : ℂ) (S R : Module.End A P) (r : ℕ) :
    pseudoTraceExpPolynomial P phi (c • S) R r =
      c • pseudoTraceExpPolynomial P phi S R r := by
  ext k
  rw [pseudoTraceExpPolynomial_coeff, Polynomial.coeff_smul,
    pseudoTraceExpPolynomial_coeff]
  by_cases hk : k < r
  · rw [if_pos hk, if_pos hk, smul_mul_assoc, map_smul]
    simp [smul_eq_mul, mul_left_comm]
  · rw [if_neg hk, if_neg hk]
    simp

/-- Cyclicity moves one left nilpotent factor to the right of the insertion polynomial. -/
theorem pseudoTraceExpPolynomial_nilpotent_cyclic (phi : symmetricFunctionals ℂ A)
    (S R : Module.End A P) (r : ℕ) :
    pseudoTraceExpPolynomial P phi (R * S) R r =
      pseudoTraceExpPolynomial P phi (S * R) R r := by
  ext k
  rw [pseudoTraceExpPolynomial_coeff, pseudoTraceExpPolynomial_coeff]
  by_cases hk : k < r
  · rw [if_pos hk, if_pos hk]
    congr 1
    rw [mul_assoc]
    have hcyc := pseudoTrace_mem_symmetricFunctionals (W := P) phi
    calc
      pseudoTrace P phi ((R * S) * R ^ k)
          = pseudoTrace P phi (R * (S * R ^ k)) := by rw [mul_assoc]
      _ = pseudoTrace P phi ((S * R ^ k) * R) := hcyc R (S * R ^ k)
      _ = pseudoTrace P phi ((S * R) * R ^ k) := by
        rw [mul_assoc, mul_assoc, ← pow_succ', ← pow_succ]
  · rw [if_neg hk, if_neg hk]

/-- Differentiating the truncated nilpotent exponential inserts one nilpotent factor. -/
theorem pseudoTraceExpPolynomial_derivative (phi : symmetricFunctionals ℂ A)
    (S R : Module.End A P) (r : ℕ) (hR : R ^ r = 0) :
    (logDerivativeScale)⁻¹ • (pseudoTraceExpPolynomial P phi S R r).derivative =
      pseudoTraceExpPolynomial P phi (S * R) R r := by
  ext k
  rw [Polynomial.coeff_smul, Polynomial.coeff_derivative,
    pseudoTraceExpPolynomial_coeff, pseudoTraceExpPolynomial_coeff]
  by_cases hk : k < r
  · rw [if_pos hk]
    by_cases hks : k + 1 < r
    · rw [if_pos hks]
      have hpow : S * R * R ^ k = S * R ^ (k + 1) := by
        rw [mul_assoc, ← pow_succ']
      rw [hpow]
      simp only [smul_eq_mul]
      calc
        (logDerivativeScale)⁻¹ *
            (logExpCoeff (k + 1) * pseudoTrace P phi (S * R ^ (k + 1)) *
              (k + 1 : ℂ)) =
            ((logDerivativeScale)⁻¹ * (k + 1 : ℂ) * logExpCoeff (k + 1)) *
              pseudoTrace P phi (S * R ^ (k + 1)) := by ring
        _ = logExpCoeff k * pseudoTrace P phi (S * R ^ (k + 1)) := by
          rw [logExpCoeff_succ]
    · have hkr : k + 1 = r := by omega
      rw [if_neg hks, zero_mul, smul_zero]
      subst r
      rw [mul_assoc, ← pow_succ', hR, mul_zero, map_zero, mul_zero]
  · have hks : ¬ k + 1 < r := by omega
    rw [if_neg hk, if_neg hks, zero_mul, smul_zero]

/-- Inserting `R + α` on the left gives the scalar-weight term plus the normalized polynomial
derivative.  Hattori--Stallings cyclicity is what moves the left `R` past the insertion. -/
theorem pseudoTraceExpPolynomial_affine_nilpotent (phi : symmetricFunctionals ℂ A)
    (S R : Module.End A P) (α : ℂ) (r : ℕ) (hR : R ^ r = 0) :
    pseudoTraceExpPolynomial P phi ((R + α • 1) * S) R r =
      α • pseudoTraceExpPolynomial P phi S R r +
        (logDerivativeScale)⁻¹ • (pseudoTraceExpPolynomial P phi S R r).derivative := by
  have hmul : (R + α • (1 : Module.End A P)) * S = R * S + α • S := by
    rw [add_mul, smul_mul_assoc, one_mul]
  rw [hmul, pseudoTraceExpPolynomial_add,
    pseudoTraceExpPolynomial_nilpotent_cyclic,
    pseudoTraceExpPolynomial_smul,
    pseudoTraceExpPolynomial_derivative phi S R r hR]
  abel

end OnePiece

/-! ## The actual two-zero-mode pseudo-trace and the omega insertion -/

namespace LogPseudoTraceCommutantData

/-- Polynomial-valued pseudo-trace with two lifted zero modes, in the order in which they occur
in Zhu's recursion. -/
noncomputable def logPseudoTraceTwoPoint
    (D : LogPseudoTraceCommutantData N A) (a b : 𝒱) : LogFormalQSeries :=
  fun e =>
    let α := e + W.centralCharge / 24
    letI : Module.Finite A (N.weight α) := D.finite_piece α
    letI : Module.Projective A (N.weight α) := D.projective_piece α
    pseudoTraceExpPolynomial (N.weight α) D.phi
      (D.zeroModeA α a * D.zeroModeA α b)
      (D.nilpotentPiece α) (D.nilpotentCutoff α)

theorem logPseudoTraceTwoPoint_coeff
    (D : LogPseudoTraceCommutantData N A) (a b : 𝒱) (e : ℂ) (k : ℕ) :
    let α := e + W.centralCharge / 24
    letI : Module.Finite A (N.weight α) := D.finite_piece α
    letI : Module.Projective A (N.weight α) := D.projective_piece α
    (D.logPseudoTraceTwoPoint a b e).coeff k =
      if k < D.nilpotentCutoff α then
        logExpCoeff k * pseudoTrace (N.weight α) D.phi
          ((D.zeroModeA α a * D.zeroModeA α b) * (D.nilpotentPiece α) ^ k)
      else 0 := by
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  exact pseudoTraceExpPolynomial_coeff (N.weight α) D.phi
    (D.zeroModeA α a * D.zeroModeA α b)
    (D.nilpotentPiece α) (D.nilpotentCutoff α) k

/-- A vanishing lifted second zero mode kills the two-point polynomial. -/
theorem logPseudoTraceTwoPoint_eq_zero_of_zeroModeA_right
    (D : LogPseudoTraceCommutantData N A) (a : 𝒱) {b : 𝒱}
    (hb : ∀ α : ℂ, D.zeroModeA α b = 0) :
    D.logPseudoTraceTwoPoint a b = 0 := by
  funext e
  apply Polynomial.ext
  intro k
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  rw [D.logPseudoTraceTwoPoint_coeff]
  by_cases hk : k < D.nilpotentCutoff α
  · rw [if_pos hk, hb α, mul_zero, zero_mul, map_zero, mul_zero]
    rfl
  · rw [if_neg hk]
    rfl

/-- The actual two-point pseudo-trace vanishes when its right insertion is Zhu translation. -/
theorem logPseudoTraceTwoPoint_Lsq_neg_one_right
    (D : LogPseudoTraceCommutantData N A) (a b : 𝒱) :
    D.logPseudoTraceTwoPoint a (Lsq W (-1) b) = 0 := by
  apply D.logPseudoTraceTwoPoint_eq_zero_of_zeroModeA_right a
  intro α
  rw [Lsq_neg_one]
  exact D.zeroModeA_L_translation_all α b

/-- Insertion of `o(ω)=L₀` is exactly the logarithmic Euler derivative plus the `c/24` shift.
The polynomial-derivative term is essential. -/
theorem logPseudoTraceTwoPoint_conformalVector
    (D : LogPseudoTraceCommutantData N A) (v : 𝒱) :
    D.logPseudoTraceTwoPoint W.conformalVector v =
      logQDeriv (D.logPseudoTraceOnePoint v) +
        (W.centralCharge / 24) • D.logPseudoTraceOnePoint v := by
  funext e
  let α := e + W.centralCharge / 24
  letI : Module.Finite A (N.weight α) := D.finite_piece α
  letI : Module.Projective A (N.weight α) := D.projective_piece α
  have homega : D.zeroModeA α W.conformalVector =
      D.nilpotentPiece α + α • (1 : Module.End A (N.weight α)) := by
    rw [nilpotentPiece]
    module
  change pseudoTraceExpPolynomial (N.weight α) D.phi
      (D.zeroModeA α W.conformalVector * D.zeroModeA α v)
      (D.nilpotentPiece α) (D.nilpotentCutoff α) = _
  rw [homega, pseudoTraceExpPolynomial_affine_nilpotent D.phi
    (D.zeroModeA α v) (D.nilpotentPiece α) α (D.nilpotentCutoff α)
    (D.nilpotentPiece_pow_cutoff α)]
  change α • D.logPseudoTraceOnePoint v e +
      (logDerivativeScale)⁻¹ • (D.logPseudoTraceOnePoint v e).derivative =
    (e • D.logPseudoTraceOnePoint v e +
      (logDerivativeScale)⁻¹ • (D.logPseudoTraceOnePoint v e).derivative) +
      (W.centralCharge / 24) • D.logPseudoTraceOnePoint v e
  dsimp only [α]
  module

end LogPseudoTraceCommutantData

/-! ## The exact cross-weight residual and logarithmic formal blocks -/

/-- The one missing cross-weight input: Zhu's `a[-1]` recursion for the actual logarithmic
pseudo-trace.  Support finiteness of the outer `finsum` follows independently from VOA
regularity, exactly as in the ordinary recursion; this structure asserts only the identity.

No `[-2]`, omega, convergence, spanning, or modularity field is included. -/
structure LogPseudoTraceRecursionData (D : LogPseudoTraceCommutantData N A) : Prop where
  zhu : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱,
    D.logPseudoTraceOnePointHom (vSqZ W a ka (-1) v) =
      D.logPseudoTraceTwoPoint a v +
        ∑ᶠ m : ℕ, logQConv (zhuG (m + 1))
          (D.logPseudoTraceOnePointHom
            (vSqZ W a ka (2 * (m + 1) - 1 : ℤ) v))

namespace LogPseudoTraceRecursionData

variable {D : LogPseudoTraceCommutantData N A}

/-- Zhu's logarithmic `[-2]` relation follows from the single cross-weight recursion and the
already-proved `L[-1]` translation identity. -/
theorem negTwo (R : LogPseudoTraceRecursionData (N := N) D)
    {ka : ℕ} (hk : 1 ≤ ka) {a : 𝒱}
    (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) :
    D.logPseudoTraceOnePointHom (vSqZ W a ka (-2) v) +
      ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ) •
        logQConv (zhuG (m + 1))
          (D.logPseudoTraceOnePointHom
            (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v)) = 0 := by
  set x : 𝒱 := Lsq W (-1) v with hx
  have hrec := R.1 ka hk a ha x
  have hL : vSqZ W a ka (-1) x =
      Lsq W (-1) (vSqZ W a ka (-1) v) - vSqZ W a ka (-2) v := by
    have h := Lsq_neg_one_vSqZ_comm hk ha (-1) v
    rw [show (-1 : ℤ) - 1 = -2 from by norm_num,
      show (-((-1 : ℤ) : ℂ)) = 1 from by push_cast; ring, one_smul] at h
    rw [hx, ← h]
    abel
  have htwo : D.logPseudoTraceTwoPoint a x = 0 := by
    rw [hx]
    exact D.logPseudoTraceTwoPoint_Lsq_neg_one_right a v
  have htrans (y : 𝒱) :
      D.logPseudoTraceOnePointHom (Lsq W (-1) y) = 0 :=
    D.logPseudoTraceOnePoint_Lsq_neg_one y
  have hLZ : D.logPseudoTraceOnePointHom (vSqZ W a ka (-1) x) =
      -D.logPseudoTraceOnePointHom (vSqZ W a ka (-2) v) := by
    rw [hL, map_sub, htrans, zero_sub]
  have htail : ∀ m : ℕ,
      D.logPseudoTraceOnePointHom
          (vSqZ W a ka (2 * (m + 1) - 1 : ℤ) x) =
        ((2 * (m + 1) - 1 : ℕ) : ℂ) •
          D.logPseudoTraceOnePointHom
            (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) := by
    intro m
    have h := Lsq_neg_one_vSqZ_comm hk ha (2 * (m + 1) - 1 : ℤ) v
    rw [show (2 * (m + 1) - 1 - 1 : ℤ) = 2 * (m + 1) - 2 from by ring,
      ← hx, sub_eq_iff_eq_add] at h
    have hc : (((2 * (m + 1) - 1 : ℕ) : ℂ)) =
        ((2 * (m + 1) - 1 : ℤ) : ℂ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (m + 1))]
      ring
    have hidx : vSqZ W a ka (2 * (m + 1) - 1 : ℤ) x =
        Lsq W (-1) (vSqZ W a ka (2 * (m + 1) - 1 : ℤ) v) +
          ((2 * (m + 1) - 1 : ℕ) : ℂ) •
            vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v := by
      rw [hc, h, neg_smul]
      abel
    rw [hidx, map_add, map_smul, htrans, zero_add]
  rw [hLZ, htwo, zero_add] at hrec
  simp_rw [htail, logQConv_smul_right] at hrec
  rw [neg_eq_iff_eq_neg] at hrec
  rw [hrec, neg_add_cancel]

/-- The conformal-vector specialization of the same cross-weight recursion gives the correct
logarithmic omega relation. -/
theorem omega (R : LogPseudoTraceRecursionData (N := N) D) (v : 𝒱) :
    D.logPseudoTraceOnePointHom (Lsq W (-2) v) =
      logQDeriv (D.logPseudoTraceOnePointHom v) +
        ∑ᶠ m : ℕ, logQConv (zhuG (m + 1))
          (D.logPseudoTraceOnePointHom
            (Lsq W (2 * (m + 1) - 2 : ℤ) v)) := by
  have hrec := R.1 2 (by norm_num) W.conformalVector
    W.conformalVector_mem_grading_two v
  have hm1 : vSqZ W W.conformalVector 2 (-1) v =
      Lsq W (-2) v + (W.centralCharge / 24) • v := by
    rw [Lsq_apply, show (-2 : ℤ) + 1 = -1 from by norm_num,
      sqBracketCoeffZ_vacuum_neg_one, mul_one, sub_add_cancel]
  have hodd : ∀ m : ℕ,
      vSqZ W W.conformalVector 2 (2 * (m + 1) - 1 : ℤ) v =
        Lsq W (2 * (m + 1) - 2 : ℤ) v := by
    intro m
    rw [Lsq_apply,
      show (2 * (m + 1) - 2 : ℤ) + 1 = 2 * (m + 1) - 1 from by ring,
      sqBracketCoeffZ_vacuum_of_ne _ (by omega), mul_zero, zero_smul, sub_zero]
  rw [hm1, map_add, map_smul, D.logPseudoTraceTwoPoint_conformalVector] at hrec
  simp_rw [hodd] at hrec
  change D.logPseudoTraceOnePointHom (Lsq W (-2) v) +
      (W.centralCharge / 24) • D.logPseudoTraceOnePointHom v =
    logQDeriv (D.logPseudoTraceOnePointHom v) +
      (W.centralCharge / 24) • D.logPseudoTraceOnePointHom v +
        ∑ᶠ m : ℕ, logQConv (zhuG (m + 1))
          (D.logPseudoTraceOnePointHom
            (Lsq W (2 * (m + 1) - 2 : ℤ) v)) at hrec
  funext e
  have h := congrFun hrec e
  simp only [Pi.add_apply, Pi.smul_apply] at h ⊢
  linear_combination h

end LogPseudoTraceRecursionData

/-- Polynomial-valued logarithmic analogue of Zhu's formal-block predicate.  It retains the
cyclic/translation layer and uses `logQDeriv`, never fixed-`τ` evaluation. -/
structure IsLogPseudoTraceFormalBlock
    (S : 𝒱 →ₗ[ℂ] LogFormalQSeries) (character : LogFormalQSeries) : Prop
    extends LogPseudoTraceCommutantData.IsLogPseudoTraceCyclicBlock
      (W := W) S character where
  negTwo : ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱,
    S (vSqZ W a ka (-2) v) +
      ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ) •
        logQConv (zhuG (m + 1))
          (S (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v)) = 0
  omega : ∀ v : 𝒱, S (Lsq W (-2) v) =
    logQDeriv (S v) +
      ∑ᶠ m : ℕ, logQConv (zhuG (m + 1))
        (S (Lsq W (2 * (m + 1) - 2 : ℤ) v))

namespace LogPseudoTraceCommutantData

/-- Operational commutant data plus the exact cross-weight Zhu recursion produce the full
polynomial-valued logarithmic formal-block identities. -/
theorem isLogPseudoTraceFormalBlock
    (D : LogPseudoTraceCommutantData N A) (R : LogPseudoTraceRecursionData (N := N) D) :
    IsLogPseudoTraceFormalBlock (W := W)
      D.logPseudoTraceOnePointHom D.logPseudoCharacter where
  toIsLogPseudoTraceCyclicBlock := D.isLogPseudoTraceCyclicBlock
  negTwo := fun _ hk _ ha v => R.negTwo hk ha v
  omega := R.omega

end LogPseudoTraceCommutantData

end VOA
