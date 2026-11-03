/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuTheorem
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The convergence bridge `FormalQSeries → ℍ`

Everything in the modularity layer up to here is **formal**: a `q`-series is its coefficient
function
(`FormalQSeries = ℂ → ℂ`), and no analysis is involved.  Zhu's Theorem 5.3.8, by contrast, is a
statement about honest functions on the upper half-plane.  The bridge between the two is the item
that keeps `zhu_modularity` conditional, and it is present in neither this repo nor Mathlib.

## What the bridge needs

For a module `M` of conformal weight `h`, the character is `Σ_{n ≥ 0} (dim M_{h+n}) q^{h+n−c/24}`.
Convergence on the whole disc `|q| < 1` — equivalently on all of `ℍ` — is exactly the statement that
the coefficients grow **subexponentially**:

  for every `r > 1` there is `C` with `dim M_{h+n} ≤ C·rⁿ`.

This file builds the bridge **from that hypothesis**:

* `summable_of_subexponential` — subexponential nonnegative coefficients are summable against any
  `‖q‖ < 1` (pure analysis: compare with a geometric series of ratio `r‖q‖ < 1`);
* `qParam`, `norm_qParam_lt_one` — `q = e^{2πiτ}` has `‖q‖ < 1` on `ℍ`;
* `QSummableAt`, `qEvalAt` — the summability predicate and the evaluation map;
* `qSummableAt_of_subexponential` — the bridge itself;
* `SubexponentialCoeffs`, `HasQEval` — the two named data.

## What is *not* here

That a `C₂`-cofinite VOA **has** subexponentially growing graded dimensions is the deep input
(Zhu; Dong–Li–Mason; Buhl): `C₂`-cofiniteness gives an ordered spanning set over a finite generating
set, whence a partition-type count `dim M_{h+n} = O(exp(c√n))`, which is subexponential.  The repo
already proves the hard half of the spanning-set input — 5.3.11a, `C₂`-cofinite ⟹ finitely generated
(`Modules/FiniteGeneration`).  In this file `SubexponentialCoeffs` is carried as a named `Prop`.
It is **supplied downstream** (`Modularity/BuhlSpanningC2.lean`): for the adjoint module by
`subexponentialCoeffs_adjoint_of_C2Cofinite`, and for a module with a finite lowest-weight
generating bottom family by `subexponentialCoeffs_of_C2Cofinite`, via the ordered spanning set and
the coloured-partition bound `pcountLe_subexponential` (`Modularity/GrowthBound.lean`).

## Status
Proved, axiom-clean, `pbw`-free.  The bridge is **built**; its single input
(`C₂`-cofinite ⟹ `SubexponentialCoeffs`) is named, not assumed away.

## References
* Zhu, J. AMS 9 (1996) §4–5; Dong–Li–Mason; Buhl, *A spanning set for VOA modules*; Gannon §5.3.5.
-/

namespace VOA

open scoped BigOperators

/-! ## Subexponential growth implies summability -/

/-- **Subexponential growth**: `a n ≤ C·rⁿ` for every ratio `r > 1` (with `C` allowed to depend on
`r`).  This is exactly what makes a power series converge on the *whole* open unit disc. -/
def Subexponential (a : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, ∀ n : ℕ, a n ≤ C * r ^ n

/-- **Subexponential coefficients are summable against any `‖q‖ < 1`.**

Choose `r` strictly between `1` and `‖q‖⁻¹`; then `aₙ‖q‖ⁿ ≤ C·(r‖q‖)ⁿ` with `r‖q‖ < 1`, and the
geometric series dominates. -/
theorem summable_of_subexponential {a : ℕ → ℝ} (hpos : ∀ n, 0 ≤ a n) (hsub : Subexponential a)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) : Summable (fun n : ℕ => a n * t ^ n) := by
  rcases eq_or_lt_of_le ht0 with hteq | htpos
  · -- `t = 0`: only the `n = 0` term survives
    refine summable_of_ne_finset_zero (s := {0}) (fun n hn => ?_)
    have hn0 : n ≠ 0 := by simpa using hn
    rw [← hteq, zero_pow hn0, mul_zero]
  · -- `t > 0`: compare with a geometric series
    obtain ⟨r, hr1, hrt⟩ : ∃ r : ℝ, 1 < r ∧ r * t < 1 := by
      refine ⟨(1 + t⁻¹) / 2, ?_, ?_⟩
      · have h1 : 1 < t⁻¹ := (one_lt_inv₀ htpos).mpr ht
        linarith
      · have h1 : 1 < t⁻¹ := (one_lt_inv₀ htpos).mpr ht
        have : (1 + t⁻¹) / 2 < t⁻¹ := by linarith
        calc (1 + t⁻¹) / 2 * t < t⁻¹ * t := by
              exact mul_lt_mul_of_pos_right this htpos
          _ = 1 := inv_mul_cancel₀ (ne_of_gt htpos)
    obtain ⟨C, hC⟩ := hsub r hr1
    have hCnn : 0 ≤ C := by
      have := hC 0
      simpa using le_trans (hpos 0) this
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hpos n) (pow_nonneg ht0 n))
      (fun n => ?_) (((summable_geometric_of_lt_one (by positivity) hrt).mul_left C))
    calc a n * t ^ n ≤ (C * r ^ n) * t ^ n :=
          mul_le_mul_of_nonneg_right (hC n) (pow_nonneg ht0 n)
      _ = C * (r * t) ^ n := by rw [mul_pow]; ring

/-! ## Closure properties of `Subexponential`

Enough to recognise the growth bounds that actually occur. -/

/-- Domination: a sequence below a subexponential one is subexponential. -/
theorem Subexponential.of_le {a b : ℕ → ℝ} (hab : ∀ n, a n ≤ b n) (hb : Subexponential b) :
    Subexponential a := fun r hr => by
  obtain ⟨C, hC⟩ := hb r hr
  exact ⟨C, fun n => le_trans (hab n) (hC n)⟩

/-- Constants are subexponential. -/
theorem subexponential_const (c : ℝ) : Subexponential (fun _ => c) := fun r hr =>
  ⟨max c 0, fun n => le_trans (le_max_left c 0)
    (le_mul_of_one_le_right (le_max_right c 0) (one_le_pow₀ hr.le))⟩

/-- A subexponential sequence stays subexponential after scaling by a constant `≥ 0`. -/
theorem Subexponential.const_mul {a : ℕ → ℝ} (ha : Subexponential a) {c : ℝ} (hc : 0 ≤ c) :
    Subexponential (fun n => c * a n) := fun r hr => by
  obtain ⟨C, hC⟩ := ha r hr
  refine ⟨c * C, fun n => ?_⟩
  calc c * a n ≤ c * (C * r ^ n) := by exact mul_le_mul_of_nonneg_left (hC n) hc
    _ = c * C * r ^ n := by ring

/-- **The Dong–Li–Mason growth shape is subexponential**: `exp(c√n)` is dominated by `C·rⁿ` for
every `r > 1`.

This is the bound that `C₂`-cofiniteness produces via the partition count, so this lemma is the
step that converts it into the hypothesis `summable_of_subexponential` consumes.  The constant is
explicit: `c√n − n·log r` is maximised at `√n = c/(2 log r)`, with value `c²/(4 log r)`. -/
theorem subexponential_exp_sqrt (c : ℝ) :
    Subexponential (fun n : ℕ => Real.exp (c * Real.sqrt n)) := by
  intro r hr
  have hL : 0 < Real.log r := Real.log_pos hr
  refine ⟨Real.exp (c ^ 2 / (4 * Real.log r)), fun n => ?_⟩
  have hrpow : (r : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log r) := by
    rw [Real.exp_nat_mul, Real.exp_log (lt_trans zero_lt_one hr)]
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  set s : ℝ := Real.sqrt n with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsn : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  rw [← hsn]
  have hkey : 0 ≤ Real.log r * (s - c / (2 * Real.log r)) ^ 2 := by positivity
  have hexp : Real.log r * (s - c / (2 * Real.log r)) ^ 2
      = Real.log r * s ^ 2 - c * s + c ^ 2 / (4 * Real.log r) := by
    field_simp
    ring
  nlinarith [hkey, hexp]

/-! ## The `q`-parameter on the upper half-plane -/

/-- `q = e^{2πiτ}`, the uniformizing parameter of the cusp. -/
noncomputable def qParam (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ))

/-- `‖q‖ < 1` on the upper half-plane — this is what makes the whole theory converge. -/
theorem norm_qParam_lt_one (τ : UpperHalfPlane) : ‖qParam τ‖ < 1 := by
  rw [qParam, Complex.norm_exp]
  refine Real.exp_lt_one_iff.mpr ?_
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re
      = -(2 * Real.pi * (τ : ℂ).im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hpi : 0 < Real.pi := Real.pi_pos
  have him : 0 < (τ : ℂ).im := τ.im_pos
  nlinarith

theorem norm_qParam_nonneg (τ : UpperHalfPlane) : 0 ≤ ‖qParam τ‖ := norm_nonneg _

/-! ## Summability and evaluation of a formal `q`-series -/

/-- **The `q`-series of `χ` along the progression `h + ℕ` is summable at `τ`.**

A module `q`-series is supported on `h + ℕ` (bounded below with integer spacing), so this is the
right summability predicate: `Σ_n χ(h+n)·qⁿ` converges. -/
def QSummableAt (χ : FormalQSeries) (h : ℂ) (τ : UpperHalfPlane) : Prop :=
  Summable (fun n : ℕ => χ (h + n) * (qParam τ) ^ n)

/-- **The evaluation of a formal `q`-series at `τ`**: `Σ_n χ(h+n) q^{h+n}`.  The overall `q^h`
carries the (possibly non-integral) conformal-weight shift. -/
noncomputable def qEvalAt (χ : FormalQSeries) (h : ℂ) (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * h) *
    ∑' n : ℕ, χ (h + n) * (qParam τ) ^ n

/-- **The bridge**: subexponentially growing coefficients are summable at every `τ ∈ ℍ`.

This is the whole analytic content, isolated: given the growth bound, the character is a genuine
holomorphic-in-the-making function of `τ`, uniformly over the upper half-plane. -/
theorem qSummableAt_of_subexponential (χ : FormalQSeries) (h : ℂ)
    (hsub : Subexponential (fun n : ℕ => ‖χ (h + n)‖)) (τ : UpperHalfPlane) :
    QSummableAt χ h τ := by
  refine Summable.of_norm ?_
  have := summable_of_subexponential (a := fun n : ℕ => ‖χ (h + n)‖)
    (fun n => norm_nonneg _) hsub (norm_qParam_nonneg τ) (norm_qParam_lt_one τ)
  refine this.congr (fun n => ?_)
  rw [norm_mul, norm_pow]

/-! ## `qEvalAt` intertwines the formal `qShift` with `τ ↦ τ + 1`

`qShift` was *defined* formally as `χ e ↦ e^{2πie}·χ e` (`Modules/Rationality`), and
`char_T_transform` is a statement about it.  The theorem below justifies that definition
analytically: under `qEvalAt`, `qShift` really is the substitution `τ ↦ τ+1`.  So the `T`-slice of
Zhu's theorem, which `zhu_modularity_T` proves formally, transports to honest functions on `ℍ`
**unconditionally**: no summability hypothesis is needed, because the identity is termwise. -/

/-- `q = e^{2πiτ}` is invariant under `τ ↦ τ + 1`. -/
theorem qParam_translate {τ τ' : UpperHalfPlane} (hτ : (τ' : ℂ) = (τ : ℂ) + 1) :
    qParam τ' = qParam τ := by
  rw [qParam, qParam, hτ, mul_add, mul_one, Complex.exp_add]
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = ((1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      from by push_cast; ring, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- **The formal `qShift` *is* `τ ↦ τ + 1`.**

`qEvalAt (qShift χ) h τ = qEvalAt χ h (τ+1)`.  Termwise, `q^{h+n}` picks up `e^{2πi(h+n)}` under
`τ ↦ τ+1`, which is exactly the factor `qShift` applies to the coefficient. -/
theorem qEvalAt_translate (χ : FormalQSeries) (h : ℂ) {τ τ' : UpperHalfPlane}
    (hτ : (τ' : ℂ) = (τ : ℂ) + 1) :
    qEvalAt χ h τ' = qEvalAt (qShift χ) h τ := by
  have hq : qParam τ' = qParam τ := qParam_translate hτ
  have hterm : ∀ n : ℕ, qShift χ (h + n) * (qParam τ) ^ n
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * h) * (χ (h + n) * (qParam τ) ^ n) := by
    intro n
    rw [qShift, mul_add, Complex.exp_add,
      show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n : ℂ)
          = ((n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by push_cast; ring,
      Complex.exp_nat_mul_two_pi_mul_I, mul_one]
    ring
  rw [qEvalAt, qEvalAt, hq, tsum_congr hterm, tsum_mul_left, hτ]
  rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) + 1) * h
      = 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * h
        + 2 * (Real.pi : ℂ) * Complex.I * h from by ring, Complex.exp_add]
  ring

/-- Scaling a formal `q`-series scales its evaluation (no summability needed: `tsum_mul_left`). -/
theorem qEvalAt_smul (c : ℂ) (χ : FormalQSeries) (h : ℂ) (τ : UpperHalfPlane) :
    qEvalAt (c • χ) h τ = c * qEvalAt χ h τ := by
  rw [qEvalAt, qEvalAt, show (∑' n : ℕ, (c • χ) (h + n) * qParam τ ^ n)
      = ∑' n : ℕ, c * (χ (h + n) * qParam τ ^ n) from
        tsum_congr (fun n => by simp only [Pi.smul_apply, smul_eq_mul]; ring), tsum_mul_left]
  ring

section
variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Zhu's 5.3.18b at the `T`-generator, ANALYTICALLY and unconditionally.**

`χ_{Mᵢ}(τ+1) = Σ_j ρ(T)_{ij}·χ_{Mⱼ}(τ)` for genuine functions on `ℍ`, with no summability
hypothesis.  Two things make this possible: `qEvalAt_translate` (the formal `qShift` really is
`τ ↦ τ+1`) and the **diagonality** of `ρ(T)`, which collapses the sum to one term so that only
`qEvalAt_smul` — not additivity, which would need convergence — is required.

This is the first slice of Zhu's theorem proved for honest functions rather than formal series. -/
theorem zhu_modularity_T_analytic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : VertexOperatorAlgebra 𝒱} (D : ModularData W ι) (h : ℂ) (i : ι)
    {τ τ' : UpperHalfPlane} (hτ : (τ' : ℂ) = (τ : ℂ) + 1) :
    qEvalAt (gradedDim (D.Mfam i).isMod) h τ'
      = ∑ j : ι, D.rep ModularGroup.T i j * qEvalAt (gradedDim (D.Mfam j).isMod) h τ := by
  rw [qEvalAt_translate _ _ hτ,
    char_T_transform (D.Mfam i).isMod (D.h i) (D.hasWeight i), qEvalAt_smul, D.rep_T,
    Finset.sum_eq_single i
      (fun j _ hj => by
        simp only [Matrix.of_apply]
        rw [modularRepT_off_diag W D.h (Ne.symm hj), zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi)]
  simp only [Matrix.of_apply, modularRepT_diag, modularTEntry]

end

section
variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `ρ(T)` written as a genuine diagonal matrix, so that its powers are computable. -/
theorem modularRepT_eq_diagonal {ι : Type*} [DecidableEq ι] (W : VertexOperatorAlgebra 𝒱)
    (hh : ι → ℂ) :
    Matrix.of (modularRepT W hh) = Matrix.diagonal (fun i => modularTEntry W (hh i)) := by
  refine Matrix.ext (fun i j => ?_)
  by_cases hij : i = j
  · subst hij; simp [modularRepT, Matrix.diagonal_apply_eq]
  · simp [modularRepT, Matrix.diagonal_apply_ne _ hij, hij]

end

/-- Translating by an integer `k` multiplies the evaluation by `e^{2πikh}`. -/
theorem qEvalAt_translate_nat (χ : FormalQSeries) (h : ℂ) (k : ℕ) {τ τ' : UpperHalfPlane}
    (hτ : (τ' : ℂ) = (τ : ℂ) + k) :
    qEvalAt χ h τ' = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * h) ^ k * qEvalAt χ h τ := by
  have hq : qParam τ' = qParam τ := by
    rw [qParam, qParam, hτ, mul_add, Complex.exp_add,
      show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ)
          = ((k : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by push_cast; ring,
      Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [qEvalAt, qEvalAt, hq, hτ,
    show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((τ : ℂ) + (k : ℂ)) * h
        = 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * h
          + ((k : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * h) from by push_cast; ring,
    Complex.exp_add, Complex.exp_nat_mul]
  ring

section
variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Zhu's 5.3.18b on the whole translation subgroup `⟨T⟩`, analytically.**

For every `k`, `χ_{Mᵢ}(τ+k) = Σ_j ρ(Tᵏ)_{ij}·χ_{Mⱼ}(τ)`, still with **no** summability hypothesis:
`ρ(T)` is diagonal, so `ρ(Tᵏ) = ρ(T)ᵏ` is too (`Matrix.diagonal_pow`), and the sum again collapses
to a single term.

This is Zhu's theorem on the infinite cyclic subgroup generated by `T` — the largest piece reachable
before the growth datum enters.  The `q`-degree shift is taken at `h = h_M − c/24`, the value for
which `e^{2πih}` is the `T`-eigenvalue `modularTEntry`. -/
theorem zhu_modularity_T_pow_analytic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : VertexOperatorAlgebra 𝒱} (D : ModularData W ι) (i : ι) (k : ℕ)
    {τ τ' : UpperHalfPlane} (hτ : (τ' : ℂ) = (τ : ℂ) + k) :
    qEvalAt (gradedDim (D.Mfam i).isMod) (D.h i - W.centralCharge / 24) τ'
      = ∑ j : ι, D.rep (ModularGroup.T ^ k) i j
          * qEvalAt (gradedDim (D.Mfam j).isMod) (D.h i - W.centralCharge / 24) τ := by
  rw [map_pow, D.rep_T, modularRepT_eq_diagonal, Matrix.diagonal_pow,
    Finset.sum_eq_single i
      (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi),
    Matrix.diagonal_apply_eq]
  rw [qEvalAt_translate_nat _ _ k hτ]
  rfl

end

/-! ## The two named data -/

section
variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- **The growth datum**: the graded dimensions of `N`, read along `h + ℕ`, grow subexponentially.

This is what `C₂`-cofiniteness supplies (Zhu / DLM / Buhl); it is carried here as a named `Prop`.
It is proved downstream for the adjoint module (`subexponentialCoeffs_adjoint_of_C2Cofinite`) and
for finitely lowest-weight-generated modules (`subexponentialCoeffs_of_C2Cofinite`). -/
def SubexponentialCoeffs (N : OrdVModule W M) (h : ℂ) : Prop :=
  Subexponential (fun n : ℕ => ‖gradedDim N (h + n)‖)

/-- Given the growth datum, the graded dimension really is summable everywhere on `ℍ`. -/
theorem qSummable_gradedDim (N : OrdVModule W M) (h : ℂ) (hsub : SubexponentialCoeffs N h)
    (τ : UpperHalfPlane) : QSummableAt (gradedDim N) h τ :=
  qSummableAt_of_subexponential _ _ hsub τ

/-- **The evaluation datum** for Zhu's theorem: an assignment of honest functions on `ℍ` to formal
`q`-series, along a fixed conformal-weight shift.  `qEvalAt · h` is the intended instance, and it is
the map `ZhuModularityWeightedAt` takes as its `ev` parameter. -/
def HasQEval (h : ℂ) (ev : FormalQSeries → UpperHalfPlane → ℂ) : Prop :=
  ∀ χ : FormalQSeries, ev χ = qEvalAt χ h

theorem hasQEval_qEvalAt (h : ℂ) : HasQEval h (fun χ => qEvalAt χ h) := fun _ => rfl

end

/-! ## The growth input, supplied downstream

The bridge above is unconditional.  What it consumes is `SubexponentialCoeffs`, which this file
does not prove.  The three-step argument is formalised downstream:

1. **`C₂`-cofinite ⟹ finitely generated** — Gannon 5.3.11a, `Modules/FiniteGeneration`
   (`iterProdSpan_eq_top_of_O₂_le`, `O₂_eq_span_homGen`, …).
2. **An ordered spanning set** over that generating set — `Modularity/BuhlSpanningC2.lean`
   (`orderedSpanningData_adjoint_of_C2Cofinite`; for modules, `orderedSpanningData_of_C2Cofinite`
   under a finite lowest-weight generation hypothesis).  It allows repeated modes, so it is weaker
   than Buhl / Gaberdiel–Neitzke but suffices for growth.
3. **The partition bound** — `Modularity/GrowthBound.lean`: `dim M_{h+n} ≤ b · pcountLe g n` and
   `pcountLe_subexponential`, from the generating-function estimate
   `pcountLe g n · tⁿ ≤ exp(g t / (1 − t)²)` for `t ∈ (0,1)`.  (A bound of the form `p(n) ≤ 2ⁿ`
   would **not** suffice: `2ⁿ` is not subexponential.)

Results: `subexponentialCoeffs_adjoint_of_C2Cofinite`, `subexponentialCoeffs_of_C2Cofinite`.
-/

end VOA
