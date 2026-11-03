import VOA.Huang.HuangODEIterPoint
import VOA.Huang.FrobeniusFundamental

/-! # Hexagon closure: Möbius charts for Fuchsian equations (VOA-free), part 1

Let `g(σ) = e^{λσ} G(e^σ)` solve a Fuchsian equation in `θ = d/dσ` (`x = e^σ`) whose coefficients
are rational with poles only at `x = 1`.  For `q` with `|1 - q| ≤ 1` the Möbius coordinate
`v = x/(x - q)` sends `x = 0, 1, ∞` to `v = 0, 1/(1-q), 1`, so the equation stays Fuchsian at
`v = 0` with coefficients convergent on `|v| < 1`.  In log coordinates (`v = e^τ`) the change is
`σ_q(τ) = log(-q) + τ - log(1 - e^τ)` and `d/dσ = (1 - e^τ) d/dτ`.

This file: the operator `L = (1 - e^τ) d/dτ` (`Lpow`), its expansion
`L^k H = Σ_{j ≤ k} P_{k,j}(e^τ) H^{(j)}` with explicit polynomials (`Pk`, `Lpow_eq`,
`Pk_self = (1-X)^k`, `Pk_eq_zero_of_lt`), and the chain rule `g^{(k)} ∘ σ_q = L^k (g ∘ σ_q)`
(`Lpow_comp`).
-/

noncomputable section
namespace VOA.Huang.TensorCat.HexagonClose
open Polynomial Filter Topology
open scoped BigOperators

/-! ## The polynomials `P_{k,j}` -/

/-- `L^k = Σ_j P_{k,j}(e^τ) d^j/dτ^j` for `L = (1 - e^τ) d/dτ`. -/
def Pk : ℕ → ℕ → ℂ[X]
  | 0, j => if j = 0 then 1 else 0
  | k + 1, j => (1 - X) * (X * derivative (Pk k j) + if j = 0 then 0 else Pk k (j - 1))

theorem Pk_zero (j : ℕ) : Pk 0 j = if j = 0 then 1 else 0 := rfl

theorem Pk_succ (k j : ℕ) :
    Pk (k + 1) j = (1 - X) * (X * derivative (Pk k j) + if j = 0 then 0 else Pk k (j - 1)) := rfl

theorem Pk_eq_zero_of_lt {k j : ℕ} (h : k < j) : Pk k j = 0 := by
  induction k generalizing j with
  | zero => rw [Pk_zero, if_neg (by omega)]
  | succ k ih =>
    rw [Pk_succ, ih (by omega), derivative_zero, mul_zero, zero_add,
      if_neg (by omega), ih (by omega), mul_zero]

theorem Pk_self (k : ℕ) : Pk k k = (1 - X) ^ k := by
  induction k with
  | zero => rw [Pk_zero, if_pos rfl, pow_zero]
  | succ k ih =>
    rw [Pk_succ, Pk_eq_zero_of_lt (by omega : k < k + 1), derivative_zero, mul_zero, zero_add,
      if_neg (by omega), Nat.add_sub_cancel, ih, pow_succ, mul_comm]

/-! ## The operator `L = (1 - e^τ) d/dτ` -/

/-- `L^k H`, with `L H = (1 - e^τ) H'`. -/
def Lpow : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, H => H
  | k + 1, H => fun τ => (1 - Complex.exp τ) * _root_.deriv (Lpow k H) τ

theorem hasDerivAt_eval_exp (P : ℂ[X]) (τ : ℂ) :
    HasDerivAt (fun τ => P.eval (Complex.exp τ))
      ((derivative P).eval (Complex.exp τ) * Complex.exp τ) τ :=
  (P.hasDerivAt (Complex.exp τ)).comp τ (Complex.hasDerivAt_exp τ)

/-- `L^k H = Σ_{j ≤ k} P_{k,j}(e^τ) H^{(j)}` on an open set where `H` is holomorphic. -/
theorem Lpow_eq {U : Set ℂ} (hU : IsOpen U) {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H U) (k : ℕ) :
    ∀ τ ∈ U, Lpow k H τ = ∑ j ∈ Finset.range (k + 1),
      (Pk k j).eval (Complex.exp τ) * iteratedDeriv j H τ := by
  induction k with
  | zero =>
    intro τ _
    simp [Lpow, Pk_zero]
  | succ k ih =>
    intro τ hτ
    have hev : Lpow k H =ᶠ[𝓝 τ] fun τ' => ∑ j ∈ Finset.range (k + 1),
        (Pk k j).eval (Complex.exp τ') * iteratedDeriv j H τ' :=
      Filter.eventually_of_mem (hU.mem_nhds hτ) ih
    have hd : HasDerivAt (fun τ' => ∑ j ∈ Finset.range (k + 1),
        (Pk k j).eval (Complex.exp τ') * iteratedDeriv j H τ')
        (∑ j ∈ Finset.range (k + 1), ((derivative (Pk k j)).eval (Complex.exp τ) *
          Complex.exp τ * iteratedDeriv j H τ +
          (Pk k j).eval (Complex.exp τ) * iteratedDeriv (j + 1) H τ)) τ := by
      refine HasDerivAt.fun_sum fun j _ => ?_
      exact (hasDerivAt_eval_exp _ τ).mul
        (VOA.Huang.FrobeniusLog.hasDerivAt_iteratedDeriv hU hH j hτ)
    change (1 - Complex.exp τ) * _root_.deriv (Lpow k H) τ = _
    rw [hev.deriv_eq, hd.deriv]
    -- regroup
    set v := Complex.exp τ with hv
    set D : ℕ → ℂ := fun j => iteratedDeriv j H τ with hD
    have hS1 : ∑ j ∈ Finset.range (k + 1 + 1), (1 - v) * (v * (derivative (Pk k j)).eval v * D j)
        = ∑ j ∈ Finset.range (k + 1), (1 - v) * (v * (derivative (Pk k j)).eval v * D j) := by
      rw [Finset.sum_range_succ, Pk_eq_zero_of_lt (by omega : k < k + 1), derivative_zero,
        eval_zero]
      ring
    have hS2 : ∑ j ∈ Finset.range (k + 1 + 1),
        (1 - v) * ((if j = 0 then 0 else (Pk k (j - 1)).eval v) * D j)
        = ∑ j ∈ Finset.range (k + 1), (1 - v) * ((Pk k j).eval v * D (j + 1)) := by
      rw [Finset.sum_range_succ', if_pos rfl, zero_mul, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [if_neg (by omega), Nat.add_sub_cancel]
    have h1 : ∑ j ∈ Finset.range (k + 1 + 1), (Pk (k + 1) j).eval v * D j =
        ∑ j ∈ Finset.range (k + 1 + 1), (1 - v) * (v * (derivative (Pk k j)).eval v * D j) +
        ∑ j ∈ Finset.range (k + 1 + 1), (1 - v) * ((if j = 0 then 0 else (Pk k (j - 1)).eval v)
          * D j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pk_succ]
      split_ifs <;> simp <;> ring
    change _ = ∑ j ∈ Finset.range (k + 1 + 1), (Pk (k + 1) j).eval v * D j
    rw [h1, hS1, hS2, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hD]
    ring

/-! ## The Möbius log-coordinate -/

/-- `σ_q(τ) = log(-q) + τ - log(1 - e^τ)`, so that `e^{σ_q(τ)} = -q e^τ/(1 - e^τ)`. -/
def sigmaQ (q τ : ℂ) : ℂ := Complex.log (-q) + τ - Complex.log (1 - Complex.exp τ)

theorem one_sub_exp_re_pos {τ : ℂ} (hτ : τ.re < 0) : 0 < (1 - Complex.exp τ).re := by
  have h1 : ‖Complex.exp τ‖ < 1 := by rw [Complex.norm_exp]; exact Real.exp_lt_one_iff.2 hτ
  have := Complex.re_le_norm (Complex.exp τ)
  rw [Complex.sub_re, Complex.one_re]
  linarith

theorem one_sub_exp_ne_zero {τ : ℂ} (hτ : τ.re < 0) : 1 - Complex.exp τ ≠ 0 := by
  intro h; have := one_sub_exp_re_pos hτ; rw [h] at this; simp at this

theorem exp_sigmaQ {q τ : ℂ} (hq : q ≠ 0) (hτ : τ.re < 0) :
    Complex.exp (sigmaQ q τ) = -q * Complex.exp τ / (1 - Complex.exp τ) := by
  rw [sigmaQ, Complex.exp_sub, Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hq),
    Complex.exp_log (one_sub_exp_ne_zero hτ)]

theorem hasDerivAt_sigmaQ (q : ℂ) {τ : ℂ} (hτ : τ.re < 0) :
    HasDerivAt (sigmaQ q) (1 / (1 - Complex.exp τ)) τ := by
  have hslit : 1 - Complex.exp τ ∈ Complex.slitPlane := Or.inl (one_sub_exp_re_pos hτ)
  have h1 : HasDerivAt (fun τ => 1 - Complex.exp τ) (-Complex.exp τ) τ := by
    simpa using (Complex.hasDerivAt_exp τ).const_sub 1
  have h2 := h1.clog hslit
  have h3 := ((hasDerivAt_id τ).const_add (Complex.log (-q))).sub h2
  convert h3 using 1
  have := one_sub_exp_ne_zero hτ
  field_simp
  ring

theorem differentiableOn_sigmaQ (q : ℂ) :
    DifferentiableOn ℂ (sigmaQ q) {τ : ℂ | τ.re < 0} := fun _ hτ =>
  (hasDerivAt_sigmaQ q hτ).differentiableAt.differentiableWithinAt

/-- **Chain rule through the chart**: `g^{(k)}(σ_q(τ)) = L^k (g ∘ σ_q)(τ)`. -/
theorem Lpow_comp {q : ℂ} {U : Set ℂ} (hU : IsOpen U) (hUneg : ∀ τ ∈ U, τ.re < 0)
    {V : Set ℂ} (hVo : IsOpen V) (hUV : ∀ τ ∈ U, sigmaQ q τ ∈ V) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g V) (k : ℕ) :
    ∀ τ ∈ U, Lpow k (fun τ => g (sigmaQ q τ)) τ = iteratedDeriv k g (sigmaQ q τ) := by
  induction k with
  | zero => intro τ _; simp [Lpow]
  | succ k ih =>
    intro τ hτ
    have hev : Lpow k (fun τ => g (sigmaQ q τ)) =ᶠ[𝓝 τ]
        fun τ' => iteratedDeriv k g (sigmaQ q τ') :=
      Filter.eventually_of_mem (hU.mem_nhds hτ) ih
    have hd := (VOA.Huang.FrobeniusLog.hasDerivAt_iteratedDeriv hVo hg k (hUV τ hτ)).comp τ
      (hasDerivAt_sigmaQ q (hUneg τ hτ))
    change (1 - Complex.exp τ) * _root_.deriv (Lpow k (fun τ => g (sigmaQ q τ))) τ = _
    rw [hev.deriv_eq, show (fun τ' => iteratedDeriv k g (sigmaQ q τ')) =
      iteratedDeriv k g ∘ sigmaQ q from rfl, hd.deriv]
    have := one_sub_exp_ne_zero (hUneg τ hτ)
    field_simp

end VOA.Huang.TensorCat.HexagonClose
