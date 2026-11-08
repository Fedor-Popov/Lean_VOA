import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Order.Field.Basic

/-!
# The logarithmic-derivative equation `p A′ = A L`

Over a field `K` of characteristic `0`, for `L ∈ K[[p]]` with `L(0) = 0`:
* `odeSol L` is the power series with constant term `1` solving `p A′ = A L` (`odeSol_spec`),
  defined by the recursion `(a+1) A_{a+1} = Σ_{i ≤ a} A_i L_{a+1−i}`;
* `eq_of_ode`: a solution is determined by its constant term;
* `odeSol_add`: `odeSol (L₁ + L₂) = odeSol L₁ · odeSol L₂`.

`odeSol L` is "`exp(∫ L/p)`" without exponentials or logarithms. It is used to define the product
`Π (1 − pᵐ qⁿ)^{e(m,n)}` through its logarithmic derivative (`MoonshineLRM5Product`).
-/

namespace VOA.Moonshine.ConwayNorton.M8

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficients of the solution of `p A′ = A L`, `A(0) = 1`. -/
noncomputable def odeCoeff (L : PowerSeries K) : ℕ → K
  | 0 => 1
  | a + 1 => ((a + 1 : ℕ) : K)⁻¹ *
      ∑ i : Fin (a + 1), odeCoeff L i * PowerSeries.coeff (a + 1 - i) L
termination_by a => a
decreasing_by exact i.isLt

omit [CharZero K] in
theorem odeCoeff_zero (L : PowerSeries K) : odeCoeff L 0 = 1 := by
  rw [odeCoeff]

omit [CharZero K] in
theorem odeCoeff_succ (L : PowerSeries K) (a : ℕ) :
    odeCoeff L (a + 1) = ((a + 1 : ℕ) : K)⁻¹ *
      ∑ i : Fin (a + 1), odeCoeff L i * PowerSeries.coeff (a + 1 - i) L := by
  rw [odeCoeff]

/-- The solution of `p A′ = A L` with `A(0) = 1`. -/
noncomputable def odeSol (L : PowerSeries K) : PowerSeries K := PowerSeries.mk (odeCoeff L)

omit [CharZero K] in
theorem constantCoeff_odeSol (L : PowerSeries K) : PowerSeries.constantCoeff (odeSol L) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, odeSol, PowerSeries.coeff_mk, odeCoeff_zero]

omit [CharZero K] in
/-- The `p^{a+1}`-coefficient of `A L` when `L(0) = 0`. -/
theorem coeff_succ_mul_of_constantCoeff_eq_zero (A L : PowerSeries K)
    (hL : PowerSeries.constantCoeff L = 0) (a : ℕ) :
    PowerSeries.coeff (a + 1) (A * L) =
      ∑ i : Fin (a + 1), PowerSeries.coeff i A * PowerSeries.coeff (a + 1 - i) L := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i A * PowerSeries.coeff j L), Finset.sum_range_succ,
    Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, hL, mul_zero, add_zero,
    Finset.sum_range]

omit [CharZero K] in
theorem coeff_succ_X_mul_derivative (A : PowerSeries K) (a : ℕ) :
    PowerSeries.coeff (a + 1) (PowerSeries.X * PowerSeries.derivative K A) =
      ((a + 1 : ℕ) : K) * PowerSeries.coeff (a + 1) A := by
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, mul_comm]
  push_cast
  ring

/-- **`odeSol L` solves `p A′ = A L`.** -/
theorem odeSol_spec (L : PowerSeries K) (hL : PowerSeries.constantCoeff L = 0) :
    PowerSeries.X * PowerSeries.derivative K (odeSol L) = odeSol L * L := by
  ext n
  rcases n with _ | a
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, hL,
      mul_zero]
  · rw [coeff_succ_X_mul_derivative, coeff_succ_mul_of_constantCoeff_eq_zero _ _ hL]
    simp only [odeSol, PowerSeries.coeff_mk]
    rw [odeCoeff_succ, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero a),
      one_mul]

/-- **Uniqueness:** two solutions of `p A′ = A L` with the same constant term coincide. -/
theorem eq_of_ode {A B L : PowerSeries K} (hL : PowerSeries.constantCoeff L = 0)
    (hA : PowerSeries.X * PowerSeries.derivative K A = A * L)
    (hB : PowerSeries.X * PowerSeries.derivative K B = B * L)
    (h0 : PowerSeries.constantCoeff A = PowerSeries.constantCoeff B) : A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | a
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    · have hA' := congrArg (PowerSeries.coeff (a + 1)) hA
      have hB' := congrArg (PowerSeries.coeff (a + 1)) hB
      rw [coeff_succ_X_mul_derivative, coeff_succ_mul_of_constantCoeff_eq_zero _ _ hL] at hA' hB'
      have hsum : ∑ i : Fin (a + 1), PowerSeries.coeff i A * PowerSeries.coeff (a + 1 - i) L =
          ∑ i : Fin (a + 1), PowerSeries.coeff i B * PowerSeries.coeff (a + 1 - i) L :=
        Finset.sum_congr rfl fun i _ => by rw [ih i (by have := i.isLt; omega)]
      have hne : ((a + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
      apply mul_left_cancel₀ hne
      rw [hA', hB', hsum]

/-- **Multiplicativity:** `odeSol (L₁ + L₂) = odeSol L₁ · odeSol L₂`. -/
theorem odeSol_add (L₁ L₂ : PowerSeries K) (h₁ : PowerSeries.constantCoeff L₁ = 0)
    (h₂ : PowerSeries.constantCoeff L₂ = 0) :
    odeSol (L₁ + L₂) = odeSol L₁ * odeSol L₂ := by
  have h12 : PowerSeries.constantCoeff (L₁ + L₂) = 0 := by rw [map_add, h₁, h₂, add_zero]
  refine eq_of_ode h12 (odeSol_spec _ h12) ?_ ?_
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add, ← mul_assoc, ← mul_assoc,
      mul_comm PowerSeries.X (odeSol L₁), mul_assoc, odeSol_spec _ h₂,
      mul_comm PowerSeries.X (odeSol L₂), mul_assoc (odeSol L₂), odeSol_spec _ h₁]
    ring
  · rw [map_mul, constantCoeff_odeSol, constantCoeff_odeSol, constantCoeff_odeSol, mul_one]

end VOA.Moonshine.ConwayNorton.M8
