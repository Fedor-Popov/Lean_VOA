import VOA.Huang.HexagonCloseChart

/-! # Hexagon closure: Möbius charts for Fuchsian equations (VOA-free), part 2

For a formal solution `G` of a Fuchsian equation `θ_λ^s G + Σ_{i<s} cᵢ θ_λ^i G = 0` with
`(1 - x)^b cᵢ` polynomial, and a chart parameter `q ≠ 0` with `|1 - q| ≤ 1`:

* `Cq q b p i` — the coefficient `cᵢ(x)` written as a convergent power series in `v`, where
  `x = -q v/(1 - v)` (`psEval_Cq`);
* `cHat` — the coefficients of the transformed equation `H^{(s)} + Σ_{j<s} ĉⱼ(e^τ) H^{(j)} = 0`
  satisfied by `H = g ∘ σ_q`, `g(σ) = e^{λσ} G(e^σ)` (`tau_ode`);
* `chart_continuation`: `v ↦ G(-q v/(1 - v))`, given for small `v`, continues to a function
  holomorphic in `τ = log v` on the whole half plane `Re τ < 0`, i.e. on the universal cover of
  `0 < |v| < 1` (from `FrobeniusLog.fundamental_system`).
-/

noncomputable section
namespace VOA.Huang.TensorCat.HexagonClose
open Polynomial Filter Topology
open VOA.Huang.FrobeniusLog (psEval logFun halfPlane LogGood LogFuchsianEq)
open VOA.Huang.HuangODEIterPoint
open VOA.Huang.FuchsianODE
open scoped BigOperators

/-! ## Geometric series -/

/-- `Σ aⁿ vⁿ`. -/
def geomA (a : ℂ) : PowerSeries ℂ := PowerSeries.mk fun n => a ^ n

theorem geomA_mem {a : ℂ} (ha : ‖a‖ ≤ 1) : geomA a ∈ SubexpPS := mk_pow_mem_subexpPS ha

theorem psEval_geomA {a v : ℂ} (h : ‖a * v‖ < 1) : psEval (geomA a) v = (1 - a * v)⁻¹ := by
  unfold psEval geomA
  rw [← tsum_geometric_of_norm_lt_one h]
  exact tsum_congr fun n => by rw [PowerSeries.coeff_mk, mul_pow]

theorem psEval_one_sub_X_pow {x : ℂ} (hx : ‖x‖ < 1) (b : ℕ) :
    psEval ((1 - PowerSeries.X) ^ b) x = (1 - x) ^ b := by
  rw [psEval_pow one_sub_X_mem_subexp hx, psEval_sub (SubexpPS.one_mem) X_mem_subexp hx,
    psEval_one, psEval_X]

/-! ## The coefficients in the chart -/

variable (q : ℂ) (b : ℕ) (p : ℕ → ℂ[X])

/-- `cᵢ(x)` at `x = -q v/(1 - v)`, as a power series in `v`:
`p(-qv/(1-v)) · (1-v)^b · (1 - (1-q) v)^{-b}`. -/
def Cq (i : ℕ) : PowerSeries ℂ :=
  (∑ m ∈ Finset.range ((p i).natDegree + 1),
      PowerSeries.C ((p i).coeff m * (-q) ^ m) * PowerSeries.X ^ m * geomA 1 ^ m) *
    (1 - PowerSeries.X) ^ b * geomA (1 - q) ^ b

theorem Cq_mem {q : ℂ} (hq1 : ‖1 - q‖ ≤ 1) (i : ℕ) : Cq q b p i ∈ SubexpPS := by
  unfold Cq
  refine SubexpPS.mul_mem (SubexpPS.mul_mem (SubexpPS.sum_mem fun m _ => ?_)
    (SubexpPS.pow_mem one_sub_X_mem_subexp b)) (SubexpPS.pow_mem (geomA_mem hq1) b)
  exact SubexpPS.mul_mem (SubexpPS.mul_mem (C_mem_subexp _) (SubexpPS.pow_mem X_mem_subexp m))
    (SubexpPS.pow_mem (geomA_mem (by simp)) m)

/-- The chart point `x = -q v/(1 - v)`. -/
def chartX (v : ℂ) : ℂ := -q * v / (1 - v)

theorem psEval_Cq {q : ℂ} (hq1 : ‖1 - q‖ ≤ 1) {c : ℕ → PowerSeries ℂ} {i : ℕ}
    (hcp : (1 - PowerSeries.X) ^ b * c i = (p i : PowerSeries ℂ)) {v : ℂ} (hv : ‖v‖ < 1)
    (hx : ‖chartX q v‖ < 1) :
    psEval (Cq q b p i) v = psEval (c i) (chartX q v) := by
  have hc : c i ∈ SubexpPS := mem_subexpPS_of_mul_eq' (a := 1) (by simp)
    (by simpa using hcp)
  have h1v : 1 - v ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hv; simp at hv
  set x := chartX q v with hxdef
  have h1x : 1 - x ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hx; simp at hx
  -- the value of `cᵢ` at `x`
  have hval := congrArg (fun A => psEval A x) hcp
  simp only at hval
  rw [psEval_mul (SubexpPS.pow_mem one_sub_X_mem_subexp b) hc hx, psEval_one_sub_X_pow hx,
    psEval_coe] at hval
  have hcx : psEval (c i) x = (p i).eval x / (1 - x) ^ b := by
    rw [eq_div_iff (pow_ne_zero _ h1x), mul_comm, hval]
  rw [hcx]
  -- the value of `Cq`
  have hav : ‖(1 - q) * v‖ < 1 := by
    rw [norm_mul]; calc ‖1 - q‖ * ‖v‖ ≤ 1 * ‖v‖ := by gcongr
      _ < 1 := by rwa [one_mul]
  have h1v' : ‖(1 : ℂ) * v‖ < 1 := by rwa [one_mul]
  have hm : ∀ m ∈ Finset.range ((p i).natDegree + 1),
      PowerSeries.C ((p i).coeff m * (-q) ^ m) * PowerSeries.X ^ m * geomA 1 ^ m ∈ SubexpPS :=
    fun m _ => SubexpPS.mul_mem (SubexpPS.mul_mem (C_mem_subexp _)
      (SubexpPS.pow_mem X_mem_subexp m)) (SubexpPS.pow_mem (geomA_mem (by simp)) m)
  unfold Cq
  rw [psEval_mul (SubexpPS.mul_mem (SubexpPS.sum_mem hm)
      (SubexpPS.pow_mem one_sub_X_mem_subexp b)) (SubexpPS.pow_mem (geomA_mem hq1) b) hv,
    psEval_mul (SubexpPS.sum_mem hm) (SubexpPS.pow_mem one_sub_X_mem_subexp b) hv,
    psEval_sum _ hm hv, psEval_one_sub_X_pow hv, psEval_pow (geomA_mem hq1) hv,
    psEval_geomA hav]
  have hterm : ∀ m ∈ Finset.range ((p i).natDegree + 1),
      psEval (PowerSeries.C ((p i).coeff m * (-q) ^ m) * PowerSeries.X ^ m * geomA 1 ^ m) v =
        (p i).coeff m * x ^ m := by
    intro m _
    rw [psEval_mul (SubexpPS.mul_mem (C_mem_subexp _) (SubexpPS.pow_mem X_mem_subexp m))
        (SubexpPS.pow_mem (geomA_mem (by simp)) m) hv,
      psEval_mul (C_mem_subexp _) (SubexpPS.pow_mem X_mem_subexp m) hv,
      psEval_pow X_mem_subexp hv, psEval_X, psEval_pow (geomA_mem (by simp)) hv,
      psEval_geomA h1v', ← Polynomial.coe_C, psEval_coe, Polynomial.eval_C, hxdef, chartX]
    rw [one_mul, div_pow, mul_pow]
    rw [inv_pow, div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl hterm, ← Polynomial.eval_eq_sum_range]
  have h1x' : 1 - x = (1 - (1 - q) * v) / (1 - v) := by
    rw [hxdef, chartX]; field_simp; ring
  rw [h1x', div_pow, inv_pow]
  have h1qv : 1 - (1 - q) * v ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hav; simp at hav
  field_simp

end VOA.Huang.TensorCat.HexagonClose
