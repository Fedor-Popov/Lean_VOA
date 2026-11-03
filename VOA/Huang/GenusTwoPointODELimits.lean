import VOA.Huang.GenusTwoPointODEBounds
import VOA.Huang.GenusTwoPointVacuum

/-!
# The limits of a common scalar ODE argument

A fixed regular-singular equation cannot contain a family of nonzero monomials
of unbounded degree. The vacuum product traces already have precisely this
diagonal form whenever their one-point coefficients have unbounded support.
Thus independence of the intertwiners in Huang's Remark 1.5 must not be read
as a common scalar equation across every traced weight.

The numerical diagonal example below also has separate subexponential bounds
and an entire-coefficient Fuchsian equation for each row, but no joint bound.
It is an analytic counterexample to an inference, not a counterexample VOA.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA PowerSeries FuchsianODE
open scoped BigOperators

/-- No fixed scalar equation for nonzero diagonal coefficients at unbounded levels. -/
theorem no_common_fuchsian_diagonal {d : ℕ → ℂ}
    (hd : ∀ K : ℕ, ∃ n, K ≤ n ∧ d n ≠ 0)
    (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ)
    (hc : ∀ i < s, c i ∈ SubexpPS) :
    ¬ ∀ n, FuchsianEq lam s c (PowerSeries.mk (fun k => if k = n then d n else 0)) := by
  intro heq
  obtain ⟨K, hK⟩ := fuchsian_finite_jet_determines lam s c hc
  obtain ⟨n, hn, hd⟩ := hd K
  have hz := hK _ (heq n) (fun j hj => by
    simp only [coeff_mk, if_neg (show j ≠ n by omega)])
  have he := congrArg (coeff n) hz
  exact hd (by simpa using he)

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P N : LWModule W}

/-- Concrete obstruction in the existing vacuum sector. The unbounded-support
hypothesis is explicit; no existence theorem for such a VOA is asserted here. -/
theorem vacuum_product_no_common_fuchsian (hv : W.vacuum ≠ 0)
    (Y : IntertwiningOperator P.isMod N.isMod N.isMod)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α)
    (hsupp : ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
      GenusOne.trace Y w (N.h + n - W.centralCharge / 24) ≠ 0)
    (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ)
    (hc : ∀ i < s, c i ∈ SubexpPS) :
    ¬ ∀ n, FuchsianEq lam s c (PowerSeries.mk (fun k =>
      productLevelCoeff (P₁ := vacuumLW W hv) (moduleIntertwiner N.isMod) Y
        W.vacuum w 0 α n k)) := by
  simpa only [productLevelCoeff_vacuum hv Y hw] using
    no_common_fuchsian_diagonal hsupp lam s c hc

/-- A scalar example, unrelated to VOA structure. -/
noncomputable def diagonalModel (n k : ℕ) : ℂ := if k = n then (16 : ℂ) ^ n else 0

/-- Every row and every column separately has finite support and is subexponential. -/
theorem diagonalModel_separately_subexponential :
    (∀ n, Subexponential (fun k => ‖diagonalModel n k‖)) ∧
      (∀ k, Subexponential (fun n => ‖diagonalModel n k‖)) := by
  constructor
  · intro n r hr
    refine ⟨16 ^ n, fun k => ?_⟩
    dsimp only [diagonalModel]
    split_ifs
    · norm_num only [norm_pow, Complex.norm_ofNat]
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr.le)
    · simp only [norm_zero]
      positivity
  · intro k r hr
    refine ⟨16 ^ k, fun n => ?_⟩
    dsimp only [diagonalModel]
    split_ifs with h
    · subst n
      norm_num only [norm_pow, Complex.norm_ofNat]
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr.le)
    · simp only [norm_zero]
      positivity

/-- Each row solves a Fuchsian equation with constant, hence entire, coefficients.
The equation depends on the row n. -/
theorem diagonalModel_fuchsian (n : ℕ) :
    FuchsianEq 0 1 (fun _ => PowerSeries.C (-(n : ℂ))) (PowerSeries.mk (diagonalModel n)) := by
  simp only [FuchsianEq, Function.iterate_one, Function.iterate_zero, id_eq,
    Finset.sum_range_one]
  ext k
  simp only [map_add, coeff_thetaShift, zero_add, coeff_C_mul, coeff_mk, map_zero]
  unfold diagonalModel
  split_ifs with h
  · subst k
    ring
  · ring

/-- Separate convergence and row-dependent ODEs do not imply mode growth. -/
theorem diagonalModel_not_twoLevelBound :
    ¬ ∃ C : ℝ, TwoLevelBound diagonalModel C 2 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 4)
  have hb := hC n n
  norm_num [diagonalModel] at hb
  have h16 : (16 : ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
  have h4 : (2 : ℝ) ^ n * 2 ^ n = 4 ^ n := by rw [← mul_pow]; norm_num
  rw [h16, mul_assoc, h4] at hb
  have hpos : (0 : ℝ) < 4 ^ n := by positivity
  exact (not_le_of_gt hn) ((mul_le_mul_iff_left₀ hpos).mp hb)

end VOA.Huang.GenusTwoPoint
