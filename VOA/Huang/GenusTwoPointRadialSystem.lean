import VOA.Huang.GenusTwoPointUniformMajorant
import VOA.Huang.GenusTwoPointGrowth

/-!
# Uniform estimates for systems graded by total degree

The coefficient spaces may change with the degree. In two variables the space
at degree n is `Fin (n+1) → ℂ`, containing the whole antidiagonal, rather than
one fixed traced-weight row. A uniformly bounded diagonal block and a
subexponential bound on the off-diagonal blocks give a cutoff independent of
the solution. All resonances are retained in the finite initial jet.

No such system is asserted for general intertwiner traces in this file.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA Filter
open scoped BigOperators

section Graded
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, NormedSpace ℂ (E n)]

/-- A regular Euler system, allowing finite-dimensional blocks of increasing
size. Only strictly lower degrees appear on the right after the diagonal. -/
def GradedEulerEquation (B : ∀ n, E n →L[ℂ] E n)
    (A : ∀ n m, E m →L[ℂ] E n) (f : ∀ n, E n) : Prop :=
  ∀ n : ℕ, (n : ℂ) • f n = B n (f n) + ∑ m ∈ Finset.range n, A n m (f m)

/-- The coefficient norm inequality, with a divisor growing independently of
the changing block dimension. -/
theorem gradedEuler_majorant {B : ∀ n, E n →L[ℂ] E n}
    {A : ∀ n m, E m →L[ℂ] E n} {f : ∀ n, E n} {b : ℝ} {a : ℕ → ℝ}
    (hB : ∀ n, ‖B n‖ ≤ b) (hA : ∀ n m, m < n → ‖A n m‖ ≤ a (n - m))
    (heq : GradedEulerEquation B A f) (n : ℕ) :
    ((n : ℝ) - b) * ‖f n‖ ≤
      ∑ m ∈ Finset.range n, a (n - m) * ‖f m‖ := by
  have hnorm : (n : ℝ) * ‖f n‖ ≤
      b * ‖f n‖ + ∑ m ∈ Finset.range n, a (n - m) * ‖f m‖ := by
    calc
      (n : ℝ) * ‖f n‖ = ‖(n : ℂ) • f n‖ := by rw [norm_smul, Complex.norm_natCast]
      _ = ‖B n (f n) + ∑ m ∈ Finset.range n, A n m (f m)‖ := congrArg norm (heq n)
      _ ≤ ‖B n (f n)‖ + ‖∑ m ∈ Finset.range n, A n m (f m)‖ := norm_add_le _ _
      _ ≤ b * ‖f n‖ + ∑ m ∈ Finset.range n, a (n - m) * ‖f m‖ := by
        apply add_le_add
        · exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))
        · apply (norm_sum_le _ _).trans
          exact Finset.sum_le_sum fun m hm => (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hA n m (Finset.mem_range.mp hm)) (norm_nonneg _))
  nlinarith

/-- A cutoff uniform over every system with these bounds, as well as every
solution. In particular it does not grow with the block dimension. -/
theorem uniform_gradedEuler_cutoff (b : ℝ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Subexponential a) {r : ℝ} (hr : 1 < r) :
    ∃ K : ℕ, ∀ (B : ∀ n, E n →L[ℂ] E n) (A : ∀ n m, E m →L[ℂ] E n)
      (f : ∀ n, E n) (C : ℝ),
      (∀ n, ‖B n‖ ≤ b) → (∀ n m, m < n → ‖A n m‖ ≤ a (n - m)) →
      GradedEulerEquation B A f → 0 ≤ C →
      (∀ n < K, ‖f n‖ ≤ C * r ^ n) → ∀ n, ‖f n‖ ≤ C * r ^ n := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) - b) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-b) tendsto_natCast_atTop_atTop |>.congr
      (fun n => by simp only [sub_eq_add_neg])
  obtain ⟨K, _, hK⟩ := uniform_majorant_cutoff ha0 ha hp 0 hr
  exact ⟨K, fun B A f C hB hA heq hC hinit =>
    hK (fun n => ‖f n‖) C (fun _ => norm_nonneg _) hC
      (fun n _ => gradedEuler_majorant hB hA heq n) hinit⟩

/-- The amplitude is controlled by a finite initial jet; it is never dropped. -/
theorem uniform_gradedEuler_initial_bound (b : ℝ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Subexponential a) {r : ℝ} (hr : 1 < r) :
    ∃ K : ℕ, ∀ (B : ∀ n, E n →L[ℂ] E n) (A : ∀ n m, E m →L[ℂ] E n)
      (f : ∀ n, E n),
      (∀ n, ‖B n‖ ≤ b) → (∀ n m, m < n → ‖A n m‖ ≤ a (n - m)) →
      GradedEulerEquation B A f → ∀ n,
      ‖f n‖ ≤ (∑ j ∈ Finset.range K, ‖f j‖) * r ^ n := by
  obtain ⟨K, hK⟩ := uniform_gradedEuler_cutoff (E := E) b a ha0 ha hr
  refine ⟨K, fun B A f hB hA heq => hK B A f _ hB hA heq
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_⟩
  intro n hn
  exact (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hn)).trans
    (le_mul_of_one_le_right (Finset.sum_nonneg fun _ _ => norm_nonneg _) (one_le_pow₀ hr.le))

/-- Resonant initial coefficients are included in a single determining jet,
uniform over every system obeying the specified bounds. -/
theorem gradedEuler_finite_jet_determines (b : ℝ) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Subexponential a) :
    ∃ K : ℕ, ∀ (B : ∀ n, E n →L[ℂ] E n) (A : ∀ n m, E m →L[ℂ] E n)
      (f : ∀ n, E n),
      (∀ n, ‖B n‖ ≤ b) → (∀ n m, m < n → ‖A n m‖ ≤ a (n - m)) →
      GradedEulerEquation B A f → (∀ n < K, f n = 0) → ∀ n, f n = 0 := by
  obtain ⟨K, hK⟩ := uniform_gradedEuler_cutoff (E := E) b a ha0 ha (by norm_num : (1 : ℝ) < 2)
  refine ⟨K, fun B A f hB hA heq hz n => norm_eq_zero.mp ?_⟩
  have hb := hK B A f 0 hB hA heq le_rfl (fun j hj => by simp [hz j hj]) n
  exact le_antisymm (by simpa only [zero_mul] using hb) (norm_nonneg _)

end Graded

/-- All coefficients of total degree n, including both endpoints. -/
noncomputable def degreeBlock (d : ℕ → ℕ → ℂ) (n : ℕ) : Fin (n + 1) → ℂ :=
  fun i => d i (n - i)

theorem norm_le_degreeBlock (d : ℕ → ℕ → ℂ) (n k : ℕ) :
    ‖d n k‖ ≤ ‖degreeBlock d (n + k)‖ := by
  have h := norm_le_pi_norm (degreeBlock d (n + k)) (⟨n, by omega⟩ : Fin (n + k + 1))
  simpa only [degreeBlock, Nat.add_sub_cancel_left] using h

/-- A precise sufficient coupled-system condition on the actual two-index
array. Establishing this condition from Ward equations is a separate task. -/
def RadialEulerControl (d : ℕ → ℕ → ℂ) : Prop :=
  ∃ (b : ℝ) (a : ℕ → ℝ)
    (B : ∀ n, (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ))
    (A : ∀ n m, (Fin (m + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)),
    (∀ n, 0 ≤ a n) ∧ Subexponential a ∧
    (∀ n, ‖B n‖ ≤ b) ∧ (∀ n m, m < n → ‖A n m‖ ≤ a (n - m)) ∧
    GradedEulerEquation B A (degreeBlock d)

/-- A coupled total-degree system gives the joint estimate required for sewing.
No common scalar equation for the individual rows is assumed. -/
theorem twoLevelGrowth_of_radialEuler {d : ℕ → ℕ → ℂ} (h : RadialEulerControl d) :
    ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 ≤ C ∧ TwoLevelBound d C r r := by
  obtain ⟨b, a, B, A, ha0, ha, hB, hA, heq⟩ := h
  intro r hr
  obtain ⟨K, hK⟩ := uniform_gradedEuler_initial_bound
    (E := fun n => Fin (n + 1) → ℂ) b a ha0 ha hr
  refine ⟨∑ j ∈ Finset.range K, ‖degreeBlock d j‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun n k => ?_⟩
  have hb := (norm_le_degreeBlock d n k).trans (hK B A (degreeBlock d) hB hA heq (n + k))
  simpa only [pow_add, mul_assoc] using hb

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

theorem productModeGrowth_of_radialEuler
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (h : RadialEulerControl (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂)) :
    ProductModeGrowth Y₁ Y₂ w₁ w₂ α₁ α₂ :=
  twoLevelGrowth_of_radialEuler h

theorem iterateModeGrowth_of_radialEuler
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (h : RadialEulerControl (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂)) :
    IterateModeGrowth Y₃ Y₄ w₁ w₂ α₁ α₂ := by
  intro r hr
  obtain ⟨C, hC, hb⟩ := twoLevelGrowth_of_radialEuler h r hr
  exact ⟨C, r, hC, by linarith, hb⟩

end VOA.Huang.GenusTwoPoint
