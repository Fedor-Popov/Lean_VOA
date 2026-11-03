import VOA.Huang.GenusTwoPointCoordinates

/-!
# The scalar iterative logarithm in Huang's geometric modification

`flowCoeff a r n` is the coefficient of z^(n+1) in D^r z, where
D = sum_{j>=1} a(j-1) z^(j+1) d/dz. All sums are finite coefficientwise.
Triangular recursion constructs the unique coefficients for any tangent-to-identity
coordinate. In particular the target log(1+c*z)/c has coefficients
(-c)^n/(n+1), including c=0 by its formal continuation.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open scoped BigOperators

/-- Coefficients of repeated application of a positive formal vector field. -/
def flowCoeff (a : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, n => if n = 0 then 1 else 0
  | r + 1, n => ∑ j ∈ Finset.range n, ((j : ℂ) + 1) * flowCoeff a r j * a (n - 1 - j)

@[simp] theorem flowCoeff_zero (a : ℕ → ℂ) (r : ℕ) : flowCoeff a (r + 1) 0 = 0 := by
  simp [flowCoeff]

@[simp] theorem flowCoeff_one (a : ℕ → ℂ) (n : ℕ) : flowCoeff a 1 (n + 1) = a n := by
  simp [flowCoeff, Finset.sum_ite_eq']

/-- Each iteration raises the order at least once. -/
theorem flowCoeff_vanish (a : ℕ → ℂ) {r n : ℕ} (h : n < r) : flowCoeff a r n = 0 := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
    apply Finset.sum_eq_zero
    intro j hj
    rw [ih (by have := Finset.mem_range.mp hj; omega), mul_zero, zero_mul]

/-- The coefficient of degree n+1 only uses a(0),...,a(n-1). -/
theorem flowCoeff_congr {a b : ℕ → ℂ} (r n : ℕ) (h : ∀ j < n, a j = b j) :
    flowCoeff a r n = flowCoeff b r n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    rw [ih j (fun k hk => h k (by omega)), h (n - 1 - j) (by omega)]

/-- After two iterations the newest generator coefficient does not occur. -/
theorem flowCoeff_congr_tail {a b : ℕ → ℂ} (r n : ℕ) (h : ∀ j < n, a j = b j) :
    flowCoeff a (r + 2) (n + 1) = flowCoeff b (r + 2) (n + 1) := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj0 : j = 0
  · subst j; simp
  · have hjn := Finset.mem_range.mp hj
    rw [flowCoeff_congr (r + 1) j (fun k hk => h k (by omega)),
      h (n + 1 - 1 - j) (by omega)]

/-- The nonlinear part of the coefficient of degree n+2 in exp(D)z. -/
def flowTail (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range n, ((r + 2).factorial : ℂ)⁻¹ * flowCoeff a (r + 2) (n + 1)

theorem flowTail_congr {a b : ℕ → ℂ} (n : ℕ) (h : ∀ j < n, a j = b j) :
    flowTail a n = flowTail b n := by
  apply Finset.sum_congr rfl
  intro r _
  rw [flowCoeff_congr_tail r n h]

/-- Coefficientwise finite exponential, with index n representing degree n+1. -/
def flowExpCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (n + 1), (r.factorial : ℂ)⁻¹ * flowCoeff a r n

@[simp] theorem flowExpCoeff_zero (a : ℕ → ℂ) : flowExpCoeff a 0 = 1 := by
  simp [flowExpCoeff, flowCoeff]

/-- The unit diagonal makes inversion possible without choosing roots. -/
theorem flowExpCoeff_succ (a : ℕ → ℂ) (n : ℕ) :
    flowExpCoeff a (n + 1) = a n + flowTail a n := by
  unfold flowExpCoeff
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp [flowCoeff, flowTail, Finset.sum_ite_eq']
  ac_rfl

/-- The iterative logarithm of a coordinate whose degree n+2 coefficient is f(n). -/
def iterativeLog (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f n - flowTail (fun j => if _h : j < n then iterativeLog f j else 0) n
termination_by n

/-- All defining coefficients are satisfied, not just a finite jet. -/
theorem iterativeLog_equation (f : ℕ → ℂ) (n : ℕ) :
    flowExpCoeff (iterativeLog f) (n + 1) = f n := by
  rw [flowExpCoeff_succ]
  have ht : flowTail (fun j => if _h : j < n then iterativeLog f j else 0) n =
      flowTail (iterativeLog f) n :=
    flowTail_congr n (fun j hj => dif_pos hj)
  conv_lhs => lhs; rw [iterativeLog]
  rw [ht]
  ring

/-- Uniqueness prevents an arbitrary coefficient family from masquerading as U. -/
theorem iterativeLog_unique (f a : ℕ → ℂ)
    (h : ∀ n, flowExpCoeff a (n + 1) = f n) : a = iterativeLog f := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have ha := h n
    have hb := iterativeLog_equation f n
    rw [flowExpCoeff_succ] at ha hb
    rw [flowTail_congr n ih] at ha
    linear_combination ha - hb

/-- The target log(1+c*z)/c, with the linear coefficient omitted. -/
def logarithmicCoordinate (c : ℂ) (n : ℕ) : ℂ := (-c) ^ (n + 1) / (n + 2)

/-- Huang's A_(n+1), in exactly the normalization of math/0303049 §1. -/
def huangA (n : ℕ) : ℂ :=
  iterativeLog (logarithmicCoordinate (2 * (Real.pi : ℂ) * Complex.I)) n

/-- The full scalar defining equation for Huang's coefficients. -/
theorem huangA_equation (n : ℕ) :
    flowExpCoeff huangA (n + 1) =
      (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (n + 1) / (n + 2) :=
  iterativeLog_equation _ n

@[simp] theorem iterativeLog_zero (f : ℕ → ℂ) : iterativeLog f 0 = f 0 := by
  rw [iterativeLog]
  simp [flowTail]

@[simp] theorem iterativeLog_one (f : ℕ → ℂ) : iterativeLog f 1 = f 1 - (f 0) ^ 2 := by
  have h := iterativeLog_equation f 1
  rw [flowExpCoeff_succ] at h
  norm_num [flowTail, flowCoeff, iterativeLog_zero, Finset.sum_range_succ] at h
  linear_combination h

/-- Huang (1.1). -/
theorem huangA_zero : huangA 0 = -(Real.pi : ℂ) * Complex.I := by
  simp [huangA, logarithmicCoordinate]
  ring

/-- Huang (1.2); the sign differs from a Taylor coefficient of exp. -/
theorem huangA_one : huangA 1 = -(Real.pi : ℂ) ^ 2 / 3 := by
  simp only [huangA, iterativeLog_one, logarithmicCoordinate]
  norm_num
  ring_nf
  simp [Complex.I_sq]
  ring

end VOA.Huang.GenusTwoPoint.Separate
