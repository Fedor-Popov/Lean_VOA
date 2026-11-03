import VOA.Huang.GenusTwoPointSepEnergyWitt

/-! # The scalar energy flow as a formal vector-field adjoint action -/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators

/-- Formal vector field for the iterated energy commutator. -/
def energyFlowSeries (a : ℕ → ℂ) (r : ℕ) : PowerSeries ℂ :=
  PowerSeries.X * PowerSeries.mk (energyWittCoeff a r)

@[simp] theorem coeff_energyFlowSeries (a : ℕ → ℂ) (r n : ℕ) :
    PowerSeries.coeff (n + 1) (energyFlowSeries a r) = energyWittCoeff a r n := by
  simp [energyFlowSeries, PowerSeries.coeff_succ_X_mul]

@[simp] theorem energyFlowSeries_zero (a : ℕ → ℂ) :
    energyFlowSeries a 0 = PowerSeries.X := by
  ext n
  cases n with
  | zero => simp [energyFlowSeries]
  | succ n => simp [coeff_energyFlowSeries, energyWittCoeff, PowerSeries.coeff_X]

/-- The scalar Witt bracket is the Euler-derivative commutator. -/
theorem energyWittBracket_series (a b : ℕ → ℂ) :
    PowerSeries.mk (energyWittBracket a b) =
      (PowerSeries.X * PowerSeries.derivative ℂ (PowerSeries.mk a)) * PowerSeries.mk b -
      PowerSeries.mk a * (PowerSeries.X * PowerSeries.derivative ℂ (PowerSeries.mk b)) := by
  ext n
  rw [PowerSeries.coeff_mk, map_sub]
  conv_rhs => lhs; rw [PowerSeries.coeff_mul]
  conv_rhs => rhs; rw [PowerSeries.coeff_mul]
  rw [← Finset.sum_sub_distrib]
  unfold energyWittBracket
  apply Finset.sum_congr rfl
  intro p _
  have he (c : ℕ → ℂ) (k : ℕ) : PowerSeries.coeff k
      (PowerSeries.X * PowerSeries.derivative ℂ (PowerSeries.mk c)) = (k : ℂ) * c k := by
    cases k with
    | zero => simp
    | succ k => simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, mul_comm]
  rw [he, he]
  simp only [PowerSeries.coeff_mk]
  ring

@[simp] theorem energyGenerator_series (a : ℕ → ℂ) :
    PowerSeries.mk (energyGenerator a) = -PowerSeries.X * PowerSeries.mk a := by
  ext n
  cases n with
  | zero => simp [energyGenerator]
  | succ n => simp [energyGenerator, PowerSeries.coeff_succ_X_mul]

/-- The ordinary coordinate vector field. -/
def coordinateVectorField (a : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.X ^ 2 * PowerSeries.mk a

/-- Exact scalar commutator recurrence, with its sign determined by Virasoro. -/
theorem energyFlowSeries_succ (a : ℕ → ℂ) (r : ℕ) :
    energyFlowSeries a (r + 1) =
      coordinateVectorField a * PowerSeries.derivative ℂ (energyFlowSeries a r) -
      PowerSeries.derivative ℂ (coordinateVectorField a) * energyFlowSeries a r := by
  have h : (fun n => energyWittCoeff a (r + 1) n) =
      energyWittBracket (energyGenerator a) (energyWittCoeff a r) := rfl
  simp only [energyFlowSeries, h, energyWittBracket_series, energyGenerator_series,
    coordinateVectorField, pow_two, map_neg, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_X]
  ring

/-- The coordinate and energy recurrences satisfy a product rule: the extra
Jacobian terms cancel exactly. -/
theorem energyFlow_product_step (a : ℕ → ℂ) (i j : ℕ) :
    coordinateVectorField a * PowerSeries.derivative ℂ
      (energyFlowSeries a i * PowerSeries.derivative ℂ (flowSeries a j)) =
      energyFlowSeries a (i + 1) * PowerSeries.derivative ℂ (flowSeries a j) +
      energyFlowSeries a i * PowerSeries.derivative ℂ (flowSeries a (j + 1)) := by
  rw [energyFlowSeries_succ, flowSeries_succ]
  have he : PowerSeries.X ^ 2 *
      (PowerSeries.derivative ℂ (flowSeries a j) * PowerSeries.mk a) =
      coordinateVectorField a * PowerSeries.derivative ℂ (flowSeries a j) := by
    unfold coordinateVectorField
    ring
  rw [he]
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-- The binomial convolution identity before evaluating the flow parameter.
This is the formal identity G(t,x) times the x-derivative of F(t,x) = F(t,x). -/
theorem energyFlow_jacobian_coeff (a : ℕ → ℂ) (r : ℕ) :
    flowSeries a r = ∑ i ∈ Finset.range (r + 1), (r.choose i : ℂ) •
      (energyFlowSeries a i * PowerSeries.derivative ℂ (flowSeries a (r - i))) := by
  induction r with
  | zero => simp [PowerSeries.derivative_X]
  | succ r ih =>
    have he : flowSeries a (r + 1) =
        coordinateVectorField a * PowerSeries.derivative ℂ (flowSeries a r) := by
      rw [flowSeries_succ]
      unfold coordinateVectorField
      ring
    rw [he, ih, map_sum, Finset.mul_sum]
    have hs : ∀ i ∈ Finset.range (r + 1),
        coordinateVectorField a * PowerSeries.derivative ℂ
          ((r.choose i : ℂ) • (energyFlowSeries a i *
            PowerSeries.derivative ℂ (flowSeries a (r - i)))) =
        (r.choose i : ℂ) • (energyFlowSeries a (i + 1) *
          PowerSeries.derivative ℂ (flowSeries a ((r + 1) - (i + 1)))) +
        (r.choose i : ℂ) • (energyFlowSeries a i *
          PowerSeries.derivative ℂ (flowSeries a ((r + 1) - i))) := by
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Derivation.map_smul, mul_smul_comm, energyFlow_product_step, smul_add]
      rw [show r + 1 - (i + 1) = r - i by omega,
        show r + 1 - i = r - i + 1 by omega]
    rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib]
    exact pascal_resum r (fun i => energyFlowSeries a i *
      PowerSeries.derivative ℂ (flowSeries a (r + 1 - i)))


/-- Sum in the flow parameter, with coefficients summed algebraically. -/
def energyFlowSum (f : ℕ → PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => ∑ᶠ r, PowerSeries.coeff n (f r))

private theorem flowSum_support (f : ℕ → PowerSeries ℂ)
    (hf : ∀ r n, n < r → PowerSeries.coeff n (f r) = 0) (n : ℕ) :
    (Function.support (fun r => PowerSeries.coeff n (f r))).Finite := by
  refine (Set.finite_Iic n).subset fun r hr => ?_
  by_contra h
  exact hr (hf r n (by simpa using h))

private theorem flowSum_pair_support (f g : ℕ → PowerSeries ℂ)
    (hf : ∀ r n, n < r → PowerSeries.coeff n (f r) = 0)
    (hg : ∀ r n, n < r → PowerSeries.coeff n (g r) = 0) (n : ℕ) :
    (Function.support (fun p : ℕ × ℕ => PowerSeries.coeff n (f p.1 * g p.2))).Finite := by
  refine ((Set.finite_Iic n).prod (Set.finite_Iic n)).subset fun p hp => ?_
  have he : ∃ q ∈ Finset.antidiagonal n,
      PowerSeries.coeff q.1 (f p.1) * PowerSeries.coeff q.2 (g p.2) ≠ 0 := by
    apply Finset.exists_ne_zero_of_sum_ne_zero
    simpa only [PowerSeries.coeff_mul] using hp
  obtain ⟨q, hq, hne⟩ := he
  have hq := Finset.mem_antidiagonal.mp hq
  have h1 : p.1 ≤ q.1 := by
    by_contra h
    exact hne (by rw [hf _ _ (by omega), zero_mul])
  have h2 : p.2 ≤ q.2 := by
    by_contra h
    exact hne (by rw [hg _ _ (by omega), mul_zero])
  change p.1 ≤ n ∧ p.2 ≤ n
  omega

/-- Coefficientwise evaluation at flow time one respects convolution.
The order bounds justify both exchanges of infinite-index finite sums. -/
theorem energyFlowSum_mul (f g : ℕ → PowerSeries ℂ)
    (hf : ∀ r n, n < r → PowerSeries.coeff n (f r) = 0)
    (hg : ∀ r n, n < r → PowerSeries.coeff n (g r) = 0) :
    energyFlowSum (fun r => ∑ p ∈ Finset.antidiagonal r, f p.1 * g p.2) =
      energyFlowSum f * energyFlowSum g := by
  ext n
  simp only [energyFlowSum, PowerSeries.coeff_mk, map_sum]
  rw [finsum_antidiagonal _ (flowSum_pair_support f g hf hg n)]
  simp only [PowerSeries.coeff_mul]
  rw [finsum_sum_comm]
  · apply Finset.sum_congr rfl
    intro q hq
    have hfin : (Function.support (fun p : ℕ × ℕ =>
        PowerSeries.coeff q.1 (f p.1) * PowerSeries.coeff q.2 (g p.2))).Finite := by
      refine ((flowSum_support f hf q.1).prod (flowSum_support g hg q.2)).subset ?_
      intro p hp
      exact ⟨fun hz => hp (by simp only [hz, zero_mul]),
        fun hz => hp (by simp only [hz, mul_zero])⟩
    rw [finsum_curry _ hfin]
    simp only [← mul_finsum, ← finsum_mul, PowerSeries.coeff_mk]
  · intro q hq
    refine ((flowSum_support f hf q.1).prod (flowSum_support g hg q.2)).subset ?_
    intro p hp
    exact ⟨fun hz => hp (by simp only [hz, zero_mul]),
      fun hz => hp (by simp only [hz, mul_zero])⟩

private theorem flowSeries_order (a : ℕ → ℂ) (r n : ℕ) (hn : n < r) :
    PowerSeries.coeff n (flowSeries a r) = 0 := by
  cases n with
  | zero => simp [flowSeries]
  | succ n => rw [coeff_flowSeries, flowCoeff_vanish a (by omega)]

private theorem energyFlowSeries_order (a : ℕ → ℂ) (r n : ℕ) (hn : n < r) :
    PowerSeries.coeff n (energyFlowSeries a r) = 0 := by
  cases n with
  | zero => simp [energyFlowSeries]
  | succ n => rw [coeff_energyFlowSeries, energyWittCoeff_vanish a (by omega)]

/-- The evaluated energy vector field. -/
def energyExponential (a : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.X * PowerSeries.mk (energyExpCoeff a)

private theorem energyFlowSum_energy (a : ℕ → ℂ) :
    energyFlowSum (fun r => (r.factorial : ℂ)⁻¹ • energyFlowSeries a r) =
      energyExponential a := by
  ext n
  cases n with
  | zero => simp [energyFlowSum, energyFlowSeries, energyExponential]
  | succ n =>
    simp only [energyFlowSum, PowerSeries.coeff_mk, map_smul, smul_eq_mul,
      coeff_energyFlowSeries, energyExponential, PowerSeries.coeff_succ_X_mul]
    apply finsum_eq_sum_of_support_subset
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    exact hr (by dsimp only; rw [energyWittCoeff_vanish a (by omega), mul_zero])

private theorem energyFlowSum_coordinate (a : ℕ → ℂ) :
    energyFlowSum (fun r => (r.factorial : ℂ)⁻¹ • flowSeries a r) = flowExponential a := by
  ext n
  cases n with
  | zero => simp [energyFlowSum, flowSeries, flowExponential]
  | succ n =>
    simp only [energyFlowSum, PowerSeries.coeff_mk, map_smul, smul_eq_mul,
      coeff_flowSeries, flowExponential, PowerSeries.coeff_succ_X_mul]
    apply finsum_eq_sum_of_support_subset
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    exact hr (by dsimp only; rw [flowCoeff_vanish a (by omega), mul_zero])

private theorem energyFlowSum_derivative (a : ℕ → ℂ) :
    energyFlowSum (fun r => (r.factorial : ℂ)⁻¹ •
      PowerSeries.derivative ℂ (flowSeries a r)) =
      PowerSeries.derivative ℂ (flowExponential a) := by
  ext n
  simp only [energyFlowSum, PowerSeries.coeff_mk, map_smul, smul_eq_mul,
    PowerSeries.coeff_derivative, flowExponential, PowerSeries.coeff_succ_X_mul,
    coeff_flowSeries]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1)) _ (by
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    exact hr (by dsimp only; rw [flowCoeff_vanish a (by omega), zero_mul, mul_zero]))]
  simp only [flowExpCoeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The full formal Jacobian identity for arbitrary positive coordinate coefficients. -/
theorem energyExponential_mul_derivative (a : ℕ → ℂ) :
    energyExponential a * PowerSeries.derivative ℂ (flowExponential a) =
      flowExponential a := by
  let f := fun r => (r.factorial : ℂ)⁻¹ • energyFlowSeries a r
  let g := fun r => (r.factorial : ℂ)⁻¹ • PowerSeries.derivative ℂ (flowSeries a r)
  have hf : ∀ r n, n < r → PowerSeries.coeff n (f r) = 0 := by
    intro r n hn
    simp [f, energyFlowSeries_order a r n hn]
  have hg : ∀ r n, n < r → PowerSeries.coeff n (g r) = 0 := by
    intro r n hn
    simp [g, PowerSeries.coeff_derivative, coeff_flowSeries, flowCoeff_vanish a hn]
  rw [← energyFlowSum_energy, ← energyFlowSum_derivative, ← energyFlowSum_mul f g hf hg]
  have he : (fun r => ∑ p ∈ Finset.antidiagonal r, f p.1 * g p.2) =
      (fun r => (r.factorial : ℂ)⁻¹ • flowSeries a r) := by
    funext r
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    conv_rhs => arg 2; rw [energyFlow_jacobian_coeff a r]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi := Finset.mem_range.mp hi
    simp only [f, g, smul_mul_assoc, mul_smul_comm, smul_smul,
      fact_choose r i (by omega)]
    rw [mul_comm]
  rw [he, energyFlowSum_coordinate]

end VOA.Huang.GenusTwoPoint.Separate
