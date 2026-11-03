import VOA.Huang.GenusTwoPointSepConformal

/-!
# The scalar Witt coefficients of energy conjugation

The nonnegative Virasoro algebra has zero central cocycle. Its locally finite
representations therefore evaluate the same scalar bracket and exponential.
This file does not identify the resulting scalar exponential with Zhu's series.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators

/-- Coefficients of the bracket of two nonnegative Witt tails. -/
def energyWittBracket (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ Finset.antidiagonal n, ((p.1 : ℂ) - p.2) * a p.1 * b p.2

section Representation
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (L : ℕ → Module.End ℂ M)
variable (hL : ∀ x, (Function.support (fun n => L n x)).Finite)

/-- Evaluation of a formal nonnegative Virasoro tail on a truncated module. -/
def energyWittAction (a : ℕ → ℂ) : Module.End ℂ M where
  toFun x := ∑ᶠ n, a n • L n x
  map_add' x y := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib ((hL x).subset (fun n hn hz => hn (by simp only [hz, smul_zero])))
      ((hL y).subset (fun n hn hz => hn (by simp only [hz, smul_zero])))
  map_smul' c x := by
    change (∑ᶠ n, a n • L n (c • x)) = c • ∑ᶠ n, a n • L n x
    rw [smul_finsum' c ((hL x).subset (fun n hn hz => hn (by simp only [hz, smul_zero])))]
    apply finsum_congr
    intro n
    rw [map_smul, smul_comm]

@[simp] theorem energyWittAction_apply (a : ℕ → ℂ) (x : M) :
    energyWittAction L hL a x = ∑ᶠ n, a n • L n x := rfl

include hL in
private theorem weightedSupport (a : ℕ → ℂ) (x : M) :
    (Function.support (fun n => a n • L n x)).Finite :=
  (hL x).subset (fun n hn hz => hn (by simp only [hz, smul_zero]))

include hL in
private theorem compositeSupport (a b : ℕ → ℂ) (x : M) :
    (Function.support (fun p : ℕ × ℕ => (a p.1 * b p.2) • L p.1 (L p.2 x))).Finite := by
  refine ((hL x).biUnion (fun j _ => (hL (L j x)).image (fun i => (i, j)))).subset ?_
  intro p hp
  have hj : L p.2 x ≠ 0 := by intro hz; exact hp (by simp only [hz, map_zero, smul_zero])
  have hi : L p.1 (L p.2 x) ≠ 0 := by intro hz; exact hp (by simp only [hz, smul_zero])
  exact Set.mem_iUnion.mpr ⟨p.2, Set.mem_iUnion.mpr ⟨hj, ⟨p.1, hi, rfl⟩⟩⟩

private theorem energyWittAction_comp (a b : ℕ → ℂ) (x : M) :
    energyWittAction L hL a (energyWittAction L hL b x) =
      ∑ᶠ p : ℕ × ℕ, (a p.1 * b p.2) • L p.1 (L p.2 x) := by
  rw [finsum_curry _ (compositeSupport L hL a b x)]
  simp only [energyWittAction_apply]
  apply finsum_congr
  intro i
  rw [map_finsum _ (weightedSupport L hL b x),
    smul_finsum' _ ((weightedSupport L hL b x).subset (fun j hj hz =>
      hj (by simpa only [map_smul, map_zero] using congrArg (L i) hz)))]
  apply finsum_congr
  intro j
  rw [map_smul, smul_smul]

/-- Evaluation respects the full nonnegative Witt commutator. Joint finiteness
is proved before any interchange of sums. -/
theorem energyWittAction_comm
    (hcomm : ∀ i j x, L i (L j x) - L j (L i x) =
      ((i : ℂ) - j) • L (i + j) x)
    (a b : ℕ → ℂ) :
    conjugationGenerator (energyWittAction L hL a) (energyWittAction L hL a)
      (energyWittAction L hL b) = energyWittAction L hL (energyWittBracket a b) := by
  ext x
  rw [conjugationGenerator_apply, energyWittAction_comp, energyWittAction_comp]
  conv_lhs => rhs; rw [← finsum_comp_equiv (Equiv.prodComm ℕ ℕ)]
  simp only [Equiv.prodComm_apply, Prod.swap]
  have hf := compositeSupport L hL a b x
  have hg : (Function.support (fun p : ℕ × ℕ =>
      (b p.2 * a p.1) • L p.2 (L p.1 x))).Finite :=
    (compositeSupport L hL b a x).preimage (Function.Injective.injOn Prod.swap_injective)
  rw [← finsum_sub_distrib hf hg]
  have he : (fun p : ℕ × ℕ => (a p.1 * b p.2) • L p.1 (L p.2 x) -
      (b p.2 * a p.1) • L p.2 (L p.1 x)) =
      (fun p : ℕ × ℕ => (((p.1 : ℂ) - p.2) * a p.1 * b p.2) • L (p.1 + p.2) x) := by
    funext p
    rw [mul_comm (b p.2), ← smul_sub, hcomm, smul_smul]
    congr 1
    ring
  rw [he, finsum_prod_eq_finsum_antidiagonal_sq _
    (support_pair_smul_add_finite _ _ (hL x))]
  apply finsum_congr
  intro n
  rw [energyWittBracket, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal.mp hp]

end Representation

/-- The coefficient family of the negative logarithmic generator. -/
def energyGenerator (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => -a n

/-- Unnormalized iterated commutators with L(0). -/
def energyWittCoeff (a : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, n => if n = 0 then 1 else 0
  | r + 1, n => energyWittBracket (energyGenerator a) (energyWittCoeff a r) n

/-- An r-fold commutator cannot contain L(n) for n < r. -/
theorem energyWittCoeff_vanish (a : ℕ → ℂ) {r n : ℕ} (h : n < r) :
    energyWittCoeff a r n = 0 := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
    change energyWittBracket _ _ n = 0
    unfold energyWittBracket
    apply Finset.sum_eq_zero
    intro p hp
    have hp := Finset.mem_antidiagonal.mp hp
    cases hzero : p.1 with
    | zero => simp [energyGenerator]
    | succ k => rw [ih (by omega), mul_zero]

/-- The coefficient of L(n) in the finite Hadamard exponential. -/
def energyExpCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (n + 1), (r.factorial : ℂ)⁻¹ * energyWittCoeff a r n

section Exponential
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (L : ℕ → Module.End ℂ M)
variable (hL : ∀ x, (Function.support (fun n => L n x)).Finite)
variable (hcomm : ∀ i j x, L i (L j x) - L j (L i x) =
  ((i : ℂ) - j) • L (i + j) x)

private theorem energyWittAction_initial (a : ℕ → ℂ) :
    energyWittAction L hL (energyWittCoeff a 0) = L 0 := by
  ext x
  rw [energyWittAction_apply, finsum_eq_single _ 0]
  · simp [energyWittCoeff]
  · intro n hn
    simp [energyWittCoeff, hn]

include hcomm in
/-- All iterated operator commutators reduce to scalar Witt coefficients. -/
theorem energyWittCoeff_evaluate (a : ℕ → ℂ) (r : ℕ) :
    (conjugationGenerator (energyWittAction L hL (energyGenerator a))
      (energyWittAction L hL (energyGenerator a)) ^ r) (L 0) =
      energyWittAction L hL (energyWittCoeff a r) := by
  induction r with
  | zero => exact (energyWittAction_initial L hL a).symm
  | succ r ih =>
    rw [VOA.pow_succ'_apply, ih, energyWittAction_comm L hL hcomm]
    rfl

include hcomm in
/-- The exact scalar answer to energy conjugation in every locally finite
nonnegative Virasoro representation. This is independent of the VOA. -/
theorem energy_conjugation_eq (a : ℕ → ℂ)
    (hD : IsLocNilp (energyWittAction L hL (energyGenerator a))) (x : M) :
    expFun hD (L 0 (expFun hD.neg x)) =
      energyWittAction L hL (energyExpCoeff a) x := by
  rw [expFun_conjugation_eq_finsum hD hD]
  have he : ∀ r, conjugationCoeff (energyWittAction L hL (energyGenerator a))
      (energyWittAction L hL (energyGenerator a)) (L 0) r x =
      ∑ᶠ n, ((r.factorial : ℂ)⁻¹ * energyWittCoeff a r n) • L n x := by
    intro r
    simp only [conjugationCoeff, linearFlowCoeff, energyWittCoeff_evaluate L hL hcomm,
      LinearMap.smul_apply, energyWittAction_apply]
    rw [smul_finsum' _ (weightedSupport L hL _ x)]
    apply finsum_congr
    intro n
    rw [smul_smul]
  simp_rw [he]
  have hf : (Function.support (fun p : ℕ × ℕ =>
      ((p.1.factorial : ℂ)⁻¹ * energyWittCoeff a p.1 p.2) • L p.2 x)).Finite := by
    refine ((hL x).biUnion (fun n _ => (Set.finite_Iic n).image (fun r => (r, n)))).subset ?_
    intro p hp
    have hn : L p.2 x ≠ 0 := by intro hz; exact hp (by simp only [hz, smul_zero])
    have hr : p.1 ≤ p.2 := by
      by_contra h
      exact hp (by
        dsimp only
        rw [energyWittCoeff_vanish a (by omega), mul_zero, zero_smul])
    exact Set.mem_iUnion.mpr ⟨p.2, Set.mem_iUnion.mpr ⟨hn, ⟨p.1, hr, rfl⟩⟩⟩
  rw [← finsum_curry _ hf, ← finsum_comp_equiv (Equiv.prodComm ℕ ℕ)]
  have hs := hf.preimage (Function.Injective.injOn Prod.swap_injective)
  simp only [Equiv.prodComm_apply, Prod.swap]
  change (Function.support (fun p : ℕ × ℕ =>
    ((p.2.factorial : ℂ)⁻¹ * energyWittCoeff a p.2 p.1) • L p.1 x)).Finite at hs
  rw [finsum_curry _ hs]
  apply finsum_congr
  intro n
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1)) _ (by
    intro r hr
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    exact hr (by
      dsimp only
      rw [energyWittCoeff_vanish a (by omega), mul_zero, zero_smul]))]
  simp only [energyExpCoeff, Finset.sum_smul]

end Exponential
/-- The nonlinear third coefficient detects the positive-mode commutator. -/
theorem energyExpCoeff_three (a : ℕ → ℂ) :
    energyExpCoeff a 3 = -3 * a 2 - (1 / 2 : ℂ) * a 0 * a 1 := by
  norm_num [energyExpCoeff, energyWittCoeff, energyWittBracket, energyGenerator,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  ring

end VOA.Huang.GenusTwoPoint.Separate
