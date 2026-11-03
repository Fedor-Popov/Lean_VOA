import VOA.Classification.COne.OrbIcoChan1

/-! # OrbIco: the Leibniz rule for the annihilation exponential `E⁺(β)`

`E⁺(β, z) = exp(-Σ β(n) z^{-n}/n)` is the exponential of a derivation of the polynomial Fock
algebra, hence multiplicative. In components:

`aExpVec_mul`: `E⁺(β)_{-N}(x y) = Σ_{k ≤ N} E⁺(β)_{-k} x · E⁺(β)_{-(N-k)} y`.

`aExpVec_vSchur_mul`: on a product of two Schur states of total degree `N`, the vacuum part of
`E⁺(β)_{-N}` is `gco(p) · gco(r)`.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA HeisenbergN VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice Finset OrbPrim

variable (L : IntegralLattice)

/-- The recursion of `aExpVec`, multiplied out. -/
theorem aExpVec_succ_smul (β : L.carrier) (k : ℕ) (x : FockN (rank L)) :
    ((k + 1 : ℕ) : ℂ) • aExpVec L β (k + 1) x =
      ∑ m ∈ range (k + 1), -(chargeOsc L β ((m : ℤ) + 1) (aExpVec L β (k - m) x)) := by
  rw [aExpVec_succ, LinearMap.smul_apply, smul_smul]
  rw [show ((k + 1 : ℕ) : ℂ) * ((k : ℂ) + 1)⁻¹ = 1 by
    push_cast; exact mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero k), one_smul,
    LinearMap.coe_sum, Finset.sum_apply]
  rfl

theorem negOsc_mul (β : L.carrier) (m : ℕ) (x y : FockN (rank L)) :
    -(chargeOsc L β ((m : ℤ) + 1) (x * y)) =
      -(chargeOsc L β ((m : ℤ) + 1) x) * y + x * -(chargeOsc L β ((m : ℤ) + 1) y) := by
  rw [WpC2.chargeOsc_mul' L β (by omega)]
  ring

/-- **Leibniz rule for `E⁺(β)`.** -/
theorem aExpVec_mul (β : L.carrier) : ∀ (N : ℕ) (x y : FockN (rank L)),
    aExpVec L β N (x * y) =
      ∑ k ∈ range (N + 1), aExpVec L β k x * aExpVec L β (N - k) y := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x y
  rcases N with _ | N
  · simp [aExpVec_zero]
  set A := fun k (z : FockN (rank L)) => aExpVec L β k z with hA
  set D := fun (m : ℕ) (z : FockN (rank L)) => -(chargeOsc L β ((m : ℤ) + 1) z) with hD
  have hrec : ∀ (k : ℕ) (z : FockN (rank L)),
      ((k + 1 : ℕ) : ℂ) • A (k + 1) z = ∑ m ∈ range (k + 1), D m (A (k - m) z) :=
    fun k z => aExpVec_succ_smul L β k z
  have hNz : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  apply smul_right_injective _ hNz
  simp only
  change ((N + 1 : ℕ) : ℂ) • A (N + 1) (x * y) =
    ((N + 1 : ℕ) : ℂ) • ∑ k ∈ range (N + 1 + 1), A k x * A (N + 1 - k) y
  rw [hrec]
  -- expand with the induction hypothesis and the derivation property
  have h1 : ∑ m ∈ range (N + 1), D m (A (N - m) (x * y)) =
      ∑ m ∈ range (N + 1), ∑ k ∈ range (N + 1 - m),
        (D m (A k x) * A (N - m - k) y + A k x * D m (A (N - m - k) y)) := by
    refine sum_congr rfl fun m hm => ?_
    have hm' : m < N + 1 := mem_range.mp hm
    rw [show A (N - m) (x * y) = ∑ k ∈ range (N - m + 1), A k x * A (N - m - k) y from
      ih (N - m) (by omega) x y, show N + 1 - m = N - m + 1 by omega]
    simp only [hD]
    rw [map_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    exact negOsc_mul L β m _ _
  rw [h1]
  simp only [sum_add_distrib]
  -- first part
  have hS1 : ∑ m ∈ range (N + 1), ∑ k ∈ range (N + 1 - m), D m (A k x) * A (N - m - k) y =
      ∑ i ∈ range (N + 1), (((i + 1 : ℕ) : ℂ) • A (i + 1) x) * A (N - i) y := by
    rw [← sum_range_diag_flip (N + 1) (fun m k => D m (A k x) * A (N - m - k) y)]
    refine sum_congr rfl fun i hi => ?_
    rw [hrec, sum_mul]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < i + 1 := mem_range.mp hj
    rw [show N - j - (i - j) = N - i by omega]
  -- second part
  have hS2 : ∑ m ∈ range (N + 1), ∑ k ∈ range (N + 1 - m), A k x * D m (A (N - m - k) y) =
      ∑ i ∈ range (N + 1), A (N - i) x * (((i + 1 : ℕ) : ℂ) • A (i + 1) y) := by
    have hrefl : ∀ m ∈ range (N + 1),
        ∑ k ∈ range (N + 1 - m), A k x * D m (A (N - m - k) y) =
          ∑ l ∈ range (N + 1 - m), A (N - m - l) x * D m (A l y) := by
      intro m hm
      have hm' : m < N + 1 := mem_range.mp hm
      rw [← sum_range_reflect (fun l => A (N - m - l) x * D m (A l y)) (N + 1 - m)]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k < N + 1 - m := mem_range.mp hk
      rw [show N + 1 - m - 1 - k = N - m - k by omega, show N - m - (N - m - k) = k by omega]
    rw [sum_congr rfl hrefl,
      ← sum_range_diag_flip (N + 1) (fun m l => A (N - m - l) x * D m (A l y))]
    refine sum_congr rfl fun i hi => ?_
    rw [hrec, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < i + 1 := mem_range.mp hj
    rw [show N - j - (i - j) = N - i by omega]
  rw [hS1, hS2]
  -- the target
  have hT : ((N + 1 : ℕ) : ℂ) • ∑ k ∈ range (N + 1 + 1), A k x * A (N + 1 - k) y =
      ∑ k ∈ range (N + 1 + 1), ((k : ℕ) : ℂ) • (A k x * A (N + 1 - k) y) +
      ∑ k ∈ range (N + 1 + 1), (((N + 1 - k : ℕ) : ℂ)) • (A k x * A (N + 1 - k) y) := by
    rw [smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k < N + 1 + 1 := mem_range.mp hk
    rw [← add_smul]
    congr 1
    push_cast [Nat.cast_sub (show k ≤ N + 1 by omega)]
    ring
  have e1 : ∑ k ∈ range (N + 1 + 1), ((k : ℕ) : ℂ) • (A k x * A (N + 1 - k) y) =
      ∑ i ∈ range (N + 1), (((i + 1 : ℕ) : ℂ) • A (i + 1) x) * A (N - i) y := by
    rw [sum_range_succ']
    rw [show ((0 : ℕ) : ℂ) = 0 by simp, zero_smul, add_zero]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i < N + 1 := mem_range.mp hi
    rw [show N + 1 - (i + 1) = N - i by omega, smul_mul_assoc]
  have e2 : ∑ k ∈ range (N + 1 + 1), (((N + 1 - k : ℕ) : ℂ)) • (A k x * A (N + 1 - k) y) =
      ∑ i ∈ range (N + 1), A (N - i) x * (((i + 1 : ℕ) : ℂ) • A (i + 1) y) := by
    rw [sum_range_succ, Nat.sub_self, show ((0 : ℕ) : ℂ) = 0 by simp, zero_smul, add_zero]
    rw [← sum_range_reflect _ (N + 1)]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i < N + 1 := mem_range.mp hi
    rw [show N + 1 - 1 - i = N - i by omega, show N + 1 - (N - i) = i + 1 by omega,
      mul_smul_comm]
  rw [hT, e1, e2]

/-- `E⁺(β)_{-k}` kills a Schur state of smaller degree. -/
theorem aExpVec_vSchur_of_lt (α β : L.carrier) {k N : ℕ} (h : N < k) :
    aExpVec L β k (vSchur L α N) = 0 := by
  have hm := aExpVec_mem_gradingZN L β k (Screen.vSchur_mem_gradingWN L α N)
  rwa [gradingZN_of_neg (by omega), Submodule.mem_bot] at hm

/-- The vacuum part of `E⁺(β)_{-(p+r)}` on `S_p(α) S_r(α)`. -/
theorem aExpVec_vSchur_mul (hPos : L.PosDef) (α β : L.carrier) (p r : ℕ) :
    aExpVec L β (p + r) (vSchur L α p * vSchur L α r) =
      (gco ((L.form α β : ℤ) : ℂ) p * gco ((L.form α β : ℤ) : ℂ) r) • vacuumN (rank L) := by
  rw [aExpVec_mul, sum_eq_single p]
  · rw [aExpVec_vSchur L hPos α β p p le_rfl, show p + r - p = r by omega,
      aExpVec_vSchur L hPos α β r r le_rfl, Nat.sub_self, Nat.sub_self, vSchur_zero,
      smul_mul_smul_comm, one_mul]
    rfl
  · intro k hk hkp
    have hk' : k < p + r + 1 := mem_range.mp hk
    rcases lt_or_gt_of_ne hkp with hlt | hgt
    · rw [aExpVec_vSchur_of_lt L α β (show r < p + r - k by omega), mul_zero]
    · rw [aExpVec_vSchur_of_lt L α β hgt, zero_mul]
  · intro hp; exact absurd (mem_range.mpr (by omega)) hp

end VOA.Classification.COne.OrbIco
