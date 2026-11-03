import VOA.Classification.COne.QExpWeightTwoAnalytic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# A theta logarithmic derivative for the weight-one construction

Mathlib's two-variable theta is the even theta function. The correction
`-α` makes its logarithmic derivative covariant under S and invariant under
integral shifts of the two coordinates. T and T squared also act explicitly.
These identities do not identify this function with `weightOneQSeries`.
-/

open Complex
open scoped UpperHalfPlane MatrixGroups

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Logarithmic derivative in the elliptic variable, wherever theta is nonzero. -/
def weightOneThetaLog (z τ : ℂ) : ℂ := jacobiTheta₂' z τ / jacobiTheta₂ z τ

/-- The normalized corrected logarithmic derivative at `α * τ + β`.
For the odd theta convention use `α = a/N - 1/2`, `β = b/N - 1/2`. -/
def weightOneThetaValue (α β τ : ℂ) : ℂ :=
  -α - weightOneThetaLog (α * τ + β) τ / (2 * Real.pi * I)

/-- S transformation, obtained by cancelling Mathlib's common theta factor. -/
theorem weightOneThetaLog_S (z τ : ℂ) (hτ : τ ≠ 0)
    (hz : jacobiTheta₂ z τ ≠ 0) :
    weightOneThetaLog (z / τ) (-1 / τ) =
      τ * weightOneThetaLog z τ + 2 * Real.pi * I * z := by
  let A : ℂ := 1 / (-I * τ) ^ (1 / 2 : ℂ) * cexp (-Real.pi * I * z ^ 2 / τ)
  have he : jacobiTheta₂ z τ = A * jacobiTheta₂ (z / τ) (-1 / τ) :=
    jacobiTheta₂_functional_equation z τ
  have hd : jacobiTheta₂' z τ = A / τ *
      (jacobiTheta₂' (z / τ) (-1 / τ) -
        2 * Real.pi * I * z * jacobiTheta₂ (z / τ) (-1 / τ)) :=
    jacobiTheta₂'_functional_equation z τ
  have hprod : A * jacobiTheta₂ (z / τ) (-1 / τ) ≠ 0 := he ▸ hz
  obtain ⟨hA, hnew⟩ := mul_ne_zero_iff.mp hprod
  unfold weightOneThetaLog
  rw [he, hd]
  generalize jacobiTheta₂' (z / τ) (-1 / τ) = v
  generalize hu : jacobiTheta₂ (z / τ) (-1 / τ) = u at *
  field_simp
  ring

/-- Elliptic period one for the logarithmic derivative. -/
theorem weightOneThetaLog_add_one (z τ : ℂ) :
    weightOneThetaLog (z + 1) τ = weightOneThetaLog z τ := by
  simp only [weightOneThetaLog, jacobiTheta₂'_add_left, jacobiTheta₂_add_left]

/-- Elliptic quasi-period tau for the logarithmic derivative. -/
theorem weightOneThetaLog_add_tau (z τ : ℂ) (hz : jacobiTheta₂ z τ ≠ 0) :
    weightOneThetaLog (z + τ) τ = weightOneThetaLog z τ - 2 * Real.pi * I := by
  simp only [weightOneThetaLog, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _), sub_div, mul_div_cancel_right₀ _ hz]

/-- The parity calculation needed for T (not only T squared). -/
theorem weightOneThetaTerm_T (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term n z (τ + 1) = jacobiTheta₂_term n (z + 1 / 2) τ := by
  obtain ⟨m, hm⟩ := n.even_mul_pred_self
  have hi : n ^ 2 - n = 2 * m := by nlinarith [hm]
  have hc : (n : ℂ) ^ 2 - n = 2 * (m : ℂ) := by exact_mod_cast hi
  unfold jacobiTheta₂_term
  calc
    _ = cexp (2 * Real.pi * I * n * (z + 1 / 2) + Real.pi * I * n ^ 2 * τ) *
        cexp ((m : ℂ) * (2 * Real.pi * I)) := by
      rw [← Complex.exp_add]
      congr 1
      linear_combination (Real.pi * I : ℂ) * hc
    _ = _ := by rw [exp_int_mul_two_pi_mul_I, mul_one]

theorem weightOneTheta_T (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  exact tsum_congr (fun n => weightOneThetaTerm_T n z τ)

theorem weightOneThetaDeriv_T (z τ : ℂ) :
    jacobiTheta₂' z (τ + 1) = jacobiTheta₂' (z + 1 / 2) τ := by
  unfold jacobiTheta₂' jacobiTheta₂'_term
  exact tsum_congr (fun n => congrArg (fun x : ℂ => 2 * Real.pi * I * n * x)
    (weightOneThetaTerm_T n z τ))

/-- T acts on the shifted coordinates by `(α, β) ↦ (α, β + α + 1/2)`. -/
theorem weightOneThetaValue_T (α β τ : ℂ) :
    weightOneThetaValue α β (τ + 1) =
      weightOneThetaValue α (β + α + 1 / 2) τ := by
  simp only [weightOneThetaValue, weightOneThetaLog, weightOneThetaDeriv_T, weightOneTheta_T]
  rw [show α * (τ + 1) + β + 1 / 2 = α * τ + (β + α + 1 / 2) by ring]

/-- T squared requires no nonvanishing assumption. -/
theorem weightOneThetaValue_T_sq (α β τ : ℂ) :
    weightOneThetaValue α β (τ + 2) = weightOneThetaValue α (β + 2 * α) τ := by
  simp only [weightOneThetaValue, weightOneThetaLog,
    jacobiTheta₂'_add_right, jacobiTheta₂_add_right]
  rw [show α * (τ + 2) + β = α * τ + (β + 2 * α) by ring]

/-- The normalized correction exactly cancels the inhomogeneous S term. -/
theorem weightOneThetaValue_S (α β τ : ℂ) (hτ : τ ≠ 0)
    (hz : jacobiTheta₂ (β * τ - α) τ ≠ 0) :
    weightOneThetaValue α β (-1 / τ) = τ * weightOneThetaValue β (-α) τ := by
  have he : α * (-1 / τ) + β = (β * τ - α) / τ := by field_simp; ring
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold weightOneThetaValue
  rw [he, weightOneThetaLog_S _ _ hτ hz]
  simp only [sub_eq_add_neg]
  field_simp
  ring

/-- A unit shift of the second coordinate leaves the corrected value unchanged. -/
theorem weightOneThetaValue_add_one_right (α β τ : ℂ) :
    weightOneThetaValue α (β + 1) τ = weightOneThetaValue α β τ := by
  simp only [weightOneThetaValue, ← add_assoc, weightOneThetaLog_add_one]

/-- A unit shift of the first coordinate also leaves the corrected value unchanged. -/
theorem weightOneThetaValue_add_one_left (α β τ : ℂ)
    (hz : jacobiTheta₂ (α * τ + β) τ ≠ 0) :
    weightOneThetaValue (α + 1) β τ = weightOneThetaValue α β τ := by
  have he : (α + 1) * τ + β = (α * τ + β) + τ := by ring
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold weightOneThetaValue
  rw [he, weightOneThetaLog_add_tau _ _ hz]
  field_simp
  ring

/-- The standard primitive root used in the theta Fourier identity. -/
def weightOneStandardRoot (N : ℕ) : ℂ := cexp (2 * Real.pi * I / N)

/-- Missing analytic Fourier identity, including the nonzero denominator.
For positive N this is the classical odd-theta logarithmic-derivative formula.
The zero torsion point is excluded because theta vanishes there. This is a
named input, not a proved theorem. Only the standard primitive root is used. -/
def WeightOneThetaFourier (N : ℕ) : Prop :=
  ∀ a b : Fin N, ¬(a.val = 0 ∧ b.val = 0) → ∀ τ : ℍ,
    jacobiTheta₂ (((a.val : ℂ) / N - 1 / 2) * τ +
      ((b.val : ℂ) / N - 1 / 2)) τ ≠ 0 ∧
    weightOneQSeries N (weightOneStandardRoot N) a b τ =
      weightOneScale N (weightOneStandardRoot N) a b *
        weightOneThetaValue ((a.val : ℂ) / N - 1 / 2) ((b.val : ℂ) / N - 1 / 2) τ

/-- Concrete S transformation from the analytic bridge, for a positive first
index. The boundary a=0 and arbitrary primitive roots are not claimed here. -/
theorem weightOneQSeries_S_of_thetaFourier {N : ℕ} (hN : 0 < N)
    (hfourier : WeightOneThetaFourier N) (a b : Fin N) (ha : 0 < a.val) (τ : ℍ) :
    let aNeg : Fin N := ⟨N - a.val, by omega⟩
    weightOneQSeries N (weightOneStandardRoot N) a b (ModularGroup.S • τ) =
      (weightOneScale N (weightOneStandardRoot N) a b /
        weightOneScale N (weightOneStandardRoot N) b aNeg) * (τ : ℂ) *
        weightOneQSeries N (weightOneStandardRoot N) b aNeg τ := by
  dsimp only
  let aNeg : Fin N := ⟨N - a.val, by omega⟩
  change weightOneQSeries N (weightOneStandardRoot N) a b (ModularGroup.S • τ) =
    (weightOneScale N (weightOneStandardRoot N) a b /
      weightOneScale N (weightOneStandardRoot N) b aNeg) * (τ : ℂ) *
      weightOneQSeries N (weightOneStandardRoot N) b aNeg τ
  have hab : ¬(a.val = 0 ∧ b.val = 0) := by omega
  have hba : ¬(b.val = 0 ∧ aNeg.val = 0) := by
    have : aNeg.val = N - a.val := rfl
    have := a.isLt
    omega
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hneg : (aNeg.val : ℂ) / N - 1 / 2 = -((a.val : ℂ) / N - 1 / 2) := by
    change ((N - a.val : ℕ) : ℂ) / N - 1 / 2 = _
    rw [Nat.cast_sub a.isLt.le]
    field_simp
    ring
  obtain ⟨hz, ht⟩ := hfourier b aNeg hba τ
  have hs := (hfourier a b hab (ModularGroup.S • τ)).2
  have hζ : IsPrimitiveRoot (weightOneStandardRoot N) N :=
    Complex.isPrimitiveRoot_exp N hN.ne'
  have hscale := weightOneScale_ne_zero hN hζ b aNeg
  rw [ht, hs]
  rw [hneg] at hz ⊢
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp only [inv_neg, neg_div, one_div]
  rw [hS, weightOneThetaValue_S _ _ _ τ.ne_zero (by simpa [sub_eq_add_neg] using hz)]
  field_simp

end VOA.Classification.COne.SSHecke
