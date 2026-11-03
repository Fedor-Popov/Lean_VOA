import VOA.Classification.COne.QExpWeightTwoTheta
import VOA.Classification.COne.QExpWeightTwoRealization
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Generator laws including the boundary torsion indices

The only analytic hypothesis is `WeightOneThetaFourier N`, the shifted
odd-theta logarithmic derivative identity (DLMF 20.5.1 and 20.5.10,
https://dlmf.nist.gov/20.5). This file does not assert that input.
-/

open Complex UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- The representative of a residue in the existing finite index type. -/
def weightOneIndex {N : ℕ} [NeZero N] (a : ZMod N) : Fin N := ⟨a.val, a.val_lt⟩

/-- Remove the nonzero coefficient-clearing scalar from the standard-root series. -/
def weightOneNormalized {N : ℕ} [NeZero N] (a b : ZMod N) (τ : ℍ) : ℂ :=
  weightOneQSeries N (weightOneStandardRoot N) (weightOneIndex a) (weightOneIndex b) τ /
    weightOneScale N (weightOneStandardRoot N) (weightOneIndex a) (weightOneIndex b)

theorem weightOneQSeries_zero (N : ℕ) (ζ : ℂ) (a b : Fin N)
    (ha : a.val = 0) (hb : b.val = 0) : weightOneQSeries N ζ a b = 0 := by
  funext τ
  simp [weightOneQSeries, weightOneIntegralCoeff, ha, hb]

@[simp] theorem weightOneNormalized_zero {N : ℕ} [NeZero N] :
    weightOneNormalized (0 : ZMod N) 0 = 0 := by
  funext τ
  simp [weightOneNormalized, weightOneQSeries, weightOneIntegralCoeff, weightOneIndex]

theorem weightOneNormalized_eq_theta {N : ℕ} [NeZero N]
    (hf : WeightOneThetaFourier N) (a b : ZMod N) (hab : ¬(a = 0 ∧ b = 0)) (τ : ℍ) :
    weightOneNormalized a b τ =
      weightOneThetaValue ((a.val : ℂ) / N - 1 / 2) ((b.val : ℂ) / N - 1 / 2) τ := by
  have h := (hf (weightOneIndex a) (weightOneIndex b)
    (by simpa [weightOneIndex, ZMod.val_eq_zero] using hab) τ).2
  unfold weightOneNormalized
  rw [h, mul_div_cancel_left₀ _ (weightOneScale_ne_zero (NeZero.pos N)
    (show IsPrimitiveRoot (weightOneStandardRoot N) N from
      Complex.isPrimitiveRoot_exp N (NeZero.ne N)) (weightOneIndex a) (weightOneIndex b))]
  rfl

/-- S covariance at every residue, including `a = 0` and the zero series. -/
theorem weightOneNormalized_S {N : ℕ} [NeZero N] (hf : WeightOneThetaFourier N)
    (a b : ZMod N) (τ : ℍ) :
    weightOneNormalized a b (ModularGroup.S • τ) =
      (τ : ℂ) * weightOneNormalized b (-a) τ := by
  by_cases hab : a = 0 ∧ b = 0
  · rcases hab with ⟨rfl, rfl⟩
    simp
  have hba : ¬(b = 0 ∧ -a = 0) := by simpa [and_comm] using hab
  rw [weightOneNormalized_eq_theta hf a b hab,
    weightOneNormalized_eq_theta hf b (-a) hba]
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp only [inv_neg, neg_div, one_div]
  rw [hS]
  have hz := (hf (weightOneIndex b) (weightOneIndex (-a))
    (by simpa [weightOneIndex, ZMod.val_eq_zero] using hba) τ).1
  dsimp [weightOneIndex] at hz
  by_cases ha : a = 0
  · subst a
    simp only [neg_zero, ZMod.val_zero, Nat.cast_zero, zero_div, zero_sub] at hz ⊢
    have hz' : jacobiTheta₂ (((b.val : ℂ) / N - 1 / 2) * τ - -(1 / 2)) τ ≠ 0 := by
      convert hz using 1
      rw [show ((b.val : ℂ) / N - 1 / 2) * (τ : ℂ) - -(1 / 2) =
        (((b.val : ℂ) / N - 1 / 2) * τ + -(1 / 2)) + 1 by ring,
        jacobiTheta₂_add_left]
    rw [weightOneThetaValue_S _ _ _ τ.ne_zero hz']
    congr 1
    convert weightOneThetaValue_add_one_right
      ((b.val : ℂ) / N - 1 / 2) (-(1 / 2)) τ using 1
    norm_num
  · letI : NeZero a := ⟨ha⟩
    have hn : ((-a).val : ℂ) / N - 1 / 2 = -((a.val : ℂ) / N - 1 / 2) := by
      rw [ZMod.val_neg_of_ne_zero, Nat.cast_sub a.val_lt.le]
      have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      field_simp
      ring
    rw [hn] at hz ⊢
    exact weightOneThetaValue_S _ _ _ τ.ne_zero (by simpa [sub_eq_add_neg] using hz)

/-- T covariance, with reduction of the second residue modulo N. -/
theorem weightOneNormalized_T {N : ℕ} [NeZero N] (hf : WeightOneThetaFourier N)
    (a b : ZMod N) (τ : ℍ) :
    weightOneNormalized a b (ModularGroup.T • τ) = weightOneNormalized a (a + b) τ := by
  by_cases hab : a = 0 ∧ b = 0
  · rcases hab with ⟨rfl, rfl⟩
    simp
  have hab' : ¬(a = 0 ∧ a + b = 0) := by simpa +contextual using hab
  rw [weightOneNormalized_eq_theta hf a b hab,
    weightOneNormalized_eq_theta hf a (a + b) hab']
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul]
    simp [add_comm]
  rw [hT, weightOneThetaValue_T]
  by_cases hlt : a.val + b.val < N
  · rw [ZMod.val_add_of_lt hlt, Nat.cast_add]
    congr 1
    ring
  · rw [ZMod.val_add_of_le (by omega), Nat.cast_sub (by omega), Nat.cast_add]
    have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have he : (b.val : ℂ) / N - 1 / 2 + ((a.val : ℂ) / N - 1 / 2) + 1 / 2 =
        (((a.val : ℂ) + b.val - N) / N - 1 / 2) + 1 := by field_simp; ring
    rw [he, weightOneThetaValue_add_one_right]

theorem weightOneNormalized_slash_S {N : ℕ} [NeZero N] (hf : WeightOneThetaFourier N)
    (a b : ZMod N) :
    weightOneNormalized a b ∣[(1 : ℤ)] ModularGroup.S = weightOneNormalized b (-a) := by
  funext τ
  rw [SL_slash_apply, weightOneNormalized_S hf]
  simp [denom, ModularGroup.S, mul_comm, τ.ne_zero]

theorem weightOneNormalized_slash_T {N : ℕ} [NeZero N] (hf : WeightOneThetaFourier N)
    (a b : ZMod N) :
    weightOneNormalized a b ∣[(1 : ℤ)] ModularGroup.T = weightOneNormalized a (a + b) := by
  funext τ
  rw [SL_slash_apply, weightOneNormalized_T hf]
  simp [denom, ModularGroup.T]

end VOA.Classification.COne.SSHecke
