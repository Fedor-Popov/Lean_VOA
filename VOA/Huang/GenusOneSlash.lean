import VOA.Huang.GenusOneODE
import VOA.Modularity.BlockSlash
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The analytic part of S-covariance, for complex square weights

The principal branch `z^(-α)` is holomorphic on the upper half-plane. The
Serre derivative has complex weight α, so no integral-weight representation is
silently imposed. Full block covariance additionally needs module square grading.
-/
namespace VOA.Huang.GenusOne
open VOA Complex
open scoped BigOperators MatrixGroups
universe u

/-- Weight-α S-slash, with the principal complex power on the upper half-plane. -/
noncomputable def sSlash (α : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ (-α) * f (mobiusC ModularGroup.S z)

theorem sSlash_apply (α : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    sSlash α f z = z ^ (-α) * f (-1 / z) := by
  simp [sSlash, mobiusC, denomC, ModularGroup.S]

/-- The Serre derivative at an arbitrary complex weight. -/
noncomputable def insertionSerre (α : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv f z +
    α * zhuGC 1 z * f z

/-- S-slashing preserves holomorphy for any complex weight. -/
theorem differentiableOn_sSlash (α : ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (imGT 0)) :
    DifferentiableOn ℂ (sSlash α f) (imGT 0) := by
  intro z hz
  have hp : z ∈ Complex.slitPlane := Or.inr (ne_of_gt hz)
  exact ((differentiableAt_id.cpow_const hp).mul
    (((hf _ (mobiusC_mem_imGT ModularGroup.S hz)).differentiableAt
      ((isOpen_imGT 0).mem_nhds (mobiusC_mem_imGT ModularGroup.S hz))).comp z
      (hasDerivAt_mobiusC ModularGroup.S hz).differentiableAt)).differentiableWithinAt

/-- Explicit derivative of the weight-α S-slash. -/
theorem deriv_sSlash (α : ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (imGT 0)) {z : ℂ} (hz : z ∈ imGT 0) :
    _root_.deriv (sSlash α f) z =
      -α * (z ^ (-α) / z) * f (mobiusC ModularGroup.S z) +
        z ^ (-α) * (_root_.deriv f (mobiusC ModularGroup.S z) / z ^ (2 : ℕ)) := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl (0 : ℝ)) hz
  have hp : z ∈ Complex.slitPlane := Or.inr (ne_of_gt hz)
  have hpow := (hasDerivAt_id z).cpow_const (c := -α) hp
  have hcomp := ((hf _ (mobiusC_mem_imGT ModularGroup.S hz)).differentiableAt
    ((isOpen_imGT 0).mem_nhds (mobiusC_mem_imGT ModularGroup.S hz))).hasDerivAt.comp z
      (hasDerivAt_mobiusC ModularGroup.S hz)
  have hd := (hpow.mul hcomp).deriv
  change _root_.deriv (sSlash α f) z = _ at hd
  rw [hd]
  simp only [id_eq, Function.comp_apply]
  rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  simp only [denomC, ModularGroup.S, Matrix.of_apply, Matrix.cons_val_one,
    Matrix.cons_val_zero, Int.cast_one, Int.cast_zero, one_mul, add_zero,
    mul_one, zpow_neg, zpow_ofNat]
  ring

/-- The quasimodular anomaly cancels for complex weights as well. -/
theorem insertionSerre_sSlash (α : ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (imGT 0)) {z : ℂ} (hz : z ∈ imGT 0) :
    insertionSerre α (sSlash α f) z = sSlash (α + 2) (insertionSerre α f) z := by
  have hz0 : z ≠ 0 := by rintro rfl; exact (lt_irrefl (0 : ℝ)) hz
  have hG := slashC_G2C ModularGroup.S hz
  have hden : denomC ModularGroup.S z = z := by simp [denomC, ModularGroup.S]
  have hc : (ModularGroup.S 1 0 : ℂ) = 1 := by norm_num [ModularGroup.S]
  rw [slashC, hden, hc, mul_one, zpow_neg, zpow_ofNat] at hG
  have hp : z ^ (-(α + 2)) = z ^ (-α) / z ^ (2 : ℕ) := by
    rw [show -(α + 2) = -α - (2 : ℂ) by ring, Complex.cpow_sub _ _ hz0]
    congr 1
    exact Complex.cpow_natCast z 2
  rw [insertionSerre, deriv_sSlash α hf hz]
  simp only [sSlash]
  rw [hp, insertionSerre, zhuGC_one hz, zhuGC_one (mobiusC_mem_imGT ModularGroup.S hz)]
  have hG' : G2C (mobiusC ModularGroup.S z) / z ^ (2 : ℕ) =
      G2C z - (2 * (Real.pi : ℂ) * Complex.I) / z := by
    simpa only [div_eq_mul_inv] using hG
  have hi := two_pi_I_ne_zero
  field_simp at hG' ⊢
  linear_combination -α * z ^ (-α) * f (mobiusC ModularGroup.S z) * hG'

variable {V M₁ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁]
  {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁} {F : M₁ → ℂ → ℂ}

theorem IsInsertionAnalyticBlock.zerov (hF : IsInsertionAnalyticBlock A F) (z : ℂ) :
    F 0 z = 0 := by
  have h := hF.smulv 0 0 z
  rwa [zero_smul, zero_mul] at h

/-- The `k = m+1` term of Zhu's condition (ii). -/
noncomputable def insertionNegTwoTerm (A : OrdVModule W M₁) (F : M₁ → ℂ → ℂ)
    (a : V) (ka : ℕ) (v : M₁) (z : ℂ) (m : ℕ) : ℂ :=
  ((2 * (m + 1) - 1 : ℕ) : ℂ)
    * (zhuGC (m + 1) z * F (sqAct A a ka (2 * (m + 1) - 2 : ℤ) v) z)

/-- The `k = m+1` term of Zhu's condition (iii). -/
noncomputable def insertionOmegaTerm (A : OrdVModule W M₁) (F : M₁ → ℂ → ℂ)
    (v : M₁) (z : ℂ) (m : ℕ) : ℂ :=
  zhuGC (m + 1) z * F (sqL A (2 * (m + 1) - 2 : ℤ) v) z


theorem insertionNegTwoTerm_zero (A : OrdVModule W M₁) (F : M₁ → ℂ → ℂ)
    (a : V) (ka : ℕ) (v : M₁) (z : ℂ) :
    insertionNegTwoTerm A F a ka v z 0 = zhuGC 1 z * F (sqAct A a ka 0 v) z := by
  rw [insertionNegTwoTerm, show (2 * ((0 : ℕ) + 1) - 2 : ℤ) = 0 from by norm_num]
  norm_num

theorem insertionNegTwoTerm_succ (A : OrdVModule W M₁) (F : M₁ → ℂ → ℂ)
    (a : V) (ka : ℕ) (v : M₁) (z : ℂ) (m : ℕ) :
    insertionNegTwoTerm A F a ka v z (m + 1) =
      ((2 * (m + 2) - 1 : ℕ) : ℂ)
      * (zhuGC (m + 2) z * F (sqAct A a ka (2 * (m + 2) - 2 : ℤ) v) z) := by
  rw [insertionNegTwoTerm,
    show (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2 : ℤ) = 2 * ((m : ℤ) + 2) - 2 from by
      push_cast; ring]

theorem insertionOmegaTerm_zero (A : OrdVModule W M₁) (F : M₁ → ℂ → ℂ)
    (v : M₁) (z : ℂ) :
    insertionOmegaTerm A F v z 0 = zhuGC 1 z * F (sqL A 0 v) z := by
  rw [insertionOmegaTerm, show (2 * ((0 : ℕ) + 1) - 2 : ℤ) = 0 from by norm_num]

theorem insertionOmegaTerm_succ (A : OrdVModule W M₁) (F : M₁ → ℂ → ℂ)
    (v : M₁) (z : ℂ) (m : ℕ) :
    insertionOmegaTerm A F v z (m + 1) = zhuGC (m + 2) z * F (sqL A (2 * (m + 2) - 2 : ℤ) v) z := by
  rw [insertionOmegaTerm, show (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2 : ℤ) = 2 * ((m : ℤ) + 2) - 2 from by
    push_cast; ring]

theorem IsInsertionAnalyticBlock.negTwo_tail (hF : IsInsertionAnalyticBlock A F)
    (ka : ℕ) (hka : 1 ≤ ka)
    {a : V} (ha : a ∈ W.grading (ka : ℤ)) (v : M₁) {z : ℂ} (hz : z ∈ imGT 0) :
    F (sqAct A a ka (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * F (sqAct A a ka (2 * (m + 2) - 2 : ℤ) v) z) = 0 := by
  obtain ⟨K, hK⟩ := sqAct_tail_eventually_zero A a ka v
  have hlaw := hF.negTwo ka hka a ha v z hz
  change _ + ∑ᶠ m : ℕ, insertionNegTwoTerm A F a ka v z m = 0 at hlaw
  have hpeel : (∑ᶠ m : ℕ, insertionNegTwoTerm A F a ka v z m)
      = insertionNegTwoTerm A F a ka v z 0 + ∑ᶠ m : ℕ, insertionNegTwoTerm A F a ka v z (m + 1) :=
    finsum_nat_peel (K := K) (fun m hm => by
      rw [insertionNegTwoTerm, hK m hm, hF.zerov z]; simp)
  have h0 : insertionNegTwoTerm A F a ka v z 0 = 0 := by
    rw [insertionNegTwoTerm_zero, hF.vanish ka hka a ha v]; simp
  have hshift : (∑ᶠ m : ℕ, insertionNegTwoTerm A F a ka v z (m + 1))
      = ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * F (sqAct A a ka (2 * (m + 2) - 2 : ℤ) v) z) :=
    finsum_congr (fun m => insertionNegTwoTerm_succ A F a ka v z m)
  rw [hpeel, h0, zero_add, hshift] at hlaw
  exact hlaw

/-- On a square-weight eigenvector the omega recursion is a complex-weight
Serre equation, with only modular Eisenstein series in the remaining tail. -/
theorem IsInsertionAnalyticBlock.omega_serre (hF : IsInsertionAnalyticBlock A F) {α : ℂ} {v : M₁}
    (hv : sqL A 0 v = α • v) {z : ℂ} (hz : z ∈ imGT 0) :
    F (sqL A (-2) v) z
      = insertionSerre α (F v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 2) z * F (sqL A (2 * (m + 2) - 2 : ℤ) v) z := by
  obtain ⟨K, hK⟩ := sqL_tail_eventually_zero A v
  have hlaw := hF.omega v z hz
  change _ = _ + ∑ᶠ m : ℕ, insertionOmegaTerm A F v z m at hlaw
  have hpeel : (∑ᶠ m : ℕ, insertionOmegaTerm A F v z m)
      = insertionOmegaTerm A F v z 0 + ∑ᶠ m : ℕ, insertionOmegaTerm A F v z (m + 1) :=
    finsum_nat_peel (K := K) (fun m hm => by
      rw [insertionOmegaTerm, hK m hm, hF.zerov z]; simp)
  have hL0 : sqL A 0 v = α • v := hv
  have h0 : insertionOmegaTerm A F v z 0
      = α * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * (G2C z * F v z) := by
    rw [insertionOmegaTerm_zero, hL0, hF.smulv, zhuGC_one hz]
    ring
  have hshift : (∑ᶠ m : ℕ, insertionOmegaTerm A F v z (m + 1))
      = ∑ᶠ m : ℕ, zhuGC (m + 2) z * F (sqL A (2 * (m + 2) - 2 : ℤ) v) z :=
    finsum_congr (fun m => insertionOmegaTerm_succ A F v z m)
  rw [hpeel, h0, hshift] at hlaw
  rw [hlaw, insertionSerre, zhuGC_one hz]
  ring

end VOA.Huang.GenusOne
