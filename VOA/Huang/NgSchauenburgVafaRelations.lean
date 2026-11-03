import VOA.Huang.NgSchauenburgVafaAlgebra
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! # Dominant exponent relations in the Vafa argument

The arithmetic step here does not assume a nonzero determinant: a strict
row-sum bound proves it. The categorical extraction of the three-channel
Anderson–Moore–Vafa relations is a separate obligation, not a hypothesis
silently supplied by `Modular`.
-/
noncomputable section
namespace VOA.Huang.NgSchauenburg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integer exponent matrix for equations `tᵢ^mᵢ = ∏ⱼ tⱼ^Bᵢⱼ`. -/
def vafaExponentMatrix (m : ι → ℕ) (B : Matrix ι ι ℕ) : Matrix ι ι ℤ :=
  fun i j => (if i = j then (m i : ℤ) else 0) - B i j

/-- Strict row-sum dominance proves full rank over the integers. -/
theorem vafaExponentMatrix_det_ne_zero (m : ι → ℕ) (B : Matrix ι ι ℕ)
    (h : ∀ i, ∑ j, B i j < m i) : (vafaExponentMatrix m B).det ≠ 0 := by
  let A := vafaExponentMatrix m B
  have hn : (A.map (Int.castRingHom ℝ)).det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro i
    have hs : (∑ j, (B i j : ℝ)) < m i := by exact_mod_cast h i
    have hb : (B i i : ℝ) ≤ ∑ j, (B i j : ℝ) :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ i)
    have hd : 0 ≤ (m i : ℝ) - B i i := sub_nonneg.mpr (hb.trans hs.le)
    calc
      _ = ∑ j ∈ Finset.univ.erase i, (B i j : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
        simp [A, vafaExponentMatrix, hij, Matrix.map_apply]
      _ = (∑ j, (B i j : ℝ)) - B i i :=
        Finset.sum_erase_eq_sub (Finset.mem_univ i)
      _ < (m i : ℝ) - B i i := sub_lt_sub_right hs _
      _ = _ := by simp [A, vafaExponentMatrix, Matrix.map_apply, Real.norm_eq_abs,
        abs_of_nonneg hd]
  intro hz
  apply hn
  erw [← (Int.castRingHom ℝ).map_det, hz, map_zero]

omit [DecidableEq ι] in
/-- Dominant monomial relations force torsion; the determinant condition is proved. -/
theorem finite_order_of_dominant_relations {G : Type*} [CommGroup G]
    (t : ι → G) (m : ι → ℕ) (B : Matrix ι ι ℕ)
    (hrow : ∀ i, ∑ j, B i j < m i)
    (hrel : ∀ i, t i ^ m i = ∏ j, t j ^ B i j) :
    ∀ i, IsOfFinOrder (t i) := by
  classical
  apply finite_order_of_monomial_relations (vafaExponentMatrix m B) t
    (vafaExponentMatrix_det_ne_zero m B hrow)
  funext i
  simp only [monomialAction, vafaExponentMatrix, zpow_sub, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  have hd : (∏ j, t j ^ (if i = j then (m i : ℤ) else 0)) = t i ^ m i := by
    simp
  rw [hd]
  simp only [zpow_natCast, hrel, mul_inv_cancel, Pi.one_apply]

omit [DecidableEq ι] in
/-- The `4d` versus `3d` specialization used after dual-compatible Vafa relations. -/
theorem finite_order_of_vafa_rows {G : Type*} [CommGroup G]
    (t : ι → G) (d : ι → ℕ) (B : Matrix ι ι ℕ)
    (hd : ∀ i, 0 < d i) (hrow : ∀ i, ∑ j, B i j = 3 * d i)
    (hrel : ∀ i, t i ^ (4 * d i) = ∏ j, t j ^ B i j) :
    ∀ i, IsOfFinOrder (t i) := by
  apply finite_order_of_dominant_relations t (fun i => 4 * d i) B
  · intro i
    rw [hrow]
    exact Nat.mul_lt_mul_of_pos_right (by norm_num : 3 < 4) (hd i)
  · exact hrel

end VOA.Huang.NgSchauenburg
