import VOA.DeligneAudit.DeligneFusionCVRectPolynomialCyclic
import VOA.DeligneAudit.DeligneFusionCVRectReflection
import VOA.DeligneAudit.DeligneFusionCVRectSplit
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Finite polynomial currents in the actual cyclic representation

The finite polynomial agrees with the full current series when its high modes
are zero as operators. Its fixed-degree reflection is the canonical reversed
series. The two finite coordinate conventions are identified explicitly.
-/

namespace VOA.DeligneAudit.A2.CVRectPolynomial

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily

noncomputable section

/-- The canonical two-color sum coordinates and the actual operator coordinates. -/
def colorIndex (N : ℕ) : Fin N ⊕ Fin N ≃ Variables N where
  toFun
    | Sum.inl i => (false, i)
    | Sum.inr i => (true, i)
  invFun x := if x.1 then Sum.inr x.2 else Sum.inl x.2
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨b, i⟩; cases b <;> rfl

/-- Renaming changes only the indexing convention of the same two colors. -/
def colorCoordinates (N : ℕ) :
    MvPolynomial (Fin N ⊕ Fin N) ℂ ≃ₐ[ℂ] MvPolynomial (Variables N) ℂ :=
  MvPolynomial.renameEquiv ℂ (colorIndex N)

@[simp] theorem colorCoordinates_X_left (N : ℕ) (i : Fin N) :
    colorCoordinates N (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (false, i) := by
  simp [colorCoordinates, MvPolynomial.renameEquiv_apply, colorIndex]

@[simp] theorem colorCoordinates_X_right (N : ℕ) (i : Fin N) :
    colorCoordinates N (MvPolynomial.X (Sum.inr i)) = MvPolynomial.X (true, i) := by
  simp [colorCoordinates, MvPolynomial.renameEquiv_apply, colorIndex]

section Finite

variable {A : Type*} [Semiring A]

/-- A finite current polynomial with exactly the first `N` mode coefficients. -/
def finiteCurrent (N : ℕ) (F : ℕ → A) : Polynomial A := by
  classical
  exact Polynomial.ofFn N (fun i => F i.val)

theorem finiteCurrent_coeff_lt (N : ℕ) (F : ℕ → A) (j : ℕ) (hj : j < N) :
    (finiteCurrent N F).coeff j = F j := by
  classical
  exact Polynomial.ofFn_coeff_eq_val_of_lt _ hj

theorem finiteCurrent_coeff_ge (N : ℕ) (F : ℕ → A) (j : ℕ) (hj : N ≤ j) :
    (finiteCurrent N F).coeff j = 0 := by
  classical
  exact Polynomial.ofFn_coeff_eq_zero_of_ge _ hj

theorem finiteCurrent_natDegree_le (N : ℕ) (F : ℕ → A) :
    (finiteCurrent N F).natDegree ≤ N - 1 := by
  classical
  cases N with
  | zero => simp [finiteCurrent]
  | succ N => exact Nat.le_pred_of_lt (Polynomial.ofFn_natDegree_lt (by omega) _)

/-- An exact operator cutoff identifies the finite polynomial and full series. -/
theorem finiteCurrent_series (N : ℕ) (F : ℕ → A) (hF : ∀ j, N ≤ j → F j = 0) :
    (finiteCurrent N F : PowerSeries A) = PowerSeries.mk F := by
  apply PowerSeries.ext
  intro j
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk]
  by_cases hj : j < N
  · exact finiteCurrent_coeff_lt N F j hj
  · rw [finiteCurrent_coeff_ge N F j (by omega), hF j (by omega)]

private theorem reflect_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial A) (d : ℕ) :
    Polynomial.reflect d (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, Polynomial.reflect_add, ih]

/-- Reflection keeps the common truncation bound, including leading zero modes. -/
theorem reflect_finiteCurrent (N : ℕ) (F : ℕ → A) :
    Polynomial.reflect (N - 1) (finiteCurrent N F) =
      ∑ i : Fin N, Polynomial.C (F i.val) * Polynomial.X ^ (N - 1 - i.val) := by
  classical
  unfold finiteCurrent
  rw [Polynomial.ofFn_eq_sum_monomial, reflect_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val ≤ N - 1 := by omega
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.reflect_C_mul_X_pow,
    Polynomial.revAt_le hi]

/-- The reversed finite series is literally the reflected finite polynomial. -/
theorem reflect_finiteCurrent_series (N : ℕ) (F : ℕ → A) :
    (Polynomial.reflect (N - 1) (finiteCurrent N F) : PowerSeries A) =
      ∑ i : Fin N, PowerSeries.C (F i.val) * PowerSeries.X ^ (N - 1 - i.val) := by
  rw [reflect_finiteCurrent]
  change Polynomial.coeToPowerSeries.ringHom (∑ i : Fin N,
    Polynomial.C (F i.val) * Polynomial.X ^ (N - 1 - i.val)) = _
  rw [map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]

/-- Evaluation of the canonical reversed left series agrees with operator reflection. -/
theorem map_reverseLeft (N : ℕ) (φ : MvPolynomial (Fin N ⊕ Fin N) ℂ →+* A)
    (F : ℕ → A) (hF : ∀ i : Fin N, φ (MvPolynomial.X (Sum.inl i)) = F i.val) :
    PowerSeries.map φ (CVRectSplit.reverseLeft N N) =
      (Polynomial.reflect (N - 1) (finiteCurrent N F) : PowerSeries A) := by
  rw [reflect_finiteCurrent_series]
  unfold CVRectSplit.reverseLeft
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hF]

/-- Evaluation of the canonical reversed right series agrees with operator reflection. -/
theorem map_reverseRight (N : ℕ) (φ : MvPolynomial (Fin N ⊕ Fin N) ℂ →+* A)
    (F : ℕ → A) (hF : ∀ i : Fin N, φ (MvPolynomial.X (Sum.inr i)) = F i.val) :
    PowerSeries.map φ (CVRectSplit.reverseRight N N) =
      (Polynomial.reflect (N - 1) (finiteCurrent N F) : PowerSeries A) := by
  rw [reflect_finiteCurrent_series]
  unfold CVRectSplit.reverseRight
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hF]

end Finite

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Restriction to the cyclic submodule preserves actual polynomial evaluation. -/
theorem vectorEval_cyclic_coe (R : CurrentModule bracketTable V) (w : V) (N : ℕ)
    (p : MvPolynomial (Variables N) ℂ) :
    (↑(vectorEval (cyclicRep R w) (cyclicVector R w) N p) : V) = vectorEval R w N p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [vectorEval]
  | add p q hp hq => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hp hq
  | mul_X p x hp =>
      rw [mul_comm p, vectorEval_X_mul, vectorEval_X_mul]
      have hh := congrArg (colorOp R x) hp
      rcases x with ⟨b, i⟩
      cases b <;> simpa only [colorOp, Bool.false_eq_true, ↓reduceIte,
        cyclicRep_op_coe] using hh

end
end VOA.DeligneAudit.A2.CVRectPolynomial

#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.finiteCurrent_series
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.reflect_finiteCurrent_series
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.map_reverseLeft
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.map_reverseRight
#print axioms VOA.DeligneAudit.A2.CVRectPolynomial.vectorEval_cyclic_coe
